# ------------------------------------------------------------
# JAGS/BUGS parser with plates (static) + interactive visNetwork
# ------------------------------------------------------------
suppressWarnings(suppressMessages({
  library(igraph)
  library(visNetwork)
  library(htmlwidgets)
  library(htmltools)
  library(jsonlite)
}))

# ---------- Helpers ----------
.strip_comments <- function(model_lines) {
  model_lines <- gsub("#.*$", "", model_lines)
  trimws(model_lines)
}

.extract_model_block <- function(model_lines) {
  txt <- paste(model_lines, collapse = "\n")
  mstart <- regexpr("\\bmodel\\s*\\{", txt, perl = TRUE)
  if (mstart[1] == -1) stop("No 'model { ... }' block found.")
  start <- as.integer(mstart) + attr(mstart, "match.length")
  depth <- 1L; i <- start; end_pos <- NA_integer_
  while (i <= nchar(txt)) {
    ch <- substr(txt, i, i)
    if (ch == "{") depth <- depth + 1L
    if (ch == "}") { depth <- depth - 1L; if (depth == 0L) { end_pos <- i; break } }
    i <- i + 1L
  }
  if (is.na(end_pos)) stop("Could not find closing '}' for model block.")
  block <- substr(txt, start, end_pos - 1L)
  blines <- unlist(strsplit(block, "\n", fixed = TRUE))
  blines <- blines[nzchar(trimws(blines))]
  blines
}

.normalize_index <- function(name) gsub("\\[[^\\]]*\\]", "[]", name, perl = TRUE)

.tokenize_symbols <- function(expr) {
  m <- gregexpr("\\b[A-Za-z_][A-Za-z0-9_.]*\\b(?:\\[[^\\]]+\\])?", expr, perl = TRUE)
  if (length(m) == 0L || m[[1]][1] == -1) return(character(0))
  unique(regmatches(expr, m)[[1]])
}

.is_numeric_like <- function(tok) {
  grepl("^([0-9]+(\\.[0-9]*)?|\\.[0-9]+)([eE][+-]?[0-9]+)?$", tok)
}

.ignore_set <- c(
  "model","for","in","if","else","T","F","NA","TRUE","FALSE",
  "I","log","log10","exp","sqrt","pow","abs","step","ceil","floor","round","phi",
  "cos","sin","tan","acos","asin","atan","max","min","mean","sd","sum","prod","length",
  # distributions
  "dbern","dbin","dcat","ddirch","ddexp","dgamma","dlnorm","dlogis","dnorm",
  "dpar","dpois","dunif","dweib","dmulti","dmnorm","dmvnorm","dwish","dinvgamma",
  "dhyper","dnbinom","dt","dchisqr","dexp","dbeta",
  # link helpers
  "cloglog","logit","probit","ilogit","equals","inprod"
)

# Combine soft-wrapped lines using a last-character heuristic
.coalesce_lines <- function(model_lines) {
  out <- character(0); buf <- ""
  for (ln in model_lines) {
    s <- trimws(ln); if (!nzchar(s)) next
    buf <- paste0(buf, " ", s)
    last_char <- if (nzchar(s)) substr(s, nchar(s), nchar(s)) else ""
    if (last_char %in% c(",", "+", "-", "*", "/", "^", "=")) next
    out <- c(out, trimws(buf)); buf <- ""
  }
  if (nzchar(trimws(buf))) out <- c(out, trimws(buf))
  out
}

.extract_loops <- function(model_lines) {
  if (is.null(model_lines) || length(model_lines) == 0) {
    return(data.frame(var=character(), range=character(), label=character(), stringsAsFactors=FALSE))
  }
  if (!is.character(model_lines)) model_lines <- as.character(model_lines)
  
  vars <- c(); ranges <- c(); labels <- c()
  for (ln in model_lines) {
    if (!nzchar(trimws(ln))) next
    m <- regexec("for\\s*\\(\\s*([A-Za-z_][A-Za-z0-9_]*)\\s+in\\s+([^\\)]*)\\)", ln, perl = TRUE)
    hit <- regmatches(ln, m)[[1]]
    if (length(hit) >= 3) {
      v <- trimws(hit[2])
      r <- trimws(hit[3])
      vars   <- c(vars, v)
      ranges <- c(ranges, r)
      labels <- c(labels, paste0(v, " in ", r))
    }
  }
  if (!length(vars))
    return(data.frame(var=character(), range=character(), label=character(), stringsAsFactors=FALSE))
  
  data.frame(var=vars, range=ranges, label=labels, stringsAsFactors=FALSE)
}

.index_vars_in_token <- function(tok) {
  m <- regexpr("\\[([^\\]]+)\\]", tok, perl = TRUE)
  if (m[1] == -1) return(character(0))
  inner <- regmatches(tok, m)
  inner <- sub("^\\[", "", sub("\\]$", "", inner))
  syms <- gregexpr("\\b[A-Za-z_][A-Za-z0-9_]*\\b", inner, perl = TRUE)
  if (length(syms) == 0L || syms[[1]][1] == -1) return(character(0))
  unique(regmatches(inner, syms)[[1]])
}

.extract_edges_from_lines <- function(model_lines) {
  model_lines <- .coalesce_lines(model_lines)
  from_vec <- character(); to_vec <- character()
  
  for (line in model_lines) {
    LHS <- RHS <- NULL
    if (grepl("~", line, fixed = TRUE)) {
      parts <- strsplit(line, "~", fixed = TRUE)[[1]]
      if (length(parts) >= 2) { LHS <- trimws(parts[1]); RHS <- paste(parts[-1], collapse = "~") }
    }
    if (is.null(LHS) && grepl("<-", line, fixed = TRUE)) {
      parts <- strsplit(line, "<-", fixed = TRUE)[[1]]
      if (length(parts) >= 2) { LHS <- trimws(parts[1]); RHS <- paste(parts[-1], collapse = "<-") }
    }
    if (is.null(LHS) || is.null(RHS)) next
    
    LHS <- sub("\\s+.*$", "", LHS)
    LHSn <- .normalize_index(LHS)
    
    toks <- .tokenize_symbols(RHS)
    parents <- toks[!toks %in% .ignore_set & !.is_numeric_like(toks)]
    parents <- parents[parents != LHS]
    parents <- unique(.normalize_index(parents))
    
    if (length(parents)) {
      from_vec <- c(from_vec, parents)
      to_vec   <- c(to_vec, rep(LHSn, length(parents)))
    }
  }
  
  if (!length(from_vec)) {
    return(data.frame(from=character(0), to=character(0), stringsAsFactors=FALSE))
  }
  unique(data.frame(from = from_vec, to = to_vec, stringsAsFactors = FALSE))
}

.classify_nodes <- function(model_lines, node_names) {
  stoch_lhs <- unique(sub("\\s+.*$","", trimws(gsub("^\\s*([^~]+)~.*$","\\1",
                                                    grep("~", model_lines, value=TRUE, perl=TRUE)))))
  det_lhs   <- unique(sub("\\s+.*$","", trimws(gsub("^\\s*([^<]+)<-.*$","\\1",
                                                    grep("<-", model_lines, value=TRUE, fixed=TRUE)))))
  
  norm <- function(v) unique(gsub("\\[[^\\]]*\\]", "[]", v, perl=TRUE))
  stoch_set <- norm(stoch_lhs)
  det_set   <- norm(det_lhs)
  ifelse(node_names %in% stoch_set, "stochastic",
         ifelse(node_names %in% det_set, "deterministic", "data/derived"))
}

# ---------- Builder ----------
build_bugs_dependency_graph <- function(model_text,
                                        plot_static = FALSE,
                                        show_plates = TRUE,
                                        vertex_size = 26,
                                        edge_arrow_size = 0.4,
                                        plate_padding = 0.35) {
  # prepare lines safely (avoid 'lines' name!)
  raw <- unlist(strsplit(model_text, "\n", fixed=TRUE))
  raw <- .strip_comments(raw)
  model_lines <- .extract_model_block(raw)
  
  loop_df <- .extract_loops(model_lines)                 # var, range, label
  edges   <- .extract_edges_from_lines(model_lines)
  
  # Drop edges from loop index vars (e.g., i, t, tmt)
  if (nrow(edges) && nrow(loop_df)) {
    loop_vars <- unique(loop_df$var)
    edges <- edges[!(edges$from %in% loop_vars), , drop = FALSE]
  }
  
  if (!nrow(edges)) {
    warning("No dependencies found. Check '~' and '<-'.")
    g <- make_empty_graph()
    return(list(nodes = data.frame(name=character()),
                edges=edges, graph=g, plates=loop_df))
  }
  
  nodes <- sort(unique(c(edges$from, edges$to)))
  
  # Build index membership map
  tokens <- .tokenize_symbols(paste(model_lines, collapse=" "))
  tokens <- unique(tokens[!tokens %in% .ignore_set])
  
  index_map <- setNames(replicate(length(nodes), character(0), simplify = FALSE), nodes)
  for (t in tokens) {
    base <- .normalize_index(t)
    iv   <- .index_vars_in_token(t)
    if (base %in% names(index_map) && length(iv)) {
      index_map[[base]] <- unique(c(index_map[[base]], iv))
    }
  }
  
  vertices <- data.frame(name = nodes, stringsAsFactors = FALSE)
  vertices$index_vars <- I(index_map[vertices$name])
  vertices$type <- .classify_nodes(model_lines, vertices$name)
  
  g <- graph_from_data_frame(edges, directed = TRUE, vertices = vertices)
  
  if (plot_static) {
    set.seed(42)
    lay <- layout_with_sugiyama(g)$layout
    plot(g,
         layout = lay,
         vertex.label = V(g)$name,
         vertex.size = vertex_size,
         vertex.label.cex = 0.8,
         vertex.label.family = "sans",
         vertex.color = "lightgray",
         edge.arrow.size = edge_arrow_size,
         edge.curved = 0.05)
    title("BUGS/JAGS Dependency Graph (static with plate rectangles)")
    
    if (show_plates && nrow(loop_df)) {
      xy <- lay; rownames(xy) <- V(g)$name
      cols <- c("#8ecae6","#90be6d","#f4a261","#e9c46a","#bdb2ff")
      for (k in seq_len(nrow(loop_df))) {
        loop_var <- loop_df$var[k]
        members <- V(g)$name[vapply(V(g)$name, function(vn){
          iv <- index_map[[vn]]; length(iv) && loop_var %in% iv
        }, logical(1))]
        if (length(members)) {
          x <- xy[members,1]; y <- xy[members,2]
          rect(min(x)-plate_padding, min(y)-plate_padding,
               max(x)+plate_padding, max(y)+plate_padding,
               border = cols[(k-1) %% length(cols) + 1], lwd = 2)
          text(min(x)-plate_padding, max(y)+plate_padding,
               labels = loop_df$label[k], adj = c(0,0), cex = 0.9)
        }
      }
    }
  }
  
  list(nodes = vertices, edges = edges, graph = g, plates = loop_df)
}

# ---------- Interactive (visNetwork) ----------
to_vis <- function(res, raw_model_lines) {
  nodes <- res$nodes; edges <- res$edges
  
  plate_tip <- vapply(nodes$index_vars, function(iv){
    if (!length(iv)) "" else paste0("indexed by: ", paste(iv, collapse=", "))
  }, character(1))
  
  nodes$id <- seq_len(nrow(nodes))
  name_to_id <- setNames(nodes$id, nodes$name)
  
  type_cols <- c(stochastic="#FFD063", deterministic="#A6D6FF", `data/derived`="#DADADA")
  nodes$color.background <- unname(type_cols[nodes$type])
  nodes$color.border <- "#555555"
  nodes$color.highlight.background <- "#FFEEA6"
  nodes$color.highlight.border <- "#333333"
  nodes$label <- nodes$name
  nodes$title <- paste0(
    "<b>", nodes$name, "</b><br/>",
    "type: ", nodes$type,
    ifelse(nchar(plate_tip)>0, paste0("<br/>", plate_tip), "")
  )
  
  edf <- data.frame(
    from = name_to_id[edges$from],
    to   = name_to_id[edges$to],
    arrows = "to",
    smooth = TRUE,
    stringsAsFactors = FALSE
  )
  
  list(nodes = nodes, edges = edf)
}

plot_interactive <- function(res, model_text, title = "JAGS Dependency Graph (interactive)") {
  raw_lines <- {
    x <- unlist(strsplit(model_text, "\n", fixed=TRUE))
    x <- gsub("#.*$","", x)
    x[nzchar(trimws(x))]
  }
  ve <- to_vis(res, raw_lines)
  
  nodes_df <- ve$nodes[, c("id","label","title","color.background","color.border",
                           "color.highlight.background","color.highlight.border")]
  edges_df <- ve$edges
  
  g <- visNetwork::visNetwork(nodes_df, edges_df, width="100%", height="650px")
  g <- visNetwork::visOptions(g, highlightNearest=TRUE, nodesIdSelection=TRUE)
  g <- visNetwork::visPhysics(g, stabilization=TRUE, solver="forceAtlas2Based")
  g <- visNetwork::visEdges(g, arrows="to")
  g <- visNetwork::visNodes(g, shape="box", borderWidth=1)
  g <- visNetwork::visLegend(
    g,
    addNodes = data.frame(
      label=c("stochastic","deterministic","data/derived"),
      shape="box",
      color=c("#FFD063","#A6D6FF","#DADADA")
    ),
    useGroups = FALSE, width=0.25
  )
  g <- visNetwork::visInteraction(g, navigationButtons=TRUE, dragNodes=TRUE, zoomView=TRUE)
  g <- visNetwork::visLayout(g, randomSeed=42)
  g <- visNetwork::visExport(g, type="png")
  
  # Title added once, no duplication
  g <- htmlwidgets::prependContent(
    g,
    htmltools::tags$h3(style="margin:6px 0 10px; font-family:sans-serif;", title)
  )
  g
}

# Literal rectangle plates on the canvas
plot_interactive_with_plates <- function(res, model_text,
                                         title = "JAGS Dependency Graph (interactive plates)",
                                         plate_colors = c("#8ecae6","#90be6d","#f4a261","#e9c46a","#bdb2ff"),
                                         plate_padding_px = 24) {
  
  raw_lines <- {
    x <- unlist(strsplit(model_text, "\n", fixed=TRUE))
    x <- gsub("#.*$","", x)
    x[nzchar(trimws(x))]
  }
  ve <- to_vis(res, raw_lines)
  
  nodes_df <- ve$nodes[, c("id","label","title","color.background","color.border",
                           "color.highlight.background","color.highlight.border")]
  edges_df <- ve$edges
  
  # group nodes by loop var membership
  plate_groups <- list()
  if (nrow(res$plates)) {
    for (k in seq_len(nrow(res$plates))) {
      loop_var <- res$plates$var[k]
      label    <- res$plates$label[k]
      member_ids <- ve$nodes$id[
        vapply(res$nodes$index_vars, function(iv) loop_var %in% iv, logical(1))
      ]
      plate_groups[[label]] <- unname(member_ids)
    }
  }
  
  g <- visNetwork(nodes_df, edges_df, width="100%", height="650px")
  g <- visOptions(g, highlightNearest=TRUE, nodesIdSelection=TRUE)
  g <- visPhysics(g, stabilization=TRUE, solver="forceAtlas2Based")
  g <- visEdges(g, arrows="to")
  g <- visNodes(g, shape="box", borderWidth=1)
  g <- visLegend(
    g,
    addNodes = data.frame(
      label=c("stochastic","deterministic","data/derived"),
      shape="box",
      color=c("#FFD063","#A6D6FF","#DADADA")
    ),
    useGroups = FALSE, width=0.25
  )
  g <- visInteraction(g, navigationButtons=TRUE, dragNodes=TRUE, zoomView=TRUE)
  g <- visLayout(g, randomSeed=42)
  g <- visExport(g, type="png")
  
  # Title once
  g <- htmlwidgets::prependContent(
    g,
    htmltools::tags$h3(style="margin:6px 0 10px; font-family:sans-serif;", title)
  )
  
  # draw plate rectangles post-render
  plate_groups_json <- jsonlite::toJSON(plate_groups, auto_unbox = TRUE)
  plate_colors_json <- jsonlite::toJSON(plate_colors, auto_unbox = TRUE)
  js_code <- sprintf("
    function(ctx) {
      var groups = %s;
      var colors = %s;
      var pad = %d;
      var net = this;

      function bboxForIds(ids) {
        if (!ids || !ids.length) return null;
        var pos = net.getPositions(ids);
        var xs = [], ys = [];
        ids.forEach(function(id){
          var p = pos[id]; if (!p) return;
          xs.push(p.x); ys.push(p.y);
        });
        if (!xs.length) return null;
        var xmin = Math.min.apply(null, xs) - pad,
            xmax = Math.max.apply(null, xs) + pad,
            ymin = Math.min.apply(null, ys) - pad,
            ymax = Math.max.apply(null, ys) + pad;
        return {xmin:xmin, xmax:xmax, ymin:ymin, ymax:ymax};
      }

      var labels = Object.keys(groups);
      for (var gi = 0; gi < labels.length; gi++) {
        var label = labels[gi];
        var ids   = groups[label];
        if (!ids || !ids.length) continue;
        var bb = bboxForIds(ids);
        if (!bb) continue;

        var tl = net.canvasToDOM({x: bb.xmin, y: bb.ymin});
        var br = net.canvasToDOM({x: bb.xmax, y: bb.ymax});
        var x = tl.x, y = tl.y, w = br.x - tl.x, h = br.y - tl.y;

        ctx.save();
        ctx.setTransform(1,0,0,1,0,0);

        var col = colors[gi %% colors.length];
        ctx.globalAlpha = 0.08;
        ctx.fillStyle = col;
        ctx.fillRect(x, y, w, h);

        ctx.globalAlpha = 1.0;
        ctx.strokeStyle = col;
        ctx.lineWidth = 2;
        ctx.strokeRect(x, y, w, h);

        ctx.font = '12px sans-serif';
        ctx.fillStyle = '#333';
        ctx.fillText(label, x + 6, y + 14);

        ctx.restore();
      }
    }", plate_groups_json, plate_colors_json, as.integer(plate_padding_px))
  
  g <- visEvents(g, afterDrawing = htmlwidgets::JS(js_code))
  g
}

# ---------- Example JAGS model ----------
model_txt <- "
# Model
model{
  # Data analysis
  for (tmt in 1:2){                                      # Treatments tmt=1 (Seretide), tmt=2 (Fluticasone)
    for (i in 1:4){                                      # There are 4 non-absorbing health states
      r[tmt,i,1:5] ~ dmulti(pi[tmt,i,1:5], n[tmt,i])    # Multinomial DATA
      pi[tmt,i,1:5] ~ ddirch(prior[tmt,i,1:5])          # Dirichlet prior for probs.
    }
  }
  # Calculating summaries from a decision model
  for (tmt in 1:2){ 
    for (i in 1:5){ s[tmt,i,1] <- equals(i,1) }         # Initialise starting state
    for (i in 1:4){  
      for (t in 2:13){
        s[tmt,i,t] <- inprod(s[tmt,1:4,t-1], pi[tmt,1:4,i])  # 12 cycles
      }
      E[tmt,i] <- sum(s[tmt,i,2:13])
    }
    E[tmt,5] <- 12 - sum(E[tmt,1:4])
  }
  for (i in 1:5){
    D[i] <- E[1,i] - E[2,i]
    prob[i] <- step(D[i])
  }
}
"

# ---------- Run ----------
res <- build_bugs_dependency_graph(model_txt, plot_static = TRUE, show_plates = TRUE)

# Interactive
plot_interactive(res, model_text = model_txt, title = "Markov Decision Model (Dirichlet–Multinomial)")

# Interactive with plate rectangles
plot_interactive_with_plates(
  res,
  model_text = model_txt,
  title = "Markov Decision Model (Dirichlet–Multinomial)",
  plate_colors = c("#8ecae6","#90be6d","#f4a261"),
  plate_padding_px = 28
)
