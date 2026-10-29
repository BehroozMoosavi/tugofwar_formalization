// The 3D dependency map of the blueprint.
//
// Nodes are the definitions and theorems, coloured by chapter; an arrow runs
// from a result to each result that uses it. Selecting a node, by clicking or
// by searching, highlights its neighbourhood, flies the camera to it and shows
// its details in the side panel.
(function () {
  "use strict";

  var data = JSON.parse(document.getElementById("g3-data").textContent);
  var canvas = document.getElementById("g3-canvas");
  var info = document.getElementById("g3-info");
  var input = document.getElementById("g3-q");
  var results = document.getElementById("g3-results");
  var modeSel = document.getElementById("g3-mode");
  var layoutSel = document.getElementById("g3-layout");
  var legend = document.getElementById("g3-legend");

  function esc(s) {
    return String(s).replace(/[&<>"]/g, function (c) {
      return { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c];
    });
  }

  // ---- the graph structure, from the raw data (before the library mutates it)
  var byId = new Map();
  var deps = new Map();   // id -> ids it uses
  var users = new Map();  // id -> ids that use it
  data.nodes.forEach(function (n) {
    byId.set(n.id, n);
    deps.set(n.id, []);
    users.set(n.id, []);
    n.search = (n.number + " " + n.title + " " + n.id + " " + n.lean.join(" ")
                + " " + n.kindName).toLowerCase();
  });
  data.links.forEach(function (l) {
    deps.get(l.target).push(l.source);
    users.get(l.source).push(l.target);
  });

  function closure(start, next) {
    var seen = new Set([start]);
    var stack = [start];
    while (stack.length) {
      next.get(stack.pop()).forEach(function (m) {
        if (!seen.has(m)) { seen.add(m); stack.push(m); }
      });
    }
    return seen;
  }

  // ---- the library
  if (typeof ForceGraph3D === "undefined") {
    canvas.innerHTML = '<p class="g3-error">The 3D library could not be loaded. ' +
      "Please check your internet connection and reload the page.</p>";
    return;
  }

  var dark = window.matchMedia &&
             window.matchMedia("(prefers-color-scheme: dark)").matches;
  var BG = dark ? "#0f1218" : "#ffffff";
  var DIM = dark ? "rgba(110,120,140,0.22)" : "rgba(160,165,175,0.30)";
  var LINK = dark ? "rgba(170,180,200,0.35)" : "rgba(70,80,100,0.30)";
  var LINK_HL = dark ? "#ffffff" : "#1d2330";
  var SELECTED = "#ff3d00";

  var selected = null;
  var hlNodes = new Set();
  var visibleChapters = new Set(data.chapters.map(function (c) { return c.number; }));

  function idOf(x) { return typeof x === "object" ? x.id : x; }
  function isHL(l) {
    return selected !== null && hlNodes.has(idOf(l.source)) && hlNodes.has(idOf(l.target));
  }
  function nodeColor(n) {
    if (selected === null) return n.color;
    if (n.id === selected) return SELECTED;
    return hlNodes.has(n.id) ? n.color : DIM;
  }

  var Graph;
  try { Graph = new ForceGraph3D(canvas); } catch (e) { Graph = null; }
  if (!Graph || typeof Graph.graphData !== "function") Graph = ForceGraph3D()(canvas);

  Graph
    .backgroundColor(BG)
    .width(canvas.clientWidth)
    .height(canvas.clientHeight)
    .nodeId("id")
    .nodeVal(function (n) { return n.main ? 9 : (n.kind === "definition" ? 2.5 : 3); })
    .nodeResolution(16)
    .nodeOpacity(0.95)
    .nodeColor(nodeColor)
    .nodeLabel(function (n) {
      return '<div class="g3-tip"><b>' + esc(n.kindName + " " + n.number) + "</b><br>" +
        esc(n.title) + '<br><span>Chapter ' + n.chapter + ": " +
        esc(n.chapterTitle) + "</span></div>";
    })
    .nodeVisibility(function (n) { return visibleChapters.has(n.chapter); })
    .linkVisibility(function (l) {
      return visibleChapters.has(byId.get(idOf(l.source)).chapter) &&
             visibleChapters.has(byId.get(idOf(l.target)).chapter);
    })
    .linkColor(function (l) { return isHL(l) ? LINK_HL : LINK; })
    .linkWidth(function (l) { return isHL(l) ? 1.2 : 0.3; })
    .linkOpacity(0.7)
    .linkDirectionalArrowLength(3.5)
    .linkDirectionalArrowRelPos(1)
    .linkDirectionalParticles(function (l) { return isHL(l) ? 3 : 0; })
    .linkDirectionalParticleWidth(1.5)
    .linkDirectionalParticleSpeed(0.006)
    .onNodeClick(function (n) { select(n.id, true); })
    .onBackgroundClick(function () { clearSelection(); })
    .graphData({
      nodes: data.nodes.map(function (n) { return Object.assign({}, n); }),
      links: data.links.map(function (l) { return Object.assign({}, l); })
    });

  function refresh() {
    Graph.nodeColor(Graph.nodeColor())
         .linkColor(Graph.linkColor())
         .linkWidth(Graph.linkWidth())
         .linkDirectionalParticles(Graph.linkDirectionalParticles());
  }
  function refreshVisibility() {
    Graph.nodeVisibility(Graph.nodeVisibility())
         .linkVisibility(Graph.linkVisibility());
  }

  window.addEventListener("resize", function () {
    Graph.width(canvas.clientWidth).height(canvas.clientHeight);
  });

  // ---- selection
  function highlightSet(id) {
    var mode = modeSel.value;
    if (mode === "up") return closure(id, deps);
    if (mode === "down") return closure(id, users);
    var s = new Set([id]);
    deps.get(id).forEach(function (m) { s.add(m); });
    users.get(id).forEach(function (m) { s.add(m); });
    return s;
  }

  function chip(id) {
    var n = byId.get(id);
    return '<button type="button" class="g3-chip" data-id="' + esc(id) + '" title="' +
      esc(n.title) + '" style="border-color:' + n.color + '">' +
      esc(n.number) + " " + esc(n.title) + "</button>";
  }

  function renderInfo(id) {
    var n = byId.get(id);
    var d = deps.get(id), u = users.get(id);
    var modeText = { direct: "direct neighbours",
                     up: "results it depends on, directly or indirectly",
                     down: "results that use it, directly or indirectly" }[modeSel.value];
    info.innerHTML =
      '<div class="g3-kind" style="color:' + n.color + '">' + esc(n.kindName + " " + n.number) +
        (n.ok ? ' <span class="g3-ok">&#10003; formalized</span>' : "") + "</div>" +
      '<div class="g3-title">' + esc(n.title) + "</div>" +
      '<div class="g3-chap">Chapter ' + n.chapter + ": " + esc(n.chapterTitle) + "</div>" +
      (n.lean.length ? '<div class="g3-lean">' + n.lean.map(function (x) {
          return "<code>" + esc(x.replace(/^PLaplacian\./, "")) + "</code>";
        }).join(" ") + "</div>" : "") +
      '<div class="g3-count">' + (hlNodes.size - 1) + " " + modeText + "</div>" +
      '<div class="g3-sec">Depends on (' + d.length + ")</div>" +
      (d.length ? d.map(chip).join("") : '<p class="g3-none">nothing: a starting point</p>') +
      '<div class="g3-sec">Used by (' + u.length + ")</div>" +
      (u.length ? u.map(chip).join("") : '<p class="g3-none">nothing: an end result</p>') +
      '<a class="g3-open" href="index.html#' + encodeURIComponent(id) +
        '">Open the statement and its Lean code &rarr;</a>';
    info.querySelectorAll(".g3-chip").forEach(function (b) {
      b.addEventListener("click", function () { select(b.dataset.id, true); });
    });
  }

  function flyTo(id) {
    var node = Graph.graphData().nodes.find(function (m) { return m.id === id; });
    if (!node || node.x === undefined) return;
    var distance = 110;
    var r = Math.hypot(node.x, node.y, node.z) || 1;
    var k = 1 + distance / r;
    Graph.cameraPosition({ x: node.x * k, y: node.y * k, z: node.z * k }, node, 1200);
  }

  function select(id, fly) {
    if (!byId.has(id)) return;
    var ch = byId.get(id).chapter;
    if (!visibleChapters.has(ch)) { visibleChapters.add(ch); refreshVisibility(); renderLegend(); }
    selected = id;
    hlNodes = highlightSet(id);
    refresh();
    renderInfo(id);
    if (fly) flyTo(id);
    if (history.replaceState) history.replaceState(null, "", "#" + id);
  }

  function clearSelection() {
    selected = null;
    hlNodes = new Set();
    refresh();
    info.innerHTML = '<p class="g3-empty">Select a result, by searching or by clicking ' +
      "a node, to see what it depends on and what uses it.</p>";
    if (history.replaceState) history.replaceState(null, "", location.pathname);
  }

  modeSel.addEventListener("change", function () { if (selected) select(selected, false); });

  // ---- search
  var current = [];
  var active = -1;
  function search(q) {
    q = q.trim().toLowerCase();
    if (!q) { results.innerHTML = ""; current = []; return; }
    var words = q.split(/\s+/);
    current = data.nodes.filter(function (n) {
      return words.every(function (w) { return n.search.indexOf(w) >= 0; });
    }).slice(0, 12);
    active = current.length ? 0 : -1;
    renderResults();
  }
  function renderResults() {
    if (!current.length) {
      results.innerHTML = '<li class="g3-noresult">No matching result</li>';
      return;
    }
    results.innerHTML = current.map(function (n, i) {
      return '<li role="option" data-id="' + esc(n.id) + '" class="' +
        (i === active ? "active" : "") + '"><span class="g3-rnum" style="color:' +
        n.color + '">' + esc(n.number) + "</span> " + esc(n.title) + "</li>";
    }).join("");
    results.querySelectorAll("li[data-id]").forEach(function (li) {
      li.addEventListener("mousedown", function (e) {
        e.preventDefault();
        choose(li.dataset.id);
      });
    });
  }
  function choose(id) {
    var n = byId.get(id);
    input.value = n.number + " " + n.title;
    results.innerHTML = "";
    current = [];
    select(id, true);
  }
  input.addEventListener("input", function () { search(input.value); });
  input.addEventListener("keydown", function (e) {
    if (!current.length) return;
    if (e.key === "ArrowDown") { active = (active + 1) % current.length; renderResults(); e.preventDefault(); }
    else if (e.key === "ArrowUp") { active = (active - 1 + current.length) % current.length; renderResults(); e.preventDefault(); }
    else if (e.key === "Enter") { choose(current[Math.max(active, 0)].id); e.preventDefault(); }
    else if (e.key === "Escape") { results.innerHTML = ""; current = []; }
  });
  input.addEventListener("blur", function () {
    setTimeout(function () { results.innerHTML = ""; }, 150);
  });

  // ---- chapters
  function renderLegend() {
    legend.innerHTML = data.chapters.map(function (c) {
      var on = visibleChapters.has(c.number);
      return '<button type="button" class="g3-leg' + (on ? "" : " off") + '" data-ch="' +
        c.number + '"><span class="g3-sw" style="background:' + c.color + '"></span>' +
        c.number + ". " + esc(c.title) + "</button>";
    }).join("") +
    '<button type="button" class="g3-leg g3-all" data-ch="all">Show all chapters</button>';
    legend.querySelectorAll(".g3-leg").forEach(function (b) {
      b.addEventListener("click", function () {
        if (b.dataset.ch === "all") {
          data.chapters.forEach(function (c) { visibleChapters.add(c.number); });
        } else {
          var ch = Number(b.dataset.ch);
          if (visibleChapters.has(ch)) visibleChapters.delete(ch); else visibleChapters.add(ch);
        }
        refreshVisibility();
        renderLegend();
      });
    });
  }
  renderLegend();

  // ---- layout and view
  layoutSel.addEventListener("change", function () {
    var mode = layoutSel.value || null;
    Graph.dagMode(mode).dagLevelDistance(mode ? 28 : null);
    if (Graph.d3ReheatSimulation) Graph.d3ReheatSimulation();
    fitted = false;
  });
  document.getElementById("g3-clear").addEventListener("click", function () {
    input.value = "";
    clearSelection();
  });
  document.getElementById("g3-fit").addEventListener("click", function () {
    Graph.zoomToFit(800, 40);
  });

  // Fit the view once the layout settles, then honour a link such as
  // graph3d.html#thm:discunique.
  var fitted = false;
  Graph.onEngineStop(function () {
    if (fitted) return;
    fitted = true;
    Graph.zoomToFit(600, 40);
    var target = decodeURIComponent(location.hash.slice(1));
    if (target && byId.has(target)) setTimeout(function () { select(target, true); }, 700);
  });
})();
