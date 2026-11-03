// Blueprint website: filtering, deep links, and zoom on the dependency graph.
(function () {
  // Filter statements by number, title, label or Lean name.
  var filter = document.getElementById("filter");
  if (filter) {
    filter.addEventListener("input", function () {
      var q = filter.value.trim().toLowerCase();
      document.querySelectorAll("article.node").forEach(function (a) {
        var hit = !q || a.dataset.search.indexOf(q) >= 0;
        a.classList.toggle("hidden", !hit);
      });
      document.querySelectorAll("section.chapter").forEach(function (s) {
        var any = s.querySelector("article.node:not(.hidden)");
        s.classList.toggle("hidden", !any);
      });
    });
  }

  // Opening a link to a statement (from the graph or a "Uses" chip) also
  // expands its Lean code, so one click shows the formal proof.
  function openTarget() {
    var id = decodeURIComponent(location.hash.slice(1));
    if (!id) return;
    var node = document.getElementById(id);
    if (!node) return;
    var panel = node.querySelector("details.lean-panel");
    if (panel) panel.open = true;
  }
  window.addEventListener("hashchange", openTarget);
  openTarget();

  // Zoom for the dependency graph.
  var graph = document.getElementById("graph");
  if (graph) {
    var svg = graph.querySelector("svg");
    if (svg) {
      var w0 = parseFloat(svg.getAttribute("width")) || svg.getBBox().width;
      svg.removeAttribute("height");
      var scale = 1;
      var fit = function () {
        scale = Math.max(0.2, (graph.clientWidth - 20) / (w0 * 96 / 72));
        apply();
      };
      var apply = function () {
        svg.style.width = (w0 * 96 / 72 * scale) + "px";
      };
      document.querySelectorAll(".zoom button").forEach(function (b) {
        b.addEventListener("click", function () {
          var z = parseInt(b.dataset.z, 10);
          if (z === 0) fit();
          else { scale = Math.min(4, Math.max(0.2, scale * (z > 0 ? 1.25 : 0.8))); apply(); }
        });
      });
      fit();
    }
  }
})();

// ---- the library page: filtering, and formulas typeset when a declaration is opened
(function () {
  var filter = document.getElementById("lib-filter");
  if (filter) {
    var count = document.getElementById("lib-count");
    var total = document.querySelectorAll("details.lib-decl").length;
    filter.addEventListener("input", function () {
      var q = filter.value.trim().toLowerCase(), shown = 0;
      document.querySelectorAll("section.lib-file").forEach(function (sec) {
        var any = false;
        sec.querySelectorAll("details.lib-decl").forEach(function (d) {
          var hit = !q || d.dataset.search.indexOf(q) >= 0;
          d.classList.toggle("hidden", !hit);
          if (hit) { any = true; shown++; }
        });
        sec.classList.toggle("hidden", !any);
      });
      if (count) count.textContent = q ? shown + " of " + total + " declarations match" :
        count.dataset.all || count.textContent;
    });
    if (count) count.dataset.all = count.textContent;
  }
  document.querySelectorAll("details.lib-decl").forEach(function (d) {
    d.addEventListener("toggle", function () {
      var body = d.querySelector(".lib-body.mj-lazy");
      if (!d.open || !body) return;
      body.classList.remove("mj-lazy");
      body.classList.add("mj-now");
      if (window.MathJax && MathJax.typesetPromise) MathJax.typesetPromise([body]);
    });
  });
})();
