// Progressive enhancement for the MiniLean4 ebook. Everything here is optional:
// without JavaScript, steppers show every step, trace trees are fully expanded,
// and the sidebar is simply always present on wide screens.
(function () {
  "use strict";

  var I18N = (window.MINILEAN_I18N && window.MINILEAN_I18N.js) || {};
  var UI = (window.MINILEAN_I18N && window.MINILEAN_I18N.ui) || {};
  function t(key) { return I18N[key] || key; }
  window.MiniLeanT = t;

  // ----- Theme -----
  var themeBtn = document.getElementById("theme-toggle");
  function applyThemeLabel() {
    if (!themeBtn) return;
    var light = document.documentElement.classList.contains("light");
    themeBtn.textContent = light ? (UI.theme_dark || "dark") : (UI.theme_light || "light");
  }
  if (themeBtn) {
    themeBtn.addEventListener("click", function () {
      var light = document.documentElement.classList.toggle("light");
      localStorage.setItem("minilean-theme", light ? "light" : "dark");
      applyThemeLabel();
    });
    applyThemeLabel();
  }

  // ----- Scroll reveal: block elements fade up as they enter the viewport -----
  if ("IntersectionObserver" in window && !window.matchMedia("(prefers-reduced-motion: reduce)").matches
      && !document.body.classList.contains("page-print")) {
    var targets = document.querySelectorAll(
      ".content > h2, .content > aside, .content > .playground, .content > .rulebox, .content > .stepper, " +
      ".content > .theorem, .content > .definition, .content > .exercise, .content > .codeblock, .content > ul.trace, .content > .summary-box"
    );
    var io = new IntersectionObserver(function (entries) {
      entries.forEach(function (en) {
        if (en.isIntersecting) { en.target.classList.add("in"); io.unobserve(en.target); }
      });
    }, { rootMargin: "0px 0px -8% 0px" });
    targets.forEach(function (el) {
      var r = el.getBoundingClientRect();
      if (r.top < window.innerHeight) return; // already visible: no animation on load
      el.classList.add("reveal");
      io.observe(el);
    });
  }

  // ----- Sidebar on narrow screens -----
  var navBtn = document.getElementById("nav-toggle");
  if (navBtn) {
    navBtn.addEventListener("click", function () {
      var open = document.body.classList.toggle("nav-open");
      navBtn.setAttribute("aria-expanded", open ? "true" : "false");
      navBtn.textContent = open ? (UI.close || "close") : (UI.contents || "contents");
    });
    document.addEventListener("click", function (e) {
      if (!document.body.classList.contains("nav-open")) return;
      var sidebar = document.getElementById("sidebar");
      if (sidebar && !sidebar.contains(e.target) && e.target !== navBtn) {
        document.body.classList.remove("nav-open");
        navBtn.setAttribute("aria-expanded", "false");
        navBtn.textContent = UI.contents || "contents";
      }
    });
  }

  // Scroll the sidebar (and only the sidebar) so the current chapter is visible.
  var sidebarEl = document.getElementById("sidebar");
  var current = document.querySelector(".toc-list li.current");
  if (sidebarEl && current) {
    var target = current.offsetTop - sidebarEl.clientHeight / 2;
    if (target > 0) sidebarEl.scrollTop = target;
  }

  // ----- Steppers -----
  function makeButton(label, cls) {
    var b = document.createElement("button");
    b.type = "button";
    b.className = "stepper-btn" + (cls ? " " + cls : "");
    b.textContent = label;
    return b;
  }

  document.querySelectorAll(".stepper").forEach(function (box) {
    var steps = Array.prototype.slice.call(box.querySelectorAll(":scope > .step"));
    if (steps.length === 0) return;
    var index = 0;
    var showAll = false;

    var bar = document.createElement("div");
    bar.className = "stepper-bar";
    var title = document.createElement("span");
    title.className = "stepper-title";
    title.textContent = box.getAttribute("data-title") || "Step through";
    var prev = makeButton(t("prev"));
    var count = document.createElement("span");
    count.className = "stepper-count";
    var next = makeButton(t("next"));
    var all = makeButton(t("show all"));
    bar.appendChild(title);
    bar.appendChild(prev);
    bar.appendChild(count);
    bar.appendChild(next);
    bar.appendChild(all);
    box.insertBefore(bar, box.firstChild);

    function render() {
      box.classList.toggle("show-all", showAll);
      steps.forEach(function (s, i) {
        if (showAll) s.removeAttribute("hidden");
        else if (i === index) s.removeAttribute("hidden");
        else s.setAttribute("hidden", "");
      });
      count.textContent = t("step") + " " + (index + 1) + " / " + steps.length;
      prev.disabled = showAll || index === 0;
      next.disabled = showAll || index === steps.length - 1;
      all.classList.toggle("active", showAll);
      all.textContent = showAll ? t("one at a time") : t("show all");
    }
    prev.addEventListener("click", function () { if (index > 0) { index--; render(); } });
    next.addEventListener("click", function () { if (index < steps.length - 1) { index++; render(); } });
    all.addEventListener("click", function () { showAll = !showAll; render(); });
    box.addEventListener("keydown", function (e) {
      if (showAll) return;
      if (e.key === "ArrowRight") { next.click(); e.preventDefault(); }
      if (e.key === "ArrowLeft") { prev.click(); e.preventDefault(); }
    });
    box.tabIndex = 0;
    render();
  });

  // ----- Trace trees -----
  document.querySelectorAll("ul.trace").forEach(function (tree) {
    tree.querySelectorAll("li").forEach(function (li) {
      var child = Array.prototype.find.call(li.children, function (c) { return c.tagName === "UL"; });
      if (!child) return;
      var count = child.querySelectorAll("li").length;
      var btn = document.createElement("button");
      btn.type = "button";
      btn.className = "trace-toggle";
      btn.setAttribute("aria-expanded", "true");
      btn.textContent = t("hide") + " " + count;
      // Insert after the first text/inline content, before the nested list.
      li.insertBefore(btn, child);
      btn.addEventListener("click", function () {
        var collapsed = li.classList.toggle("collapsed");
        btn.setAttribute("aria-expanded", collapsed ? "false" : "true");
        btn.textContent = (collapsed ? t("show") : t("hide")) + " " + count;
      });
    });
  });
})();
