// Sidebar menu behaviour, in two parts.
//
// Documenter's menu is otherwise a pure-CSS affair: a collapsible GROUP is a
// hidden checkbox with the group name as its <label>, and `ul.collapsed` shows
// only while that checkbox is `:checked`. Groups therefore already toggle both
// ways on a click, at any depth. Two things that mechanism cannot do are added
// here.
document.addEventListener("DOMContentLoaded", function () {
  var menu = document.querySelector("nav.docs-sidebar ul.docs-menu");
  if (menu === null) return;

  // 1. CASCADING COLLAPSE.
  //
  // CSS has no way to forget. Closing a group hides everything nested inside
  // it, because the group's <ul> is what goes to `display: none` — but the
  // nested checkboxes keep their state while hidden, so re-opening the group
  // restores whichever subgroups happened to be open when it was closed. Unset
  // them, so a group always re-opens showing exactly one level.
  //
  // Opening is deliberately left alone: expanding a group reveals its immediate
  // children and nothing deeper.
  menu.addEventListener("change", function (event) {
    var toggle = event.target;
    if (!toggle.classList || !toggle.classList.contains("collapse-toggle")) return;
    if (toggle.checked) return;

    var entry = toggle.closest("li");
    if (entry === null) return;
    entry.querySelectorAll("input.collapse-toggle").forEach(function (nested) {
      if (nested !== toggle) nested.checked = false;
    });
  });

  // 2. EVERY PAGE ENTRY BECOMES AN ACCORDION.
  //
  // Documenter lists a page's headings under its menu entry — the `⚬` items —
  // but only for the page being read. Every other entry had no children in the
  // DOM at all, so the marker that means "there is more here" appeared on one
  // entry at a time while the rest of the menu stayed silent about pages that
  // have just as much under them.
  //
  // assets/menu-sections.js supplies the level-2 headings of every page,
  // generated from the built HTML at docs-build time. Entries Documenter did
  // not furnish get their list built here, in the same markup Documenter uses,
  // so the theme styles them identically.
  var sectionsFor = window.documenterMenuSections || {};

  // The menu's hrefs are relative to the page being viewed — `96-algorithms.html`
  // from the root, `../96-algorithms.html` from a subdirectory — while the map is
  // keyed by path from the site root. Stripping the leading `../` hops is the
  // whole of the difference, and works at any depth.
  function keyFor(href) {
    return href.replace(/^(\.\.\/)+/, "").replace(/#.*$/, "");
  }

  function buildSections(entry, headings) {
    var list = document.createElement("ul");
    list.className = "internal";
    headings.forEach(function (heading) {
      var item = document.createElement("li");
      var link = document.createElement("a");
      link.className = "tocitem";
      link.href = entry.getAttribute("href") + "#" + heading[0];
      var label = document.createElement("span");
      label.textContent = heading[1];
      link.appendChild(label);
      item.appendChild(link);
      list.appendChild(item);
    });
    entry.parentNode.insertBefore(list, entry.nextSibling);
    return list;
  }

  // An entry is a page link (<a>) rather than a group label (<label>); the
  // groups have their own toggle already.
  menu.querySelectorAll("li > a.tocitem").forEach(function (entry) {
    var sections = entry.nextElementSibling;
    var own = sections !== null && sections.tagName === "UL" &&
              sections.classList.contains("internal");

    if (!own) {
      var headings = sectionsFor[keyFor(entry.getAttribute("href") || "")];
      if (!headings || headings.length === 0) return;
      sections = buildSections(entry, headings);
    }

    entry.classList.add("has-internal-toggle");
    var chevron = document.createElement("i");
    chevron.className = "docs-chevron";
    entry.appendChild(chevron);

    // Start CLOSED, so every entry with more under it arrives showing the same
    // marker, and the marker means the same thing wherever it appears: `>`
    // there is more here, `v` here it is.
    sections.classList.add("is-collapsed");
    entry.classList.add("is-closed");

    entry.addEventListener("click", function (event) {
      // On the page being read the link goes nowhere useful, so the click is
      // the toggle. Elsewhere the first click should still navigate — but only
      // when it lands on the entry name, not on the marker, which is a control
      // and nothing else.
      var onMarker = event.target === chevron;
      if (!onMarker && !entry.classList.contains("is-current")) return;
      event.preventDefault();
      sections.classList.toggle("is-collapsed");
      entry.classList.toggle("is-closed");
    });

    if (entry.closest("li.is-active") !== null) entry.classList.add("is-current");
  });
});
