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

  // 2. THE ACTIVE PAGE'S OWN SECTIONS BECOME AN ACCORDION.
  //
  // Documenter lists a page's headings under its menu entry — the `⚬` items —
  // but only for the page being read, and with no way to put them away again.
  // A single-page entry such as Algorithms therefore behaved unlike every group
  // beside it: its children appeared and then stayed.
  //
  // The entry is an <a> pointing at the page the reader is already on, so its
  // click does nothing useful. Spend it on the toggle instead, and mark the
  // entry with the same chevron the groups use so it reads as collapsible.
  menu.querySelectorAll("ul.internal").forEach(function (sections) {
    var entry = sections.previousElementSibling;
    if (entry === null || entry.tagName !== "A") return;

    entry.classList.add("has-internal-toggle");
    var chevron = document.createElement("i");
    chevron.className = "docs-chevron";
    entry.appendChild(chevron);

    // Start CLOSED. Documenter reveals the active page's headings on load,
    // which made this entry the one thing in the menu that arrived expanded —
    // every group starts at `>` and waits to be asked. Closing it on setup
    // makes the menu uniform, and makes the marker mean the same thing
    // wherever it appears: `>` there is more here, `v` here it is.
    sections.classList.add("is-collapsed");
    entry.classList.add("is-closed");

    entry.addEventListener("click", function (event) {
      event.preventDefault();
      sections.classList.toggle("is-collapsed");
      entry.classList.toggle("is-closed");
    });
  });
});
