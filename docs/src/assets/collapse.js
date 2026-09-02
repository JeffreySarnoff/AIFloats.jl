// Cascading collapse for the sidebar menu.
//
// Documenter's menu is a pure-CSS affair: each collapsible entry is a hidden
// checkbox with the entry name as its <label>, and `ul.collapsed` is shown only
// while that checkbox is `:checked`. Clicking an entry therefore toggles it both
// ways already, and closing an entry hides everything nested inside it — the
// parent's <ul> is what goes to `display: none`.
//
// What CSS cannot do is FORGET. The nested checkboxes keep their state while
// hidden, so re-opening a section restores whichever subsections happened to be
// open when it was closed, which is not what "collapse away" leads a reader to
// expect. This unchecks every descendant toggle when an entry is closed, so an
// entry always re-opens showing exactly one level.
//
// Opening is deliberately left alone: expanding a section reveals its immediate
// children and nothing deeper.
document.addEventListener("DOMContentLoaded", function () {
  var menu = document.querySelector("nav.docs-sidebar ul.docs-menu");
  if (menu === null) return;

  menu.addEventListener("change", function (event) {
    var toggle = event.target;
    if (!toggle.classList || !toggle.classList.contains("collapse-toggle")) return;
    if (toggle.checked) return; // opening — leave the levels below untouched

    var entry = toggle.closest("li");
    if (entry === null) return;
    entry.querySelectorAll("input.collapse-toggle").forEach(function (nested) {
      if (nested !== toggle) nested.checked = false;
    });
  });
});
