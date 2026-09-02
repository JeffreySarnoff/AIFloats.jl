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
      if (nested === toggle) return;
      nested.checked = false;
      // Setting `checked` from script fires no `change` event, so the recorded
      // state has to be cleared here or the group would spring back open after
      // the next navigation.
      var label = nested.nextElementSibling;
      if (label !== null) setOpen("group:" + label.textContent.trim(), false);
    });

    // Page entries nested inside the group collapse with it, for the same
    // reason and by the same rule: an entry re-opens showing one level.
    entry.querySelectorAll("a.tocitem.has-internal-toggle").forEach(function (nested) {
      var list = nested.nextElementSibling;
      if (list === null || !list.classList.contains("internal")) return;
      list.classList.add("is-collapsed");
      nested.classList.add("is-closed");
      setOpen(keyFor(nested.getAttribute("href") || ""), false);
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

  // Which entries are open survives a navigation. Without that, clicking an
  // entry name costs TWO clicks to see anything: the first navigates, the page
  // reloads, and the freshly built menu has forgotten the click ever happened.
  // sessionStorage rather than localStorage — this is the shape of one visit,
  // not a preference, and a new session should open with the menu closed.
  var OPEN_KEY = "documenter-open-sections";

  function readOpen() {
    try {
      return JSON.parse(window.sessionStorage.getItem(OPEN_KEY)) || [];
    } catch (e) {
      return [];
    }
  }

  function writeOpen(keys) {
    try {
      window.sessionStorage.setItem(OPEN_KEY, JSON.stringify(keys));
    } catch (e) {
      /* private browsing, file:// with storage disabled — the menu still works,
         it just forgets between pages */
    }
  }

  function setOpen(key, open) {
    var keys = readOpen().filter(function (k) { return k !== key; });
    if (open) keys.push(key);
    writeOpen(keys);
  }

  var openOnLoad = readOpen();

  // An entry is a page link (<a>) rather than a group label (<label>); the
  // groups have their own toggle already.
  menu.querySelectorAll("li > a.tocitem").forEach(function (entry) {
    var href = entry.getAttribute("href") || "";
    var key = keyFor(href);
    var sections = entry.nextElementSibling;
    var own = sections !== null && sections.tagName === "UL" &&
              sections.classList.contains("internal");

    if (!own) {
      var headings = sectionsFor[key];
      if (!headings || headings.length === 0) return;
      sections = buildSections(entry, headings);
    }

    entry.classList.add("has-internal-toggle");
    var chevron = document.createElement("i");
    chevron.className = "docs-chevron";
    entry.appendChild(chevron);

    var isCurrent = entry.closest("li.is-active") !== null;

    // Closed unless this visit left it open, so a fresh arrival shows every
    // entry the same way and the marker means the same thing everywhere:
    // `>` there is more here, `v` here it is.
    if (openOnLoad.indexOf(key) === -1) {
      sections.classList.add("is-collapsed");
      entry.classList.add("is-closed");
    }

    function toggle() {
      var closed = sections.classList.toggle("is-collapsed");
      entry.classList.toggle("is-closed");
      setOpen(key, !closed);
    }

    entry.addEventListener("click", function (event) {
      if (event.target === chevron) {
        // The marker is a control and nothing else: it opens the entry where
        // the reader is, without taking them anywhere.
        event.preventDefault();
        toggle();
        return;
      }
      if (isCurrent) {
        // The link points at the page already being read, so it goes nowhere
        // useful. Spend the click on the toggle.
        event.preventDefault();
        toggle();
        return;
      }
      // Elsewhere the name navigates — and records that its sections should be
      // showing when the reader lands, so one click is one click.
      setOpen(key, true);
    });
  });

  // A group's checkbox is Documenter's, but its open state should survive a
  // navigation for the same reason.
  menu.querySelectorAll("input.collapse-toggle").forEach(function (box) {
    var label = box.nextElementSibling;
    var name = label === null ? null : label.textContent.trim();
    if (name === null) return;
    var key = "group:" + name;
    if (openOnLoad.indexOf(key) !== -1) box.checked = true;
    box.addEventListener("change", function () {
      setOpen(key, box.checked);
    });
  });
});
