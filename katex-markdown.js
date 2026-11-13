// 1. Render standard $...$ and $$...$$ LaTeX math in Markdown/Verso prose & tooltips using bundled KaTeX
// 2. Make all theorem/lemma/example proofs collapsible (collapsed by default)
// 3. Auto-link inline `code` references to theorems, definitions, and modules using xref.json
(function () {
  "use strict";

  // --- KaTeX rendering for $...$ and $$...$$ ---
  function renderMathInHtmlString(html) {
    // Display math: $$ ... $$ (possibly spanning multiple lines and containing <em> from underscores)
    html = html.replace(/\$\$([\s\S]+?)\$\$/g, function (_match, tex) {
      var clean = restoreMarkdownEmph(tex);
      try {
        return katex.renderToString(clean.trim(), {
          displayMode: true,
          throwOnError: false,
        });
      } catch (_e) {
        return _match;
      }
    });

    // Inline math: $ ... $ (not crossing paragraph boundaries, avoiding <code>...</code> tags)
    var parts = html.split(
      /(<code\b[^>]*>[\s\S]*?<\/code>|<pre\b[^>]*>[\s\S]*?<\/pre>|<span\b[^>]*class="katex[\s\S]*?<\/span>)/gi
    );
    for (var i = 0; i < parts.length; i += 2) {
      parts[i] = parts[i].replace(/\$([^\$\n][^$]*?)\$/g, function (match, tex) {
        var clean = restoreMarkdownEmph(tex);
        try {
          return katex.renderToString(clean.trim(), {
            displayMode: false,
            throwOnError: false,
          });
        } catch (_e) {
          return match;
        }
      });
    }
    return parts.join("");
  }

  function restoreMarkdownEmph(s) {
    return s
      .replace(/<\/?em>/gi, "_")
      .replace(/<\/?strong>/gi, "__")
      .replace(/&lt;/g, "<")
      .replace(/&gt;/g, ">")
      .replace(/&amp;/g, "&")
      // Restore CommonMark-stripped backslash escapes inside math:
      // 1. Row break `\\` at end of line (stripped to single `\` by CommonMark)
      .replace(/\\(\s*\r?\n)/g, "\\\\$1")
      // 2. Negative thin space `\!` before \left, \bigl, etc.
      .replace(/!(\\(?:left|bigl|Bigl|biggl|Biggl)\b)/g, "\\!$1")
      // 3. Thin space `\,` surrounded by whitespace, after comma `,\,`, or before differentials `, d\mu`
      .replace(/(\s),(?=\s|$)/g, "$1\\,")
      .replace(/,,/g, ",\\,")
      .replace(/([0-9a-zA-Z}\])])\s*,\s*(d(?:\\[a-zA-Z]+|[a-zA-Z])\b)/g, "$1\\, $2")
      // 4. Medium/thick space `\;` surrounded by whitespace
      .replace(/(\s);(?=\s|$)/g, "$1\\;")
      // 5. Set braces `\{ ... \}` stripped to `{ ... }` by CommonMark (when not a macro/sub/sup argument)
      .replace(
        /(\\(?:left|right|bigl|bigr|Bigl|Bigr|biggl|biggr|Biggl|Biggr))\{/g,
        "$1\\{"
      )
      .replace(
        /(\\(?:left|right|bigl|bigr|Bigl|Bigr|biggl|biggr|Biggl|Biggr))\}/g,
        "$1\\}"
      )
      .replace(
        /(^|(?:\\(?:in|subseteq|subset|supseteq|supset|setminus|cup|cap|times|equiv|ne|neq)\s+)|[=(,]\s*)\{([^{}]+)\}(?![_^])/g,
        "$1\\{$2\\}"
      );
  }

  // Fix Verso's md2Html list rendering where <ol>/<ul> items are emitted without <li> wrappers
  function fixListItemsInRoot(root) {
    if (!root || !root.querySelectorAll) return;
    var lists = root.querySelectorAll(
      ".md-text ol, .md-text ul, .verso-text ol, .verso-text ul, .docstring ol, .docstring ul"
    );
    for (var i = 0; i < lists.length; i++) {
      var list = lists[i];
      if (list.dataset.liFixed === "true") continue;
      list.dataset.liFixed = "true";
      var children = Array.prototype.slice.call(list.children);
      var hasNonLi = false;
      for (var j = 0; j < children.length; j++) {
        if (children[j].tagName !== "LI") {
          hasNonLi = true;
          break;
        }
      }
      if (!hasNonLi) continue;
      var currentLi = null;
      for (var k = 0; k < children.length; k++) {
        var child = children[k];
        if (child.tagName === "LI") {
          currentLi = child;
        } else if (child.tagName === "P" || !currentLi) {
          var li = document.createElement("li");
          list.insertBefore(li, child);
          li.appendChild(child);
          currentLi = li;
        } else {
          currentLi.appendChild(child);
        }
      }
    }
  }

  function processElement(el) {
    if (!el || el.dataset.katexProcessed === "true") return;
    if (el.innerHTML.indexOf("$") !== -1) {
      el.innerHTML = renderMathInHtmlString(el.innerHTML);
    }
    el.dataset.katexProcessed = "true";
  }

  function processAllMath() {
    if (typeof katex === "undefined") return;
    var selectors =
      ".md-text p, .md-text li, .md-text h1, .md-text h2, .md-text h3, .md-text h4, .verso-text p, .verso-text li, .docstring p, .docstring li, .page-toc a";
    var nodes = document.querySelectorAll(selectors);
    for (var i = 0; i < nodes.length; i++) {
      processElement(nodes[i]);
    }
  }

  // --- Auto-linking of inline `code` references to declarations & modules ---
  var xrefLookup = null;

  function buildXrefLookup(data) {
    var map = Object.create(null);
    var currentPath = window.location.pathname || "";

    var consts =
      data &&
      data["VersoHtml.constant"] &&
      data["VersoHtml.constant"].contents;
    if (consts) {
      var keys = Object.keys(consts);
      for (var i = 0; i < keys.length; i++) {
        var key = keys[i];
        var entries = consts[key];
        if (!entries || !entries.length) continue;
        var entry = entries[0];
        var addr = entry.address.replace(/^\/+/, "") + "#" + entry.id;
        var isCurrentPage = currentPath.indexOf(entry.address) !== -1;

        map[key] = addr;
        var parts = key.split(".");
        for (var p = 1; p < parts.length; p++) {
          var suffix = parts.slice(p).join(".");
          if (!map[suffix] || isCurrentPage) {
            map[suffix] = addr;
          }
        }
      }
    }

    var mods =
      data &&
      data["VersoHtml.module"] &&
      data["VersoHtml.module"].contents;
    if (mods) {
      var modKeys = Object.keys(mods);
      for (var j = 0; j < modKeys.length; j++) {
        var modName = modKeys[j];
        var modEntries = mods[modName];
        if (!modEntries || !modEntries.length) continue;
        var modAddr = modEntries[0].address.replace(/^\/+/, "");
        map[modName] = modAddr;
        map[modName.replace(/\./g, "/") + ".lean"] = modAddr;
        var shortMod = modName.split(".").pop();
        if (shortMod) {
          map[shortMod + ".lean"] = modAddr;
        }
      }
    }

    return map;
  }

  function resolveCodeTarget(raw) {
    if (!raw) return null;
    // Skip complex expressions containing operators or relations
    if (/[+=<>≤≥≠≈→↔↦∀∃∧∨⊢:]|\s-\s|\s\*\s|\s\/\s/.test(raw)) {
      return null;
    }
    var candidates = [raw];
    var head = raw.split(/\s+/)[0];
    if (head && head !== raw) {
      candidates.push(head);
    }

    for (var i = 0; i < candidates.length; i++) {
      var cand = candidates[i];
      if (xrefLookup && xrefLookup[cand]) {
        return xrefLookup[cand];
      }
      var el = document.getElementById(cand);
      if (el) {
        return (
          window.location.pathname +
          window.location.search +
          "#" +
          encodeURIComponent(cand)
        );
      }
    }
    return null;
  }

  function linkCodeRefsInRoot(root) {
    if (!root || !root.querySelectorAll) return;

    // Fix manual #anchor links in prose so <base href="..."> doesn't send them to site root
    var anchors = root.querySelectorAll(
      ".md-text a[href^='#'], .verso-text a[href^='#'], .docstring a[href^='#']"
    );
    for (var a = 0; a < anchors.length; a++) {
      var anchor = anchors[a];
      var href = anchor.getAttribute("href");
      if (href && href.charAt(0) === "#") {
        anchor.setAttribute(
          "href",
          window.location.pathname + window.location.search + href
        );
      }
    }

    var codes = root.querySelectorAll(
      ".md-text code, .verso-text code, .docstring code"
    );
    for (var i = 0; i < codes.length; i++) {
      var code = codes[i];
      if (code.dataset.xrefProcessed === "true") continue;
      if (code.closest("a") || code.closest("pre")) {
        code.dataset.xrefProcessed = "true";
        continue;
      }
      var raw = (code.textContent || "").trim();
      var target = resolveCodeTarget(raw);
      if (target) {
        var link = document.createElement("a");
        link.className = "doc-xref-link";
        link.href = target;
        code.parentNode.insertBefore(link, code);
        link.appendChild(code);
        code.dataset.xrefProcessed = "true";
      } else if (xrefLookup) {
        code.dataset.xrefProcessed = "true";
      }
    }
  }

  function initCrossRefs() {
    linkCodeRefsInRoot(document);
    if (typeof fetch === "function") {
      fetch("xref.json")
        .then(function (r) {
          return r.ok ? r.json() : null;
        })
        .then(function (data) {
          if (data) {
            xrefLookup = buildXrefLookup(data);
            linkCodeRefsInRoot(document);
          }
        })
        .catch(function () {});
    }
  }

  // --- Collapsible Proofs ---
  function isProofDeclaration(block) {
    var children = block.children;
    for (var i = 0; i < children.length; i++) {
      var child = children[i];
      if (
        child.classList &&
        child.classList.contains("keyword") &&
        child.classList.contains("token")
      ) {
        var kw = child.textContent.trim();
        if (kw === "theorem" || kw === "lemma" || kw === "example") {
          return true;
        }
        if (
          kw === "def" ||
          kw === "abbrev" ||
          kw === "structure" ||
          kw === "class" ||
          kw === "inductive" ||
          kw === "opaque" ||
          kw === "axiom"
        ) {
          return false;
        }
      }
    }
    return false;
  }

  function findProofSplitNode(block) {
    var children = block.children;
    for (var i = 0; i < children.length; i++) {
      var child = children[i];
      var binding =
        (child.getAttribute && child.getAttribute("data-binding")) || "";
      if (
        binding.indexOf("Lean.Parser.Command.declValSimple") !== -1 ||
        binding.indexOf("Lean.Parser.Command.declValEqns") !== -1 ||
        binding.indexOf("Lean.Parser.Command.whereStructInst") !== -1
      ) {
        return child;
      }
    }
    return null;
  }

  function setupCollapsibleProofs() {
    var blocks = document.querySelectorAll("code.hl.lean.block");
    var proofToggles = [];

    for (var i = 0; i < blocks.length; i++) {
      var block = blocks[i];
      if (block.dataset.proofProcessed === "true") continue;
      if (!isProofDeclaration(block)) continue;

      var splitNode = findProofSplitNode(block);
      if (!splitNode) continue;

      block.dataset.proofProcessed = "true";

      var proofSpan = document.createElement("span");
      proofSpan.className = "proof-body collapsed";

      var curr = splitNode;
      while (curr) {
        var next = curr.nextSibling;
        proofSpan.appendChild(curr);
        curr = next;
      }

      var btn = document.createElement("button");
      btn.type = "button";
      btn.className = "proof-toggle-btn";
      btn.textContent = "▶ Proof";
      btn.title = "Click to expand/collapse proof";

      (function (button, body) {
        button.addEventListener("click", function (e) {
          e.stopPropagation();
          var isCollapsed = body.classList.toggle("collapsed");
          button.textContent = isCollapsed ? "▶ Proof" : "▼ Proof";
        });
        proofToggles.push({ button: button, body: body });
      })(btn, proofSpan);

      block.appendChild(btn);
      block.appendChild(proofSpan);
    }

    if (proofToggles.length > 0) {
      var titleBar =
        document.querySelector("header.title-bar") ||
        document.querySelector(".code-content");
      if (titleBar && !document.querySelector(".proof-global-controls")) {
        var controls = document.createElement("div");
        controls.className = "proof-global-controls";

        var globalBtn = document.createElement("button");
        globalBtn.type = "button";
        globalBtn.className = "proof-global-btn";
        globalBtn.textContent =
          "▶ Show all proofs (" + proofToggles.length + ")";
        var allExpanded = false;

        globalBtn.addEventListener("click", function () {
          allExpanded = !allExpanded;
          for (var j = 0; j < proofToggles.length; j++) {
            var item = proofToggles[j];
            if (allExpanded) {
              item.body.classList.remove("collapsed");
              item.button.textContent = "▼ Proof";
            } else {
              item.body.classList.add("collapsed");
              item.button.textContent = "▶ Proof";
            }
          }
          globalBtn.textContent = allExpanded
            ? "▼ Hide all proofs (" + proofToggles.length + ")"
            : "▶ Show all proofs (" + proofToggles.length + ")";
        });

        controls.appendChild(globalBtn);
        titleBar.appendChild(controls);
      }
    }
  }

  function init() {
    fixListItemsInRoot(document);
    processAllMath();
    setupCollapsibleProofs();
    initCrossRefs();
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", init);
  } else {
    init();
  }

  // Also render math and cross-reference links inside hover tooltips when they appear
  var observer = new MutationObserver(function (mutations) {
    for (var i = 0; i < mutations.length; i++) {
      var added = mutations[i].addedNodes;
      for (var j = 0; j < added.length; j++) {
        var node = added[j];
        if (node.nodeType === 1) {
          fixListItemsInRoot(node);
          if (typeof katex !== "undefined") {
            var targets = node.querySelectorAll
              ? node.querySelectorAll(
                  ".docstring p, .docstring li, .md-text p, .md-text li"
                )
              : [];
            for (var k = 0; k < targets.length; k++) {
              processElement(targets[k]);
            }
          }
          linkCodeRefsInRoot(node);
        }
      }
    }
  });
  observer.observe(document.documentElement, { childList: true, subtree: true });
})();
