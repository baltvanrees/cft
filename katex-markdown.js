// 1. Render standard $...$ and $$...$$ LaTeX math in Markdown/Verso prose & tooltips using bundled KaTeX
// 2. Make all theorem/lemma/example proofs collapsible (collapsed by default)
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
      .replace(/&amp;/g, "&");
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

  // --- Collapsible Proofs ---
  function isProofDeclaration(block) {
    // Check top-level keyword tokens of the declaration
    var children = block.children;
    for (var i = 0; i < children.length; i++) {
      var child = children[i];
      if (child.classList && child.classList.contains("keyword") && child.classList.contains("token")) {
        var kw = child.textContent.trim();
        if (kw === "theorem" || kw === "lemma" || kw === "example") {
          return true;
        }
        if (kw === "def" || kw === "abbrev" || kw === "structure" || kw === "class" || kw === "inductive" || kw === "opaque" || kw === "axiom") {
          return false;
        }
      }
    }
    return false;
  }

  function findProofSplitNode(block) {
    // Find the direct child of `block` that represents `:=` or `where` starting the proof
    var children = block.children;
    for (var i = 0; i < children.length; i++) {
      var child = children[i];
      var binding = (child.getAttribute && child.getAttribute("data-binding")) || "";
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

      // Create the collapsible wrapper and move `splitNode` and all following siblings into it
      var proofSpan = document.createElement("span");
      proofSpan.className = "proof-body collapsed";

      var curr = splitNode;
      while (curr) {
        var next = curr.nextSibling;
        proofSpan.appendChild(curr);
        curr = next;
      }

      // Create the toggle button
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

    // Add a global "Show all proofs / Hide all proofs" button in the top title bar if there are proofs
    if (proofToggles.length > 0) {
      var titleBar = document.querySelector("header.title-bar") || document.querySelector(".code-content");
      if (titleBar && !document.querySelector(".proof-global-controls")) {
        var controls = document.createElement("div");
        controls.className = "proof-global-controls";

        var globalBtn = document.createElement("button");
        globalBtn.type = "button";
        globalBtn.className = "proof-global-btn";
        globalBtn.textContent = "▶ Show all proofs (" + proofToggles.length + ")";
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
    processAllMath();
    setupCollapsibleProofs();
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", init);
  } else {
    init();
  }

  // Also render math inside hover tooltips when they appear
  var observer = new MutationObserver(function (mutations) {
    if (typeof katex === "undefined") return;
    for (var i = 0; i < mutations.length; i++) {
      var added = mutations[i].addedNodes;
      for (var j = 0; j < added.length; j++) {
        var node = added[j];
        if (node.nodeType === 1) {
          var targets = node.querySelectorAll
            ? node.querySelectorAll(".docstring p, .docstring li, .md-text p, .md-text li")
            : [];
          for (var k = 0; k < targets.length; k++) {
            processElement(targets[k]);
          }
        }
      }
    }
  });
  observer.observe(document.documentElement, { childList: true, subtree: true });
})();
