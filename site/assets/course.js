(() => {
  const normalize = (node) => (node.textContent || "").trim();

  // Coqdoc emits proof sentences as adjacent nodes inside a code block.  Fold
  // complete Proof...Qed/Defined blocks without changing their contents.
  document.querySelectorAll("div.code").forEach((block) => {
    const nodes = Array.from(block.childNodes);
    let start = -1;
    let groups = [];
    nodes.forEach((node, index) => {
      const text = normalize(node);
      // Coqdoc puts the keyword and the following full stop in separate DOM
      // nodes, so match the keyword itself and include the rest of its line.
      if (start < 0 && text === "Proof") start = index;
      if (start >= 0 && /^(Qed|Defined)$/.test(text)) {
        let end = index;
        while (end + 1 < nodes.length) {
          end += 1;
          if (nodes[end].nodeName === "BR") break;
        }
        groups.push([start, end]);
        start = -1;
      }
    });
    groups.reverse().forEach(([first, last]) => {
      const details = document.createElement("details");
      details.className = "course-proof";
      const summary = document.createElement("summary");
      summary.textContent = "Proof (click to expand)";
      details.appendChild(summary);
      block.insertBefore(details, nodes[first]);
      for (let i = first; i <= last; i += 1) details.appendChild(nodes[i]);
    });
  });

  // Fold infrastructure or perspective sections whose heading explicitly
  // marks them as optional.  The heading remains inside the details element so
  // its anchor and printed title are preserved.
  document.querySelectorAll("h2, h3, h4").forEach((heading) => {
    if (!/^Optional\b/i.test(normalize(heading))) return;
    const level = Number(heading.tagName.slice(1));
    const details = document.createElement("details");
    details.className = "optional-section";
    const summary = document.createElement("summary");
    summary.textContent = normalize(heading) + " (click to expand)";
    heading.parentNode.insertBefore(details, heading);
    details.appendChild(summary);
    let node = heading;
    while (node) {
      const next = node.nextSibling;
      if (node !== heading && /^H[1-6]$/.test(node.nodeName) &&
          Number(node.nodeName.slice(1)) <= level) break;
      details.appendChild(node);
      node = next;
    }
  });
})();
