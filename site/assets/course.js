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
      if (start < 0 && /(^|\s)Proof\.?$/.test(text)) start = index;
      if (start >= 0 && /\b(Qed|Defined)\.$/.test(text)) {
        groups.push([start, index]);
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
})();
