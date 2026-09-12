---
rg: 2
id: fp-simple-highly-transitive-groups-satisfy-pbh-citation
kind: route
title: Import Belk--Fournier-Facio--Hyde--Zaremsky Theorem C
target: fp-simple-highly-transitive-groups-satisfy-pbh
requires: []
artifacts:
  - research/artifacts/bh-metabelian-products-2026-09-12.md
---

Citation import. J. Belk, F. Fournier-Facio, J. Hyde, M. C. B. Zaremsky,
*Boone--Higman embeddings of Aut(F_n) and mapping class groups of punctured
surfaces*, arXiv:2503.21882v2. Read from the PDF text extracted on MSI
(`/scratch.global/sauer354/bh-reviewer/2503.21882.txt`) on 2026-09-12.

**The proof's chain, verbatim or close paraphrase:**
- **(i) ⟹ (ii):** "by [Zarb, Theorem A]".
- **(ii) ⟹ (iii):** "By [BBMZa, Proposition 5.4], any twisted Brin–Thompson group
  admits a faithful highly transitive action".
- **(iii) ⟹ (iv):** "Any finitely presented simple group admitting a highly
  transitive action is MIF thanks to [HO16, Theorem 5.9] (see also [LBMB22b,
  Proposition A.1])".
- **(iv) ⟹ (i):** a finitely presented simple MIF group `G` embeds in
  `Aut_G(G * F_2)`, which admits an action of type (A) by their Theorem E.

**Why every subgroup is covered.** That last step puts `G` itself, and hence
every subgroup of `G`, inside a group with a type (A) action. No finite
generation of the subgroup is used.

**Direct products.** In the proof of Corollary F: "By [Zarb, Proposition 5.5],
the direct product A×B also satisfies PBH". Section 1 adds: "PBH is stable under
commensurability and direct products [Zarb]".

Not reproved here; no Lean counterpart.
