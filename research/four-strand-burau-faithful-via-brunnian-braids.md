---
rg: 2
id: four-strand-burau-faithful-via-brunnian-braids
kind: route
title: "4-strand Burau is faithful: the Brunnian reduction plus no Brunnian kernel elements"
target: four-strand-burau-representation-is-faithful
requires:
  - burau-four-faithful-iff-faithful-on-brunnian-braids
  - brunnian-four-braids-avoid-burau-kernel
---

The proof architecture of arXiv:2607.05283v1 (Bharathram–Birman–Brendle), factored:

- Proposition 1.2 = `burau-four-faithful-iff-faithful-on-brunnian-braids`, independently
  established through Long's theorem.
- Theorem 6.6 = `brunnian-four-braids-avoid-burau-kernel`, open while its combinatorial core is
  checked.

Together they give `ker ρ_4 = 1`. This route supports `four-strand-burau-representation-is-faithful`
only when both inputs are established. If the owner lane later lands a citation route importing
the preprint's Main Theorem, the two routes carry the same argument, and one of them should be
retired.
