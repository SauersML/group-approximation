---
rg: 2
id: decidable-graphical-non-exact-groups-exist
kind: claim
title: Osajda's graphical groups with isometrically embedded expanders, and his CAT(0)-cubical groups without property A, can be built with solvable word problem
distinct_from:
  decidable-residually-finite-non-exact-group-exists: that is Osajda's residually finite non-exact group (arXiv:1703.03791), shown decidable through residually finite finitely presented stages and McKinsey's algorithm; this is his earlier pair from arXiv:1406.5015, shown decidable through Dehn's algorithm, and it adds two properties that group is not shown to have — isometrically embedded expanders (so no Haagerup host), and, for the second group, a proper action on a CAT(0) cube complex.
  haagerup-hosts-carry-no-weak-expander: that excludes expander-type inputs from Haagerup hosts; item 1 here supplies a decidable such input, and item 2 supplies a decidable non-exact input that this exclusion does not reach.
artifacts:
  - research/artifacts/gq-bh-bh-graphical-sc-hard-test-case.md
---

**ESTABLISHED (lane proof, not reviewed; no priority claimed).** Proof route:
`decidable-graphical-non-exact-groups-proof`. The constructions are Osajda's,
*Small cancellation labellings of some infinite graphs and applications*, arXiv:1406.5015.
Its TeX source (arXiv e-print, `sclsiga200514.tex`) was read on MSI. What this node adds is
the word-problem algorithm.

1. **Isometric expanders.** There is a finitely generated group `G_exp`, given by a
   recursive graphical `C'(1/24)` presentation, that has **solvable word problem** and
   whose Cayley graph contains an expander family isometrically. So `G_exp`:
   - is not coarsely embeddable into Hilbert space, and hence is not exact;
   - carries a weakly embedded expander, so by `haagerup-hosts-carry-no-weak-expander` it
     embeds in **no** group with the Haagerup property (for example `F`, `T`, `V`, `nV`,
     and all SFT topological full groups).
2. **Proper cubulation without property A.** There is a finitely generated group `G_PW`,
   given by a recursive graphical `C'(1/24)` presentation, that has **solvable word
   problem**, acts properly on a CAT(0) cube complex (so it has the Haagerup property),
   and does **not** have property A (so it is not exact).

## Why it matters for Boone--Higman

Both groups are decidable inputs of `graphical-small-cancellation-inputs-satisfy-boone-higman`.
- **`G_exp`.** Boone--Higman for it would give a finitely presented simple group that is
  not coarsely embeddable into Hilbert space, a stronger conclusion than non-exactness.
  Every Haagerup host is excluded outright.
- **`G_PW`.** It is the natural test input for the exactness of Haagerup hosts such as `V`.
  An embedding `G_PW ≤ V` would make `V` non-exact. Nothing on main excludes such an
  embedding. The necessary condition is recorded in `every-cocf-group-is-exact`:
  `G_PW ≤ V` forces `G_PW` to have context-free co-word problem.
