---
rg: 2
id: free-group-factor-elementary-equivalence-problem
kind: claim
title: Decide whether the free group factors L(F_m) and L(F_n) are elementarily equivalent for distinct m, n >= 2
artifacts:
  - research/artifacts/hl-free-group-factors-2026-09-13.md
distinct_from:
  free-group-factor-isomorphism-problem: that asks for isomorphism; elementary equivalence is weaker, and non-equivalence would refute isomorphism.
---

**OPEN.** Verbatim, Goldbring–Pi arXiv:2305.08168 (Question `foeequestion`):
"Is $L(\F_m) \equiv L(\F_n)$ for some (or all) distinct $m, n\geq 2$?"

Known structure: `free-group-factor-first-order-trichotomy` (Goldbring–Pi).

## Attempts

1. **Transfer from Sela's theorem.** Nonabelian free groups are elementarily
   equivalent (Sela, Tarski problem; as quoted by Goldbring–Pi). Transfer would
   need "elementarily equivalent ICC groups have elementarily equivalent group
   factors". J. Arulseelan claimed exactly this in arXiv:2412.20346v1
   (2024-12-29). **The paper is withdrawn:** v2 (2024-12-31) is a withdrawal
   notice with arXiv comment "Error in main theorem", verified on the arXiv abs
   page 2026-09-13. *Do not use.*
2. **Reducing the number of comparisons needed.**
   `independent-free-factor-equivalences-force-common-theory` (ESTABLISHED,
   elementary):
   - two elementary equivalences with log-independent compression constants,
     e.g. `L(F_2) = L(F_3)` and `L(F_2) = L(F_4)` in theory, already force case 1
     of the trichotomy;
   - one equivalence `L(F_m) = L(F_n)` gives the family
     `L(F_r) = L(F_{1+(r-1)lambda^k})` in theory, with `lambda = (n-1)/(m-1)`.

**Exact gap:** decide `L(F_2) = L(F_3)` in theory. Given that, one further
log-independent comparison closes the first-order question completely.
