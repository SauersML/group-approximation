---
rg: 2
id: level-synchronous-first-mismatch-centralizer-proof
kind: route
title: Normalize one column per level and count its exponentially many centralizer cosets
target: level-synchronous-first-mismatch-area-is-centralizer-impossible
requires:
  - finite-mark-centralizer-commutator-area-is-proper
---

At level `n`, freeze `b_n` and conjugate the whole proposed column by
`D_(j b_n)^(-1)`.  This sends its marked involution to the fixed word `h`,
preserves the area of every commutator, and sends all `2^n` row words into
`C_G(h)`.

The row coefficients are distinct dual-prefix monomials.  The elementary
matrix quotient separates their `x_12` roots from each other and from both
elements of `<h>`, which lies in the `x_23` root subgroup.  Thus the level
supplies `2^n` distinct cosets in `C_G(h)/<h>`.

Properness of commutator filling area on this quotient makes the number of
cosets with area at most a fixed `A` finite.  Letting `n` grow contradicts
the proposed uniform bound and proves the claim.
