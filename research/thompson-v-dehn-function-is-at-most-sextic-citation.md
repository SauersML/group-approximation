---
rg: 2
id: thompson-v-dehn-function-is-at-most-sextic-citation
kind: route
title: Import Lorrain's theorem that the Dehn function of Thompson's group V is at most n^6
target: thompson-v-dehn-function-is-at-most-sextic
requires: []
---

Citation import, not a reproof.

A. Lorrain, "The Dehn function of Thompson's group V is at most sextic",
arXiv:2608.03813 (v1 4 Aug 2026, v2 5 Aug 2026; 70 pages). Read from the arXiv
v2 PDF on 2026-09-13.

- p. 65, verbatim: "Theorem 5.7. The Dehn function of Thompson's group V is at
  most of order O(n⁶)."
- The presentation is the finite presentation of V in §1.1 (generators
  `x_0, x_1, c_1, π_0`, with `x_n`, `c_n`, `π_n` defined by conjugation in
  equation (1)), following Guba 2000 and Cannon–Floyd–Parry.
- Structure, as read on pp. 60–65:
  - Theorem 5.5, quoted from Guba 2000 (Theorem 3): every word `w` of length
    `n` in V equals `p π c_(n+1)^m q^(-1)` with monotone positive words `p, q`
    in F of complexity at most `n`, an irreducible π-word `π` of rank at most
    `n`, and `0 ≤ m ≤ n+2`.
  - Theorem 5.6: the area of that rewriting is `O(n^6)`. The proof inducts on
    length by cutting `w` into halves and filling ten regions; the p. 65 tally
    is "3O(n²) + O(n³) + 2O(n⁴) + O(n⁵) + 4O(n⁶) = O(n⁶)".
  - Theorem 5.7: for `w = 1` the form collapses to `p q^(-1)` with `m = 0`,
    `π = 1`, and Guba 2006 (Theorem 1) fills `p q^(-1)` quadratically.

This route asserts only that the cited theorem says what the claim records.
The preprint is unrefereed.
