---
rg: 2
id: thompson-f-p21-cardinality-certificate-in-degree-eleven-proof
kind: route
title: A verified degree-eleven set with expansion below two and three halves, plus exact minimum cuts in degree ten
target: thompson-f-p21-cardinality-certificate-in-degree-eleven
requires:
  - thompson-f-nonamenable-iff-some-monomial-set-doubles
  - thompson-f-monomial-doubling-ratio-is-a-finite-computation
artifacts:
  - research/artifacts/thompson-f-monomial-doubling-2026-09-13.md
  - research/artifacts/thompson-f-monomial-doubling-2026-09-13-certificates/S21_11_13.txt.gz
  - research/artifacts/thompson-f-monomial-doubling-2026-09-13-certificates/X2_11_13.txt.gz
---

**Item 1.**
- *Certificate.* `S21_11_13.txt.gz` lists `160430` distinct normal forms of degree `11`, with
  letters `<= 13`. It is the source side of an optimal minimum cut from
  `experiments/thompson-f/doubling_flow.cpp` on `M_(11,13)`, and `13 = R_(S_(2,4))(11)`.
- *Two checks.* That program recounts `|S Y|` by direct image enumeration, and
  `experiments/thompson-f/doubling_verify_certificate.py` recounts it again, sharing no code.
  Both give `|S_(2,4) Y| = 318148`, and `318148 < 320860 = 2 · 160430`.
- *The solution.* Item 3 of `thompson-f-nonamenable-iff-some-monomial-set-doubles` gives
  nonzero `u, v ∈ K[Y]` with `a u = b v`. Every element of `Y` has degree `11`, so `u, v` are
  homogeneous of degree `11`.

**Item 2.**
- *The exact value.* By item 1 of `thompson-f-monomial-doubling-ratio-is-a-finite-computation`
  (`R_(S_(2,4))(10) = 12`), `Λ_(S_(2,4))(10)` is the optimum over `M_(10,12)` (`646646` words).
  Dinkelbach iteration ends with `148838/73690` and a zero-value minimum cut, which certifies
  optimality.
- *Lower degrees.* By item 2 of that claim, `Λ` is nonincreasing in `D`, so
  `Λ(D) >= Λ(10) > 2` for `D <= 10`.
- *All finite sets.* By item 3, a finite `Y` of mixed degrees with ratio `< 2` would have a
  single-degree part with ratio `< 2`.

**Item 3.**
- *Certificate.* `X2_11_13.txt.gz` lists `196488` distinct normal forms of degree `11`, with
  letters `<= 13`, `13 = R_A(11)`. Both programs give `|A Y'| = 293376`, and
  `2 · 293376 = 586752 < 589464 = 3 · 196488`.
- *A nonzero kernel.* For linear forms `l_0, l_1, l_2` in `x_0, x_1, x_2`, the map
  `K[Y']^3 -> K[A Y']^2`, `(u_0, u_1, u_2) -> (l_0 u_0 - l_1 u_1, l_1 u_1 - l_2 u_2)`, has domain
  dimension `3|Y'|` greater than target dimension `2|A Y'|`. So it has a nonzero kernel element.
- *All components nonzero.* If the common value `l_i u_i` were `0`, every `u_i` would be `0`
  because `K[F]` has no zero divisors. So the common value is nonzero, and then every `u_i` is
  nonzero.
- *Degree ten.* `Λ_A(10) = 111264/73690 > 3/2` on `M_(10,12)`, again with a zero-value cut, and
  monotonicity extends it to `D <= 10`.

**Reproduction.** `doubling_flow 11 13 "0,0;0,1;0,2;1,1;1,2"`, then
`doubling_flow 10 12 "0,0;0,1;0,2;1,1;1,2"`, `doubling_flow 11 13 "0;1;2"` and
`doubling_flow 10 12 "0;1;2"`. Each run took under three minutes on one MSI core.
