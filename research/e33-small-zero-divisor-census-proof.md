---
rg: 2
id: e33-small-zero-divisor-census-proof
kind: route
title: Exhaust bilinear support equations by SAT and reduce rational zero divisors modulo p
target: e33-balls-have-no-small-zero-divisors
requires: []
---

**Encoding** (`experiments/zero-divisor-tf/zd_sat.py`).
- **Balls.** Enumerated exactly with integer matrix products.
- **Over `F_2`.** Unknowns `x_a` for `a` in `A = B(2)` and `y_b` for `b` in
  `B = B(2)`, with `z_ab = x_a AND y_b`. Each product cell `g` gets the XOR
  constraint `XOR_{ab = g} z_ab = 0`, a singleton cell forces
  `NOT(x_a AND y_b)`, and the clauses `OR x_a` and `OR y_b` make both
  elements nonzero. There is no symmetry breaking. The solver is CryptoMiniSat
  with native XOR clauses.
- **Over `F_3`.** Each element has one-hot bits for coefficients 1 and 2.
  Each pair gives exclusive product bits `[prod = 1]` and `[prod = 2]`, and
  each cell runs a one-hot mod-3 counter that must end in state 0. The solver
  is CaDiCaL.
- **Checking models.** Every SAT model is recomputed independently with exact
  matrix products. The controls in the claim exercise this path.

Both instances at radius two are UNSAT: runs `e33-p2-r22.json` and
`e33-p3-r22.json`.

**Reduction from `Q`.** Suppose `alpha beta = 0` in `Q[H]` with `alpha` and
`beta` nonzero.
- Clear denominators and divide each element by the gcd of its integer
  coefficients. Both become primitive in `Z[H]`, and `alpha beta = 0` still
  holds.
- Reduction modulo `p` is a ring map `Z[H] -> F_p[H]`, so it gives nonzero
  elements with product zero whose supports lie inside the original ones.
- For a number field `K` with a prime `P` of residue field `F_p`, scale by a
  power of a uniformizer of the discrete valuation ring `O_(K,P)` instead,
  and reduce modulo `P`.

Radius-two supports over these rings would therefore give radius-two supports
over `F_2` or `F_3`, which the census excludes. QED
