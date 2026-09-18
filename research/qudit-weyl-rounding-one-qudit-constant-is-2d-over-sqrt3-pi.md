---
rg: 2
id: qudit-weyl-rounding-one-qudit-constant-is-2d-over-sqrt3-pi
kind: claim
title: On one prime qudit the Weyl stabilizer rounding constant is 2d/(sqrt3 pi) + O(1), via a commutator-Gram uncertainty inequality
artifacts:
  - experiments/qudit-weyl-rounding-multiqudit-2026-09-18/README.md
distinct_from:
  qudit-weyl-rounding-sharp-constant: that conjectured c_d = d/pi + O(1) on any number of qudits (refuted); this proves the one-qudit constant is 2d/(sqrt3 pi) + O(1), with the O(1) term in [-1, 4].
  qudit-weyl-rounding-constant-linear-upper-bound: that proves c_d <= 2/sin(pi/d) + 3, about 2d/pi, from a pair lemma; this proves the sharp one-qudit upper bound 2d/(sqrt3 pi) + 4 + O(1/d), from a trace-norm uncertainty inequality over all terms at once.
  qudit-weyl-rounding-constant-triangular-harper-bound: that is the matching lower bound 2d/(sqrt3 pi) - 1 from one explicit one-qudit sum; this is the upper bound.
---

**ESTABLISHED (ordinary proof, unreviewed, not Lean-verified; route
`qudit-weyl-rounding-one-qudit-constant-is-2d-over-sqrt3-pi-proof`).** Let `d >= 5` be prime. Let
`c_d^(1)` be the least `c` such that every Weyl sum `K = sum_j c_j g_j` on **one** qudit, with
weight `W = sum_j |c_j|` (identity terms excluded), has a stabilizer state `phi` with
`<phi|K|phi> >= lambda_max(K) - c (W - lambda_max(K))`. Put `A_d = 2/(sqrt3 sin(pi/d))`. Then

```text
c_d^(1)  <=  c*(d) := ( 3 + A_d + sqrt((3 + A_d)^2 + 4 A_d) ) / 2  <=  2d/(sqrt3 pi) + 4 + 1.21/d .
```

With the triangular Harper sum (`qudit-weyl-rounding-constant-triangular-harper-bound`, a one-qudit
instance), this gives the exact one-qudit asymptotics:

```text
2d/(sqrt3 pi) - 1 - o(1)  <=  c_d^(1)  <=  2d/(sqrt3 pi) + 4 + o(1).
```

So the leading coefficient on one qudit is `2/(sqrt3 pi) = 0.3676`. The triangle
`Z, X, e^(i pi/d) XZ` is the extremal configuration, and the square Harper sum is not. Values of
`c*(d)`: `5.33, 6.10, 7.64, 8.40, 15.17, 41.03` for `d = 5, 7, 11, 13, 31, 101`. The best previous
upper bound was `2/sin(pi/d) + 3`, which is `6.40, 7.61, 13.36` at `d = 5, 7, 31`.

**The new ingredient: a commutator-Gram uncertainty inequality.** Let `u_1, ..., u_k` be unitaries
with `u_i u_j = omega^(t_ij) u_j u_i`, where `omega = e^(2 pi i/d)`. Let `psi` be a unit vector,
`delta_i = 1 - Re<psi|u_i|psi>` and `w >= 0`, and put `D = diag(sqrt w)`. Then

```text
sum_i w_i delta_i  >=  ||D C D||_1 / 4,       C_ij = <psi|[u_i^*, u_j]|psi> = (1 - omega^(t_ij)) <psi|u_i^* u_j|psi>.
```

`C` is Hermitian with zero diagonal. It is the difference of the two Gram matrices of
`(u_i - 1)psi` and of `(u_i^* - 1)psi` (the second one transposed), and both have trace
`2 sum delta_i`. Because `tr C = 0`, this implies the Frobenius form
`sum_i delta_i >= ( sum_(i<j) sin^2(pi t_ij/d) |<u_i^* u_j>|^2 )^(1/2)`. Both are equalities to leading
order for the Harper pair (`pi/d`) and the triangle (`sqrt3 pi/d`).

**The rounding.** Pick a line `l` of `F_d^2` at random and measure `psi` in its stabilizer basis. The
line probabilities are `lambda_l >= x_l = max_(j on l) (1 - c delta_j/(1 - delta_j))_+`, which is
possible iff `sum_l x_l <= 1`. If `sum_l x_l > 1`, the representatives lie on `k >= 2` distinct lines
and have `sum delta < (k-1)/c`. The Frobenius form contradicts this for `c >= c*(d)`. The case
`k = 3` is the triangle, and it is exactly tight to leading order. For `k >= 4`, the step uses that for
`d >= 5` no four directions of `F_d^2` have all pairwise symplectic products `+-1`. So the `+-1`
graph is `K_4`-free, and Turán's theorem applies.

**Scope.** This is one qudit only. For `n >= 2` qudits the same inequality reduces the matching upper
bound to a pure matrix inequality (`hermitian-edge-trace-norm-vs-independence`), and the rounding
step is `qudit-weyl-rounding-constant-2d-over-sqrt3-pi-via-trace-norm`. `d = 3` is excluded, because
`2 = -1 mod 3` lets all four lines be pairwise `+-1`; that is the antiparity example.
