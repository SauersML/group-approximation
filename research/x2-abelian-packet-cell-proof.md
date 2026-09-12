---
rg: 2
id: x2-abelian-packet-cell-proof
kind: route
title: Joint functional calculus proves the abelian cell
target: x2-local-afd-holds-on-abelian-packets
requires: []
artifacts:
  - research/artifacts/x2-shadow-avoidance-recon-2026-08-31.md
---

`A` is a commutative von Neumann algebra, so `A ≅ L^∞(X, μ)` and the
`y_i` are essentially bounded functions.  Partition the joint
essential range: cover the compact
`K = {(y_1(x),…,y_j(x))} ⊂ ℂ^j` (essential range of the tuple) by
finitely many Borel cells `C_1,…,C_N` of diameter `< ε` and let
`χ_n = 1_{(y_1,…,y_j) ∈ C_n} ∈ A` — nonzero ones only.  Then
`B = span{χ_n}` is a finite-dimensional \*-subalgebra of `A ⊂ R` with
unit `1`, each `y_i` commutes with `B`, and choosing `λ_n^{(i)}` to be
the `i`-th coordinate of a point of `C_n`,

```text
‖y_i − Σ_n λ_n^{(i)} χ_n‖_∞ ≤ ε,
```

because on each cell the function's `i`-th coordinate deviates from
`λ_n^{(i)}` by at most the cell diameter — simple functions are
NORM-dense in `L^∞`, which is the one place quasidiagonality-type
approximation is free.  Since `E_B` is contractive and fixes `B`,
`‖y_i − E_B(y_i)‖ ≤ 2ε`.  With `s = 1` the commutator condition is
exact, giving local AFD at `(Y, 2ε)`.

Model checks: (i) `A` a masa of `R`, `y` = a Haar unitary: `B` = the
algebra of arcs of the circle — the classical statement that a single
unitary is quasidiagonal; (ii) the support-cut remark in the claim:
for `z` with `s ⊥ z^*z ∨ zz^*`, `zs = z(z^*z)s = 0` and
`sz = s(zz^*)z = 0` exactly, so `[z, s] = 0` — used verbatim in the
claim's second bullet; (iii) the argument never uses hyperfiniteness
of `R`, only commutativity of the packet — consistent with the cell
being elementary and rate-free.
