---
rg: 2
id: untwisted-point-evaluations-kill-k1-obstructions
kind: claim
title: Pullback plus untwisted point-evaluation maps kill every K1-null unitary in one step
distinct_from:
  homogeneous-tower-k1-failure-needs-twice-rank-dimension: that bounds block dimensions in a non-K1-injective tower; this shows the complement added by the connecting maps must be twisted, whatever the dimensions.
  bundle-endomorphism-unitaries-stable-range: that is the stable range lemma; this applies it after a one-step homotopy through constant unitaries.
artifacts:
  - research/artifacts/stw18-k1-route-constraint-map-2026-09-11.md
---

Let `X` be a connected finite CW complex of dimension `d`, `E` a rank-`r`
bundle over `X`, `B = Gamma(X, End E)`, `Y` a compact Hausdorff space,
`pi: Y -> X` continuous, and `x_1, ..., x_m in X` with chosen unitary
identifications `E_(x_l) ~= C^r`. Define the unital *-homomorphism

```text
psi : B -> Gamma(Y, End(pi^*E ⊕ theta^(m r))),
psi(a) = pi^*a ⊕ diag(a(x_1), ..., a(x_m)).
```

If `u in U(B)` has `[u] = 0` in `K_1(B)` and `d + 1 <= 2 r (m+1)`, then
`psi(u)` is null-homotopic.

Consequence: an inductive system of the LIX shape whose point-evaluation
summands are untwisted, with `m_j >= 1` and `d_j <= 4 r_j - 1`, has a
K1-injective limit. The LIX towers of the stw59 region (`d_j = 2 r_j`)
escape only because their point-evaluation summands are
`E_j(x_j) tensor L_(j+1)`, twisted by a line bundle over a new base factor.
