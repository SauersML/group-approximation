---
rg: 2
id: harder-congruence-sln-z-euler-characteristic-vanishes
kind: claim
title: Every torsion-free congruence subgroup of SL_n(Z), n >= 3, has rational Euler characteristic zero (Harder's Gauss--Bonnet formula)
distinct_from:
  lee-szczarba-level-three-top-cohomology-is-steinberg: that computes one Betti number in the top degree; this is the vanishing of the alternating sum of all of them, from the vanishing of the Gauss--Bonnet--Chern form.
---

**ESTABLISHED by citation** (`harder-congruence-sln-z-euler-characteristic-vanishes-citation`).

Let `n >= 3`, `X = SL_n(R)/SO(n)`, and let `Γ <= SL_n(Z)` be a torsion-free congruence
subgroup. Then

```text
χ_h(Γ) := Σ_i (-1)^i dim_Q H^i(Γ; Q) = 0 .
```

**Reading.**
- `X` is contractible and `Γ` acts on it freely and properly, so `Γ\X` is a `K(Γ,1)`. Hence the
  source's `χ_h(Γ\X)` is `χ_h(Γ)` with trivial rational coefficients.
- The source states the vanishing as an equality of numbers, so it includes that every
  `H^i(Γ; Q)` is finite-dimensional and that almost all vanish.
- Where this node is used in the graph, finiteness and vanishing are also checked
  independently.
