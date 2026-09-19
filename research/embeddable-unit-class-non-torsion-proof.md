---
rg: 2
id: embeddable-unit-class-non-torsion-proof
kind: route
title: Lift the stable annihilation through the matrix ultrapower
target: embeddable-unit-class-non-torsion
requires: []
---

Suppose `n [1_D] = 0` in `K_0(D)` for some `n ≥ 1`.  Unitality pushes
this to `n [1_{B_ω}] = 0` in `K_0(B_ω)`.  Unwind the definition:
there are `k` and a projection `r ∈ M_k(B_ω)` with

```text
1^{⊕ n} ⊕ r  ~  r ⊕ 0^{⊕ n}     in  M_{k+n}(B_ω),
```

implemented by a partial isometry `v` with `v^*v` and `vv^*` the two
displayed projections.  Since `M_{k+n}(B_ω) = (M_{k+n}(B))_ω`,
represent `r` and `v` by bounded sequences; the relations
`r_i^2 − r_i`, `r_i^* − r_i`, `v_i^* v_i − (1^{⊕n} ⊕ r_i)`,
`v_i v_i^* − (r_i ⊕ 0)` tend to zero along the ultrafilter.  Standard
perturbation (functional calculus for the almost-projection `r_i`,
then polar decomposition of the compressed `v_i`) produces, for
ω-many `i`, honest projections `r̃_i` and partial isometries
implementing `1^{⊕ n} ⊕ r̃_i ~ r̃_i ⊕ 0` EXACTLY in `M_{k+n}(B)`.
Hence `n [1_B] = 0` in `K_0(B)`, contradicting the hypothesis.  So
`n [1_D] ≠ 0` for all `n ≥ 1`.
