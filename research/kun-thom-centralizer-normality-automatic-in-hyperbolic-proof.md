---
rg: 2
id: kun-thom-centralizer-normality-automatic-in-hyperbolic-proof
kind: route
title: Split on whether the Kazhdan subgroup is finite, and use finiteness on both sides
target: kun-thom-centralizer-normality-automatic-in-hyperbolic
requires:
  - hyperbolic-nonelementary-centralizer-finite
  - finite-infranormal-subgroup-is-normal
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
---

Let `G` be word-hyperbolic and let `Γ ≤ G` be infranormal with property (T),
so the compression semigroup `P_Γ = {g : gΓg^(-1) <= Γ}` generates `G`.

**Case `Γ` infinite.**  An infinite elementary subgroup of a hyperbolic group
is virtually cyclic, hence infinite amenable, hence does not have property (T)
(`bekka-valette-amenable-t-dichotomy`).  So `Γ` is non-elementary and
`K = C_G(Γ)` is finite by `hyperbolic-nonelementary-centralizer-finite`.  For
`g ∈ P_Γ`, centralizing reverses the inclusion `gΓg^(-1) <= Γ`:

```text
K = C_G(Γ) <= C_G(g Γ g^(-1)) = g K g^(-1),
```

so `g^(-1) ∈ P_K`, and `P_K = N_G(K)` by
`finite-infranormal-subgroup-is-normal`.  Hence every `g ∈ P_Γ` normalizes
`K`; the normalizer is a subgroup and `P_Γ` generates `G`, so `N_G(K) = G`.

**Case `Γ` finite.**  Then `Γ` itself is finite and infranormal, so `Γ ⊴ G`
by `finite-infranormal-subgroup-is-normal`, and the centralizer of a normal
subgroup is normal: for `g ∈ G`, `g C_G(Γ) g^(-1) = C_G(gΓg^(-1)) = C_G(Γ)`.

Either way `C_G(Γ) ⊴ G`, with no soficity hypothesis used.

Note what the two cases share: the conclusion comes from a *finite* group
being compressed, once the centralizer and once the subgroup.  That is why the
argument needs nothing about property (T) beyond ruling out the infinite
elementary case.
