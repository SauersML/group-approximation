---
rg: 2
id: raag-virtual-fn-kernel-conjecture-via-simple-connectivity
kind: route
title: Zaremsky's conjecture 1.19 for all n from the homological theorem plus simple connectivity of L, by Hurewicz and Bestvina--Brady
target: raag-virtual-fn-kernel-implies-raag-fn-kernel
requires:
  - raag-virtual-fp-n-kernel-forces-acyclic-flag-complex
  - raag-virtual-fp-kernel-forces-simply-connected-flag-complex
---

Let `H ≤ A_L` have finite index and let `ψ: H → Z` be onto with kernel of type `F_n`.

- `n = 1`: `raag-virtual-fg-kernel-implies-fg-kernel` (proved without the second requirement).
- `n ≥ 2`: the kernel is finitely presented and of type `FP_n(Z)`. The second requirement makes
  `L` simply connected; the first makes `H̃_j(L; Z) = 0` for `j ≤ n − 1`. By the Hurewicz theorem
  `L` is `(n−1)`-connected. By the Bestvina--Brady theorem (Invent. Math. 129 (1997): `BB_L` is of
  type `F_n` iff `L` is `(n−1)`-connected; statement recalled and to be imported with a verified
  citation), `A_L → Z`, `v ↦ 1`, has kernel of type `F_n`.

This route is an implication only: its target stays open while
`raag-virtual-fp-kernel-forces-simply-connected-flag-complex` is open.
