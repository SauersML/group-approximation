---
rg: 2
id: reduced-projection-iff-gapped-spectral-measure
kind: claim
title: A reduced group C*-algebra has a nontrivial projection iff some self-adjoint element of Z[i][G] has a gapped spectral measure
distinct_from:
  rank-one-lattice-kadison-kaplansky-and-charzero-idempotents: that proves absence of projections for one class of torsion-free groups; this is an exact spectral reformulation of the presence of projections, valid for every group.
---

**ESTABLISHED.** Let `G` be a countable group, `tau` the canonical faithful
trace on `C*_r(G)`, and for self-adjoint `a` let `mu_a` be its spectral
measure, `tau(f(a)) = int f d mu_a`. The following are equivalent.

1. `C*_r(G)` contains a projection other than `0` and `1`.
2. Some self-adjoint `a` in `Z[i][G]` has disconnected spectrum in `C*_r(G)`.
3. Some self-adjoint `a` in `Z[i][G]` has a spectral measure `mu_a` whose
   support is not an interval.

**Supplements.**
- `supp mu_a = spec(a)` for every self-adjoint `a` in `C*_r(G)`.
- A splitting `spec(a) = K_1 ⊔ K_2` into nonempty closed pieces gives the
  projection `chi_(K_1)(a)` in `C*_r(G)`, whose trace `mu_a(K_1)` lies strictly
  between `0` and `1`.
- The spectrum of `a` in `C*_r(G)` equals its spectrum in `C*_r(H)` for any
  subgroup `H` containing the support of `a`. So a witness always lives on a
  finitely generated subgroup.

So the Kadison--Kaplansky conjecture (`kadison-kaplansky-torsion-free`) says:
for every finitely generated torsion-free `G`, every self-adjoint element of
`Z[i][G]` has an interval as the support of its spectral measure.

Derivation: `reduced-projection-iff-gapped-spectral-measure-proof`.
