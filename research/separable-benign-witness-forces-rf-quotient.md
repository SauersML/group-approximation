---
rg: 2
id: separable-benign-witness-forces-rf-quotient
kind: claim
title: "A benign witness whose Sigma is profinitely closed forces K/N to be residually finite; so N_U has no separable witness, and type F witnesses in LERF hosts, products of limit groups, retracts and kernels are dead"
distinct_from:
  two-occurrence-realizability-is-type-f-benignness: That proves the equivalences, closure properties and the halting-subgroup base case of type F benignness; this is an obstruction theorem that kills every witness (Λ, Σ) with Σ closed in the profinite topology of Λ, for every relation subgroup with non-residually-finite quotient.
  benign-witness-finite-quotients-refine-the-fold: That asks whether finite quotients of a chosen witness refine the fold on the double when F/N is residually finite; this proves that for F/N NOT residually finite no witness can have Σ closed at all, and uses it to rule out whole host classes for type F benignness.
  mikhailova-fiber-product-gives-regular-mf-benign-compiler: That builds finitely generated benign witnesses inside products of free groups; this shows those witnesses can never be upgraded to type FP_k inside a product of k limit groups when F/N is not residually finite, so the compiler is sharp at finite generation.
---

**ESTABLISHED (proposed, 2026-09-18; referee welcome; items 3(c) and 4 cite
Wilton and Bridson--Howie--Miller--Short).** Benign and `F_m`-benign are as in
`two-occurrence-realizability-is-type-f-benignness`: a witness for `N ≤ K`
is a pair `(Λ, Σ)` with `K ≤ Λ`, `Σ ≤ Λ` and `Σ ∩ K = N`. Call the witness
**separable** if `Σ` is closed in the profinite topology of `Λ`.

1. **Separable witnesses see only closed subgroups.** If `(Λ, Σ)` is a
   separable witness for `N ≤ K`, then `N` is closed in the profinite topology
   of `K`. For `N ⊴ K` this means `K/N` is residually finite. No finiteness
   hypothesis on `Λ` or `Σ` is needed.
2. **The root needs non-separable witnesses.** Let `P = F/N_P` be any finitely
   presented group that is not residually finite (for example `BS(2,3)`, or
   Higman's universal group `U`, which contains `BS(2,3)`). Then no witness for
   `N_P ≤ F`, of any finiteness type, is separable. So a proof of
   `every-re-normal-subgroup-of-a-free-group-is-type-f-benign` (even at level
   `F_2`) must produce a type `F` subgroup `Σ` that is not profinitely closed
   in its type `F` host.
3. **Host classes that are dead.** For `F/N` not residually finite, `N` has no
   witness `(Λ, Σ)` of the following kinds.
   - (a) `Λ` LERF and `Σ` finitely generated. This covers free groups, surface
     groups, limit groups (Wilton), free products of LERF groups, and
     fundamental groups of closed hyperbolic 3-manifolds (Agol). Hence no
     type `F` witness lives in such a host.
   - (b) `Λ` residually finite and `Σ` a virtual retract of `Λ`. This covers
     quasiconvex `Σ` in a virtually compact special hyperbolic `Λ`
     (Haglund--Wise), and every `Σ` that is a free factor or direct factor of a
     finite-index subgroup of a residually finite `Λ`.
   - (c) `Λ = L_1 × ... × L_k` a product of `k` limit groups (for example free
     groups) and `Σ` of type `FP_k(Q)`. In particular no type `F` witness lives
     in any finite product of limit groups.
   - (d) `Σ ⊴ Λ` with `Λ/Σ` residually finite. This covers the Bestvina--Brady
     kernels `BB_L = ker(A_L -> Z)` and every kernel of a character of a
     residually finite group, e.g. Kropholler-type kernels in residually
     finite hyperbolic or special groups.

   So the Bestvina--Brady / Kropholler replacements for the classical join
   witness, and every witness inside a product of free groups, cannot work for
   `N_U`. The exact failing step: their `Σ` is closed, and closedness passes to
   `Σ ∩ F = N_U`, whose quotient `U` is not residually finite.
4. **Sharpness in products of free groups.** Classical (finitely generated)
   witnesses inside products of free groups exist for every r.e. `N`
   (`mikhailova-fiber-product-gives-regular-mf-benign-compiler`). By item
   3(c), inside `F_r × F_s` a witness `Σ` with `F/N` not residually finite is
   finitely generated but never finitely presented. So the benign problem at
   level `F_2` cannot be solved in products of two free groups, and at type `F`
   in no product of limit groups.
5. **What survives.** The type `F` base case (the halting subgroup
   `Σ = <t, r_1, ..., r_n>` in the Boone tower `G'_M`,
   `two-occurrence-realizability-is-type-f-benignness` item 5) is consistent
   with item 1: when the halting set is not recursive, `Σ` is a free,
   non-separable subgroup of a non-LERF type `F` group. Any solution of the
   root must be of this non-separable, "machine" kind. Profinite, residual,
   and LERF-type constructions are ruled out as a class.

Proof: route `separable-benign-witness-forces-rf-quotient-proof`.
