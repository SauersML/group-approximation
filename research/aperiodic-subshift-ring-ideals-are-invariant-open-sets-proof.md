---
rg: 2
id: aperiodic-subshift-ring-ideals-are-invariant-open-sets-proof
kind: route
title: Direct proof that ideals of an aperiodic subshift crossed product are ideals of invariant open sets
target: aperiodic-subshift-ring-ideals-are-invariant-open-sets
requires: []
artifacts:
  - research/artifacts/sk-open-1-subsystem-normal-subgroups-2026-09-13-part1.md
---

Put U = ⋃{V clopen : e_V ∈ J}. It is open, and invariant because u e_V u^{-1} = e_{TV}.

I_U ⊆ J:
- If supp f ⊆ U, compactness gives V_1, …, V_k with e_{V_i} ∈ J covering supp f.
- So f = e_{supp f}(1 − ∏_i (1 − e_{V_i})) ∈ J, and f u^j ∈ J.

J ⊆ I_U:
- Let r = Σ f_j u^j ∈ J and fix i. The element r u^{-i} ∈ J has 0-coefficient f_i.
- If f_i(x) = 1, then x is not periodic. So some clopen V ∋ x has f_i = 1 on V and V ∩ T^jV = ∅ for the finitely many nonzero exponents j of r u^{-i}.
- Since e_V (f u^j) e_V = f e_V e_{T^jV} u^j = 0 for j ≠ 0, we get e_V r u^{-i} e_V = e_V ∈ J. So x ∈ U.
- So every supp f_i ⊆ U, and r ∈ I_U.

Uniqueness: e_V ∈ I_U iff V ⊆ U, and clopen sets separate points.

R/I_U ≅ LC(Y,F_2) ⋊ Z: restriction of coefficients is a surjective ring homomorphism, since locally constant functions on Y extend to X, and its kernel is I_U. Full text: artifact, Lemma 1.
