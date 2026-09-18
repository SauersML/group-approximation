---
rg: 2
id: burton-kechris-weak-class-limits-are-ultraproducts
kind: claim
title: A sequence of weak-equivalence classes converges to ã exactly when every non-principal ultraproduct of the actions is weakly equivalent to a
distinct_from:
  burton-kechris-cost-usc-and-maximum-action: that imports upper semicontinuity of cost on the space of classes and the maximum action; this imports the description of convergent sequences in that space by ultraproducts (Carderi's theorem).
  cgdls-ultraproduct-cost-equals-combinatorial-cost: that imports the cost of an ultraproduct; this imports which weak-equivalence class the ultraproduct has.
---

**ESTABLISHED (import).** Let Γ be a countable group and (X,μ) standard non-atomic. Give
Ã(Γ,X,μ) the Abért–Elek topology, in which ã_n → ã iff C_{n,k}(a_n) → C_{n,k}(a) in the
Hausdorff metric for every n,k. Here C_{n,k}(a) ⊂ [0,1]^{n×k×k} is the closure of the set of
matrices (μ(γ_l^a(A_i) ∩ A_j))_{l<n, i,j<k} over Borel partitions (A_0,…,A_{k−1}). Then
ã_n → ã iff ∏_n a_n/U ≃ a for every non-principal ultrafilter U on N.

**Source.** P. Burton, A. S. Kechris, *Weak containment of measure preserving group actions*,
arXiv:1611.07921v5 (April 17, 2019). Read 2026-09-17 from the arXiv PDF, line breaks normalised.
- §2.2 (1): "Let Γ = {γ0, γ1, . . .} be an enumeration of Γ. Let a ∈ A(Γ, X, µ) and let
  Ā = {A0, A1, . . . , Ak−1} be a partition of X into k > 1 Borel pieces. For each n > 1, let
  M^Ā_{n,k}(a) ∈ [0, 1]^{n×k×k} be the point whose value at (l, i, j), where l < n, i, j < k,
  is equal to µ(γ^a_l(Ai) ∩ Aj). Then let Cn,k(a) be the closure of the set
  {M^Ā_{n,k}(a) : Ā is a Borel partition of X}. Then we have a ≼ b ⇐⇒ ∀n, k(Cn,k(a) ⊆
  Cn,k(b)) and a ≃ b ⇐⇒ ∀n, k(Cn,k(a) = Cn,k(b))."
- §10.1: "the map ã ↦ (Cn,k(a))n,k ∈ ∏n,k H([0, 1]^{n×k×k}) is a bijection of Ã(Γ, X, µ)
  with a subset of this product space and we define the topology of Ã(Γ, X, µ) by
  transferring the relative topology of this subset back to Ã(Γ, X, µ) by this bijection."
- Theorem 10.2: "([C, Theorem 2.22]). Let ãn, ã ∈ Ã(Γ, X, µ), n ∈ N, and let U be a
  non-proncipal ultrafilter on N. If lim n→U ãn = ã, then a ≃ ∏n an/U. In particular the
  following are equivalent: (i) ãn → ã. (ii) ∏n an/U ≃ a, for every non-principal ultrafilter
  U on N."
- §3.7: "Here ∏n an/U is the ultrapoduct of the actions an by U, see, e.g., [CKT-D, Section 4]."

The ultraproduct here is the Loeb-space construction of Conley–Kechris–Tucker-Drob. Carderi–
Gaboriau–de la Salle use the same construction ("The construction of ultraproducts of
probability spaces is due to Loeb, see [CKTD13] or [Car15]"), so the ultraproduct action a_u of
`cgdls-ultraproduct-cost-equals-combinatorial-cost` is ∏_n a_n/u.
