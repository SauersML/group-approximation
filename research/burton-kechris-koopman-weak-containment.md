---
rg: 2
id: burton-kechris-koopman-weak-containment
kind: claim
title: Weak containment of measure preserving actions implies Zimmer weak containment of their reduced Koopman representations
distinct_from:
  burton-kechris-tempered-actions-koopman-bernoulli: that imports tempered actions, which use the downward consequence of this proposition for containment in the regular representation; this imports the proposition itself in its Zimmer (matrix-coefficient) form.
  cost-is-constant-on-weak-equivalence-classes: that imports monotonicity of cost under weak containment; this imports the representation-theoretic shadow of weak containment.
artifacts:
  - research/artifacts/fpbs-weakly-mixing-half-is-fixed-price-2026-09-17.md
---

**ESTABLISHED (import).** Let Γ be a countable group, and let a, b be p.m.p. actions of Γ on
standard non-atomic probability spaces. If a ≼ b, then κ^a_0 ≼_Z κ^b_0. That is, for all
v_1, ..., v_n in L²_0(X_a), ε > 0 and finite F ⊆ Γ, there are w_1, ..., w_n in L²_0(X_b) with
|⟨κ^a_0(γ)v_i, v_j⟩ − ⟨κ^b_0(γ)w_i, w_j⟩| < ε for all γ ∈ F and i, j ≤ n.

**Source.** P. Burton, A. S. Kechris, *Weak containment of measure preserving group actions*,
arXiv:1611.07921v5, read 2026-09-17 from the arXiv PDF. The text was machine-extracted, and
subscripts and superscripts are restored by hand.

- Definition 1.3: "Let π ∈ Rep(Γ, Hπ), ρ ∈ Rep(Γ, Hρ) be two unitary representations. We say that
  π is weakly contained in the sense of Zimmer in ρ, in symbols π ≼_Z ρ, if for any
  v1, ..., vn ∈ Hπ, ǫ > 0, F ⊆ Γ finite, there are w1, ..., wn ∈ Hρ such that
  |⟨π(γ)(vi), vj⟩ − ⟨ρ(γ)(wi), wj⟩| < ǫ, ∀γ ∈ F, i, j ≤ n."
- §4: "For each a ∈ A(Γ, X, µ), we let κ^a ∈ Rep(Γ, L²(X, µ)) be the corresponding Koopman
  representation, given by κ^a(γ)(f)(x) = f((γ⁻¹)^a(x)), and κ^a_0 ∈ Rep(Γ, L²_0(X, µ)) its
  restriction to the orthogonal L²_0(X, µ) of the constant functions. We have:"
- Proposition 4.1 ([K, page 67]): "a ≼ b =⇒ κ^a_0 ≼_Z κ^b_0 (=⇒ κ^a ≼_Z κ^b)".

Burton-Kechris state Section 4 for a, b in A(Γ, X, µ). Actions on other standard non-atomic spaces
reduce to this case by isomorphism, since weak containment and the Koopman representation are
isomorphism invariant. [K] is Kechris, *Global aspects of ergodic group actions*, and was not read
here.
