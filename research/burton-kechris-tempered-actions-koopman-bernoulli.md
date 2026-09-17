---
rg: 2
id: burton-kechris-tempered-actions-koopman-bernoulli
kind: claim
title: An action is tempered when its reduced Koopman representation is weakly contained in the regular representation, and the Bernoulli Koopman representation is a multiple of the regular one
distinct_from:
  burton-kechris-weak-class-limits-are-ultraproducts: that imports the ultraproduct description of convergence of classes; this imports the definition of tempered actions and the identification of the Bernoulli Koopman representation.
---

**ESTABLISHED (import).** For a ∈ A(Γ,X,μ), κ^a(γ)f(x) = f(a(γ)^{−1}x) is the Koopman
representation and κ^a_0 its restriction to L²_0(X,μ). The action a is *tempered* if
κ^a_0 ≼ λ_Γ. Tempered actions are closed downward under ≼. For a nontrivial Bernoulli shift s_Γ of an infinite group, κ^{s_Γ}_0 ≅ ∞·λ_Γ.
For non-amenable Γ, i_Γ is not tempered, and there are free actions with s̃ ≼ ã that are not
tempered, e.g. a_∞,Γ.

**Source.** P. Burton, A. S. Kechris, *Weak containment of measure preserving group actions*,
arXiv:1611.07921v5. Read 2026-09-17 from the arXiv PDF, line breaks normalised.

- §4: "For each a ∈ A(Γ, X, µ), we let κa ∈ Rep(Γ, L2(X, µ)) be the corresponding Koopman
  representation, given by κa(γ)(f)(x) = f((γ−1)a(x)), and κa0 ∈ Rep(Γ, L2_0(X, µ)) its
  restriction to the orthogonal L2_0(X, µ) of the constant functions."
- §10.5: "An action a ∈ A(Γ, X, µ) is called tempered if κa0 ≼ λΓ (see [K4]). Recall that
  λΓ ≃ κsΓ0, so that this is equivalent to κa0 ≼ κsΓ0. (In fact, κsΓ0 ∼= ∞ · λΓ, see [KL,
  page 39])."
- §10.5: "Denote by TEMP(Γ, X, µ) the set of tempered actions. By Proposition 4.1 the set of
  tempered actions if closed downwards under ≼ and so in particular it is ≃-invariant."
- §10.5: "If Γ is not amenable, then iΓ is not tempered, so a~temp∞,Γ ≺ a~∞,Γ."

**Convention.** For unitary representations π, ρ, π ≼ ρ means that every function
γ ↦ ⟨π(γ)ξ,ξ⟩ is a limit, uniformly on finite subsets of Γ, of finite sums of functions
γ ↦ ⟨ρ(γ)η,η⟩. Since κ^{s}_0 ≅ ∞·λ_Γ, a single coefficient of κ^s_0 is a finite or convergent
sum of coefficients of λ_Γ. So a pointwise approximation of each ⟨κ^a_0(γ)ξ,ξ⟩ on finite sets by
single coefficients of κ^s_0 gives κ^a_0 ≼ λ_Γ.
