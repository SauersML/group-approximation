---
rg: 2
id: relative-furstenberg-zimmer-dichotomy
kind: claim
title: An extension of dynamical systems is relatively weakly mixing or has a non-trivial relatively compact intermediate extension
distinct_from:
  strict-pair-flip-lifts-are-relatively-weakly-mixing: that proves one specific extension of a Bernoulli base is relatively weakly mixing; this is the general relative Furstenberg-Zimmer dichotomy for every extension of every group action.
artifacts:
  - research/artifacts/fpbs-furstenberg-zimmer-cost-tower-2026-09-17.md
---

**ESTABLISHED (import).** Let Γ be a group, and let π: 𝒳 → 𝒴 be an extension of probability algebra Γ-dynamical systems. No ergodicity is assumed. Exactly one of the following holds.

(i) π is relatively weakly mixing. That is, every f ∈ L²(X) with E(f|Y)=0 has, for every ε>0, some γ with ‖⟨(T^γ)* f, f⟩_{L²(X|Y)}‖_{L²(Y)} < ε.

(ii) There are a system 𝒵 and extensions φ: 𝒳 → 𝒵 and ψ: 𝒵 → 𝒴, with ψ a non-trivial relatively compact extension. Relatively compact means L²(Z) is the L²-closure of the union of its Γ-invariant finitely generated L^∞(Y)-submodules.

In the proof, 𝒵 comes from a Γ-invariant subalgebra of L^∞(X) that receives a non-trivial factor inclusion of L^∞(Y). So for standard free actions of a countable group, 𝒵 is an intermediate factor Y_F given by an invariant sigma-algebra F with B_X strictly contained in F and F contained in B_Y.

Source: A. Jamneshan, *An uncountable Furstenberg–Zimmer structure theory*, arXiv:2103.17167v4, Theorem 1.2 = Theorem 6.2, Definition 6.1, Theorem 4.1. For systems of countable complexity the dichotomy is classical (Furstenberg, Zimmer). Verbatim text: [[relative-furstenberg-zimmer-dichotomy-citation]].
