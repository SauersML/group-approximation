---
rg: 2
id: relative-furstenberg-zimmer-dichotomy-citation
kind: route
title: Import Theorem 1.2 of Jamneshan on the relative weakly mixing versus compact dichotomy
target: relative-furstenberg-zimmer-dichotomy
requires: []
artifacts:
  - research/artifacts/fpbs-furstenberg-zimmer-cost-tower-2026-09-17.md
---

Citation import from A. Jamneshan, *An uncountable Furstenberg–Zimmer structure theory*, arXiv:2103.17167v4 [math.DS], 27 Sep 2025.

- **Theorem 1.2.** "Let 𝒳=(X,μ,T) and 𝒴=(Y,ν,S) be probability algebra Γ-dynamical systems and π:𝒳→𝒴 an extension. Exactly one of the following statements is true. (i) π:𝒳→𝒴 is a relatively weakly mixing extension. (ii) There exist an probability algebra Γ-dynamical system 𝒵=(Z,λ,R) and extensions ϕ:𝒳→𝒵 and ψ:𝒵→𝒴 such that ψ is a non-trivial relatively compact extension."
- **Definition 6.1.** "A function f∈L²(X) with E(f|Y)=0 is said to be relatively weakly mixing if for all ε>0 there exists γ∈Γ such that ‖⟨(T^γ)*f,f⟩_{L²(X|Y)}‖_{L²(Y)} < ε. Moreover, we say that 𝒳 is a relatively weakly mixing extension of 𝒴 if all f∈L²(X) with E(f|Y)=0 are relatively weakly mixing." (In the source's HTML rendering the "< ε" is cut off at the inequality sign.)
- **Theorem 4.1 (ii)'** and the definition following it. "The classical Hilbert space L²(X) is the L²-closure of the union of all its Γ-invariant and finitely generated L^∞(Y)-submodules." "A PrbAlg_Γ-morphism π fulfilling one (and therefore all) of the above six properties is called a relatively compact PrbAlg_Γ-extension."
- **Proof of Theorem 6.2**, construction of the intermediate system. "Let 𝒜={K∗_Y g∈L^∞(X): g∈L²(X)}. ... It is not difficult to check that 𝒜 is a Γ-invariant vector subspace of L^∞(X) closed under complex conjugation and multiplication. Thus 𝒜 has the structure of a CvNAlg^τ_{Γ^op}-system such that Φ:𝒜→L^∞(X,μ,T) and Ψ:L^∞(Y,ν,S)→𝒜 are CvNAlg^τ_{Γ^op}-factors with Ψ non-trivial."
- **Remark 5.6.** "If 𝒳 is a PrbAlg_Γ-system of countable complexity, then the length of the Furstenberg tower of 𝒳 must be a countable ordinal since L²(X) is separable."
- **Introduction.** "These results are well understood for systems of countable measure-theoretic complexity, see [18, 48, 49] for the original papers and [13, 19, 20, 37, 45] for some textbook expositions."

All sentences were read on 2026-09-17 from https://arxiv.org/html/2103.17167. Nothing is re-proved here. The only reading added is that Φ and Ψ are inclusions, which makes 𝒵 intermediate. That is how the recursion of Theorem 6.5 uses it.
