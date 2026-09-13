---
rg: 2
id: sl3z-cocompact-wc-iff-weak-limit-of-congruence-quotients
kind: claim
title: SL3(Z) on SL3(R)/Λ is weakly contained in finite actions iff SL3(R) on SL3(R)/Λ is weakly contained in the SL3(R)-actions on SL3(R)/Γ' for finite-index Γ' of SL3(Z)
distinct_from:
  sl3z-cocompact-quotient-not-weakly-contained-in-finite-actions: that is the open exclusion for the discrete group acting; this proves it equivalent to a statement about the simple Lie group acting on homogeneous spaces, with no finite sets
  sl3-split-class-lattice-quotient-actions-are-sofic: that gives soficity inside the commensurability class through duality; this compares a lattice outside the class with the congruence quotients of the class through induction and restriction
---

**ESTABLISHED (unreviewed).** Let `G = SL_3(R)`, `Γ = SL_3(Z)`, and let `Λ <= G` be any lattice. Weak containment
of measure-preserving actions of a locally compact second countable group is Kechris' notion, with
statistics required uniformly for `g` in compact sets. A *mixture* of a family means a countable disjoint
union of members with probability weights. The following are equivalent.

1. `Γ ↷ (G/Λ, Haar)` is weakly contained in mixtures of finite `Γ`-actions.
2. `G ↷ (G/Λ, Haar)` is weakly contained in mixtures of the actions `G ↷ (G/Γ', Haar)`, where `Γ'` ranges
   over the finite-index subgroups of `Γ`.

By the congruence subgroup property (Bass--Milnor--Serre, recalled in
`bms-sln-z-representations-agree-with-algebraic-ones`), form 2 may use the principal congruence subgroups
`Γ(N)` only. **So the exclusion problem is: is a compact quotient of `SL_3(R)` a weak limit of the
congruence quotients of `SL_3(Z)`?**

**Consequences.**
* *Independence of the acting lattice.* Form 2 depends only on the commensurability class of `Γ` up to
  conjugation. Finite-index subgroups of `Γ_1 ∩ Γ_2` are cofinal for both, and `G/aΓ'a^(−1) ≅ G/Γ'`. So for
  every lattice `Γ_1` commensurable with a conjugate of `SL_3(Z)`, `Γ_1 ↷ G/Λ` is weakly contained in finite
  actions iff `SL_3(Z) ↷ G/Λ` is.
* *Spectral shadow.* Form 2 forces `L^2(G/Λ)` to be weakly contained in `⊕_N L^2(G/Γ(N))`. For `Λ` from a cubic
  division algebra this holds by Jacquet--Langlands (recalled, not imported). So form 2 asks for the
  non-spectral remainder of a transfer the automorphic side already provides.
* *Calibration.* If `Λ` is commensurable with `aΓa^(−1)`, form 2 is immediate: `Γ'' = Λ ∩ aΓa^(−1)` has finite
  index in `Λ`, `G/Γ'' → G/Λ` is a factor map, and `G/Γ'' ≅ G/a^(−1)Γ''a` with `a^(−1)Γ''a <= Γ` of finite index.
  The Hecke models of `sl3z-lattice-space-action-is-sofic` are thus recovered by induction and restriction.

Proof in `sl3z-cocompact-wc-iff-weak-limit-of-congruence-quotients-proof`.
