---
rg: 2
id: burton-kechris-maximum-action-weakly-mixing-without-t
kind: claim
title: For a countable group without property (T) the maximum weak-containment class is realized by a weakly mixing action
distinct_from:
  burton-kechris-cost-usc-and-maximum-action: that imports the existence of the maximum a_inf and the upward closure of freeness; this imports that without (T) the maximum can be realized by a weakly mixing action, and that with (T) it is not ergodic.
  burton-kechris-tempered-actions-koopman-bernoulli: that imports tempered actions and the Bernoulli Koopman representation; this imports the ergodic-theoretic dichotomy of a_inf across property (T).
artifacts:
  - research/artifacts/fpbs-weakly-mixing-half-is-fixed-price-2026-09-17.md
---

**ESTABLISHED (import).** Let Γ be a countable group and (X, μ) standard non-atomic.

1. (Burton-Kechris Theorem 3.20) Γ has property (T) iff a_∞,Γ is not ergodic.
2. (Proof of Theorem 3.20, using Kerr-Pichot) If Γ does not have property (T), then the weakly
   mixing actions are dense in A(Γ, X, μ). So a_∞,Γ can be realized, up to weak equivalence, as
   a product of a countable sequence of weakly mixing actions, and that product is weakly mixing.

Here an action is weakly mixing when its reduced Koopman representation κ_0 has no nonzero
finite-dimensional subrepresentation. a_∞,Γ is determined only up to weak equivalence, so
"realized" means that some weakly mixing action is weakly equivalent to it.

**Source.** P. Burton, A. S. Kechris, *Weak containment of measure preserving group actions*,
arXiv:1611.07921v5, read 2026-09-17 from the arXiv PDF. The text was machine-extracted, and
ligatures and line breaks are normalised.

- Theorem 3.20: "A group Γ has property (T) iff a∞,Γ is not ergodic."
- The paragraph after it: "One direction follows from the fact that for property (T) groups we
  have SERG(Γ, X, µ) = ERG(Γ, X, µ) and a∞,Γ cannot be strongly ergodic. For the other direction,
  note that if Γ does not have property (T), then the weak mixing actions are dense in
  A(Γ, X, µ) (Kerr-Pichot [KP]; see also [K, Theorem 12.9]), so a∞,Γ can be realized as a product
  of a countable sequence of weak mixing actions, which is therefore weakly mixing, thus ergodic."
- §1: "Recall that a weak mixing representation is one that has no non-0 finite-dimensional
  subrepresentations."
- Reference: "[KP] D. Kerr and M. Pichot, Asymptotic abelianess, weak mixing, and property T"
  (J. Reine Angew. Math. 623 (2008), 213-235).

**Corroboration (secondary).** M. Brannan, D. Kerr, *Quantum groups, property (T), and weak
mixing*, arXiv:1706.00554, Introduction: "Using the fact that weak mixing is preserved under tensor
products with arbitrary representations, Kerr and Pichot applied the Bekka–Valette theorem to show
that if a second countable locally compact group does not have property (T) then within the set
of all unitary representations of the group on a fixed separable infinite-dimensional Hilbert
space the weakly mixing ones form a dense Gδ in the weak topology [20] ... By a similar principle
requiring a more subtle implementation, Kerr and Pichot also established an analogous conclusion
for the measure-preserving actions of the group on a fixed standard atomless probability space."

The Kerr-Pichot paper itself was not read. [K] is Kechris, *Global aspects of ergodic group
actions*, and was not read here either.
