---
rg: 2
id: fpbs-weak-topology-cost-lsc-envelope-is-group-cost
kind: claim
title: In the weak topology the lower semicontinuous envelope of cost is the constant group cost, so every weakly lower semicontinuous cost lower bound is at most C(Γ)
distinct_from:
  fpbs-kazhdan-local-cost-formula: that writes the Bernoulli cost as an infimum of window-local statistics, an upper-bound certificate; this proves that no weakly lower semicontinuous functional below cost can certify any lower bound above C(Γ) at any free action.
  fpbs-oblivious-certificates-never-localize: that kills base-oblivious graphing certificates for block localization; this kills weak-topology lower semicontinuous lower-bound functionals for the Bernoulli cost itself.
  burton-kechris-cost-usc-and-maximum-action: that imports upper semicontinuity; this derives the lower semicontinuous envelope and the resulting barrier.
---

**ESTABLISHED.** Let Γ be an infinite finitely generated group and (X,μ) standard non-atomic.
Give FR = FR(Γ,X,μ) the weak topology, and let s be a nontrivial Bernoulli shift of Γ,
realised on (X,μ).

1. **Envelope.** For every b ∈ FR, sup over weak neighbourhoods U of b of
   inf{C(c) : c ∈ U ∩ FR} equals C(Γ).
2. **Pointwise criterion.** Cost is lower semicontinuous at b ∈ FR iff C(b) = C(Γ).
3. **Tautology.** Γ has fixed price iff cost is lower semicontinuous at s, iff cost is
   continuous on FR. So "cost is weakly lower semicontinuous" is not a reduction of fixed price
   in any form: at s it *is* fixed price, and at any other point it is the same statement for that point.
4. **Barrier.** Let Ψ : FR → [−∞,∞] be lower semicontinuous at b, and Ψ ≤ C on the conjugacy
   class of a maximum action a_∞,Γ. Then Ψ(b) ≤ C(Γ). In particular, a functional that is
   lower semicontinuous at s and is a lower bound for cost cannot certify C(s) > C(Γ).
5. **Genericity.** {a ∈ FR : C(a) = C(Γ)} is a dense G_δ subset of FR.

**Class killed.** These are all lower bounds for cost of the form
C(a) ≥ sup_w F_w(finite statistics of a in window w), with each F_w continuous in the weak
topology. An example is a supremum, over finite partitions and finite windows, of a continuous
function of the partition statistics μ(γA_i ∩ A_j), γ in the window. Every such bound is weakly lower
semicontinuous, so by item 4 it is ≤ C(Γ) at every free action. It therefore cannot separate
C(s) from C(Γ), in either direction of use.
- For a fixed-price counterexample: it cannot certify C(s) > C(Γ).
- For `fpbs-free-action-cost-at-least-bernoulli-cost`: any such Ψ that is tight at s already
  forces C(s) = C(Γ), so it is equivalent to the target and not a reduction of it.

The invariant is the LSC envelope of cost. Every member dies at the same step: approximating
b by conjugates of a_∞,Γ, which all have cost C(Γ). For Kazhdan groups C(Γ) = 1
(`fpbs-kazhdan-groups-have-cost-one`), so the only lower bound such a functional can give is
the trivial bound 1.

**Where the nontrivial LSC statement lives.** It is on the space F̃R of weak-equivalence classes
(Abért–Elek topology). There singleton classes are closed, and cost is upper semicontinuous by
Burton–Kechris Theorem 10.13. `fpbs-bernoulli-lower-bound-from-weak-class-lsc-approximation`
splits the Bernoulli lower bound into two conditions at s̃ in that space.
