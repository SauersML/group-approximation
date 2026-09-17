---
rg: 2
id: fpbs-bernoulli-lower-bound-from-weak-class-lsc-approximation
kind: route
title: Approximate the Bernoulli class by cheap classes and pass cost to the limit by lower semicontinuity at s̃
target: fpbs-free-action-cost-at-least-bernoulli-cost
requires:
  - fpbs-bernoulli-weak-class-cost-lsc
  - fpbs-bernoulli-weak-class-cheap-approximability
  - burton-kechris-cost-usc-and-maximum-action
  - abert-weiss-free-actions-weakly-contain-bernoulli
  - cost-is-constant-on-weak-equivalence-classes
---

Let Γ be infinite and finitely generated, a free, and b a nontrivial Bernoulli shift. For each
n, `fpbs-bernoulli-weak-class-cheap-approximability` gives a free a_n with C(a_n) < C(Γ) + 1/n,
and ã_n within 1/n of s̃ in a compatible metric on F̃R. So ã_n → s̃. Then
`fpbs-bernoulli-weak-class-cost-lsc` gives C(s) ≤ liminf C(a_n) ≤ C(Γ). By the imported
display C(a) ≥ C(a_∞,Γ) = C(Γ), we get C(a) ≥ C(s).

Finally b and s are free, and each weakly contains the other by Abért–Weiss. So
C(b) = C(s) by `cost-is-constant-on-weak-equivalence-classes`.

**Decomposition, not a relabelling.** Both premises are also necessary. If C(a) ≥ C(b) for
all free a, then cost is constant on FR, and both premises hold trivially. So the Bernoulli
lower bound is equivalent to their conjunction. The two premises are conditions of different
kinds at the same point s̃: a limit inequality and an approximation property. Neither is
known to imply the other.

A finitely generated fixed-price counterexample must therefore show a cost jump at s̃ (premise
1 fails), or an F̃R-neighbourhood of s̃ with cost bounded away from C(Γ) (premise 2 fails).

The weak-topology versions of both premises are settled by
`fpbs-weak-topology-cost-lsc-envelope-is-group-cost`. There, approximability holds everywhere,
and lower semicontinuity at s is the whole problem. So passing to the class space is exactly
what makes the split nontrivial.
