---
rg: 2
id: fpbs-cycle-tails-force-rank-gradient-equals-l2-betti
kind: claim
title: Zero Bernoulli cost excess, and so Bernoulli cycle-tail compactness, forces every Farber rank gradient and mod-p gradient to equal the first L2 Betti number
artifacts:
  - research/artifacts/fpbs/docs/cost-betti-rank-gradient-calibration-2026-09-17.md
distinct_from:
  fpbs-kazhdan-rankgradient-counterexample-reduction: that turns a positive-gradient chain in a Kazhdan group into a refutation of Fixed Price through cost one; this holds for every residually finite group, compares the gradient with beta_1 rather than zero, and refutes only the equality C(b)=1+beta_1, not Fixed Price
  fpbs-graphing-cost-betti-cycle-dimension-identity: that splits the cost of one graphing and shows compactness gives C=1+beta_1; this derives what C(b)=1+beta_1 forces on finite-index subgroups (generator growth, mod-p homology, torsion)
  fpbs-amen2-betti-cost-input: that is the one-sided inequality C>=1+beta_1 for free actions; this uses it with Abert-Weiss and Abert-Nikolov to pin down rank and mod-p gradients
---

Let Gamma be an infinite, finitely generated, residually finite group, with
Bernoulli action b and beta_1 = beta_1^(2)(Gamma).

**(0)** Suppose b satisfies the conclusion of
`fpbs-bernoulli-cycle-tail-compactness`: near-minimizing bounded-degree
graphings with lim_L limsup_n tau_L = 0. Then C(b) = 1 + beta_1.

Now assume only C(b) = 1 + beta_1.

**(i)** Every Farber chain (Gamma_n) has
RG(Gamma;(Gamma_n)) = lim (d(Gamma_n)-1)/[Gamma:Gamma_n] = beta_1.

**(ii)** Every Farber chain and every field K satisfy
limsup b_1(Gamma_n;K)/[Gamma:Gamma_n] <= beta_1. For every prime p and every
normal chain of p-power index with trivial intersection,
lim b_1(Gamma_n;F_p)/[Gamma:Gamma_n] = beta_1.

**(iii)** Suppose Gamma is finitely presented and the chain is normal with
trivial intersection. Then d(Gamma_n), b_1(Gamma_n;Q) and b_1(Gamma_n;F_p) for
every prime p, each divided by the index, all converge to beta_1. Also
d(tors H_1(Gamma_n;Z))/[Gamma:Gamma_n] -> 0.

**Contrapositive.** Let some infinite, finitely generated, residually finite
group have a Farber chain with RG > beta_1^(2). One sufficient certificate is
a normal p-chain with trivial intersection and mod-p gradient > beta_1^(2).
For finitely presented groups, another is linear growth of torsion rank along
a normal chain with trivial intersection. Such a group has C(b) > 1 + beta_1,
so it violates `fpbs-bernoulli-cycle-tail-compactness` and every other route
through zero excess. Fixed Price is not refuted.

**Calibration.** A proof of the compactness target, even restricted to finitely
presented residually finite groups, would give positive answers to
Ershov–Lück Questions 1.5, 1.10, 1.11 (p-chains) and 1.14 (K = F_p) for all
of them. The paper states that 1.14 "remains open if G is finitely presented
and K = F_p". The cycle-tails route is therefore at least as strong as those
open positive-characteristic approximation statements.

Derivation: Sections 2–4 of the artifact. Status records a written deduction
over imported published results, not independent validation.
