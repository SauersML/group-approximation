---
rg: 2
id: fpbs-mal-sprinkle-then-absorb-inert
kind: claim
title: After a sparse block sprinkle of the new generator at a malnormal free stage, every bounded-crossing infinite-contact absorption step is inert, so pay-then-absorb chains never reach the next stage
distinct_from:
  fpbs-malnormal-measured-absorption-cap: that caps absorption chains that start inside a subgroup orbit relation, and lists as not excluded exactly the chains that first pay a finite-contact step and then absorb; this treats that case, starting from E_H v Theta_B, which is not a subgroup relation, through the fineness of the random cluster graph rather than Q(Lambda).
  fpbs-mal-stage-block-sprinkling-threshold: that shows a sparse block sprinkle alone does not generate the next stage (first moment on detours); this shows that no later zero-cost absorption step with bounded closed-edge crossings adds anything to the sprinkled relation, and it uses the ESTABLISHED linear-perimeter count instead of the OPEN circuit lemma.
  fpbs-malnormal-subgroup-relations-finite-contacts: that counts graphing edges between two subgroup classes; this counts cycles in the cluster graph of a sprinkled relation, where each cluster is an infinite union of subgroup classes.
  fpbs-infinite-contact-zero-relative-cost: that is the positive relC = 0 criterion from connected infinite contacts; this shows the contacts created by a sparse block sprinkle never connect distinct clusters through bounded-crossing maps.
  fpbs-malnormal-coset-cycles-linear-perimeter: that is the deterministic cycle count M(k) <= A^k and a floor for packing certificates; this imports it to get almost-sure fineness of the random cluster graph and a statement about all bounded-crossing partial isomorphisms.
artifacts:
  - research/artifacts/fpbs-mal-sprinkle-then-absorb-inert-2026-09-17.md
---

**Setting.**
- `F` is free, `H <= F` is finitely generated and malnormal, `t in F \ H`,
  and `F = <H, t>`. `A = A(F, H, t)` is the constant of
  [[fpbs-malnormal-coset-cycles-linear-perimeter]] item 2.
- `Gamma ⊇ F` is countable, with `F` malnormal in `Gamma`. `a` is the
  Bernoulli shift of `Gamma` over a base that is not a point mass.
- `W ⊆ Gamma` is finite and nonempty, `B` is measurable with respect to `x|_W`,
  `epsilon = mu(B)` and `q = epsilon^{1/|W|^2}`.
- `S_1 = E_H v Theta_B`, where `Theta_B = {(y, t^{-1} y) : y in B}`.

Every `Gamma_mal` stage pair `H_n < H_{n+1}`, with `t = b_{n+1}^{-1}`, is an
instance: `H_{n+1}` is malnormal in `Gamma_mal`.

For `phi in [[E_a]]` whose label `gamma(y)` lies in `F`, `kappa(y)` is the
least number of crossings of closed potential edges (those `<z>` with
`z ∉ B`) along the class-graph walk of a syllable word
`h_0 t^{±1} h_1 ... t^{±1} h_j` for `gamma(y)`. In particular
`kappa <= ell_H(gamma)`.

1. **Inert absorption.** Assume `A q < 1`. Let `phi in [[E_a]]`, and suppose
   that for a.e. `x in D_phi(S_1)` the `S_phi`-class of `x` contains
   infinitely many `y` with `kappa(y) <= K(x) < infinity`. This holds, for
   example, if `ell_H(gamma) <= k` on the `F`-labelled part of `dom phi`.
   Then `(x, phi x) in S_1` for a.e. `x in D_phi(S_1)`. So every transfinite
   chain of such infinite-contact steps starting at `S_1` is constant.
2. **Properness.** If `q <= 1/(4 A^2)`, then
   `mu{x : (x, t^{-1} x) in S_1} <= epsilon + 1/3 < 1/2`, so the closure in
   item 1 is not `E_F`.
3. **Reductions.** The same holds for:
   - finitely many sprinkles with labels in `H t^{±1} H`;
   - sprinkles interleaved with absorption steps.

   In both cases the threshold is taken for the union window and the summed
   measure.

**The invariant and the step.**
- **Invariant.** Almost-sure Bowditch fineness of the cluster graph. Its
  vertices are the `S_1`-classes and its edges are the unsprinkled potential
  edges. Fineness follows from `M(k) <= A^k` by a first moment under block
  independence.
- **Step.** The first absorption step after the payment. Infinitely many
  edge-disjoint bounded cluster-arcs between two distinct clusters would put a
  single edge on infinitely many short cycles. Labels outside `F` are
  excluded beforehand by Theorem A of
  [[fpbs-malnormal-measured-absorption-cap]].

**Not claimed.**
- Nothing is claimed about kappa-escaping contact classes, where `kappa`
  tends to infinity along the class with finite level sets.
- Nothing is claimed about growing windows, non-Bernoulli actions, countably
  many payments, long-generator payments, or certificates not built as
  chains.
- No lower bound on `relC` is claimed. For
  [[fpbs-mal-bernoulli-single-stage-floor]] this kills the "pay epsilon, then
  absorb for free" shape of a proof of the negation, `relC = 0`, apart from
  the items just listed.

## Attempts
