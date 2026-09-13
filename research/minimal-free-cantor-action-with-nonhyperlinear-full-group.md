---
rg: 2
id: minimal-free-cantor-action-with-nonhyperlinear-full-group
kind: claim
title: Some minimal topologically free Cantor action has a topological full group with a non-hyperlinear subgroup
distinct_from:
  non-hyperlinear-group: that is the goal itself; this asks for the witness to sit inside a topological full group, where the dynamical break lines below apply.
  kun-thom-product-action-alternating-full-group-is-nonsofic: that is nonsoficity of one alternating full group; this asks for failure of hyperlinearity.
  measure-full-group-subgroups-hyperlinear-if-crossed-product-ce: that is the positive transfer theorem that fences this claim off from measure-preserving actions with Connes-embeddable crossed products.
---

**OPEN.** There is a countable group `G` acting minimally and topologically freely on the Cantor set by `alpha` such
that some subgroup of `[[alpha]]` is not hyperlinear. This is permanence-stress question Q3 of
`research/artifacts/ideas-2026-09-13/nh/nh-permanence-stress.md`, in its general form.

## Where a witness can live

- **Not in residually finite actions.** Ma, arXiv:2209.00580, Theorem C (TeX l.404–406, verbatim): "Let
  $\alpha: G\curvearrowright X$ be a minimal topologically free residually finite action of a countable discrete
  group on the Cantor set. Then $[[\alpha]]$ is LEF and thus sofic." Residual finiteness is Kerr–Nowak's
  (Ma l.1186–1188): finite ε-dense sets carrying genuine `G`-actions that ε-follow `alpha` on finite sets. Ma's proof
  (l.1253–1282) reads a permutation model off the cocycle pieces of each element, and it is an exact homomorphism
  because each finite model is a genuine action. Main has the local-residual-finiteness form in
  `lrf-cantor-actions-give-lef-full-and-elementary-groups`.
- **Not for free groups with an invariant measure.** Ma, Corollary (l.411–413): minimal topologically free
  `F_r`-actions with an invariant Borel probability measure have LEF full groups. Main:
  `free-group-crossed-product-matricial-iff-invariant-measure`, `free-group-full-support-invariant-measure-actions-are-rf`.
- **Not for amenable orbit structure.** `amenable-orbit-full-group-subgroups-are-sofic`.
- **Not for measure-preserving actions with a Connes-embeddable crossed product.**
  `measure-full-group-subgroups-hyperlinear-if-crossed-product-ce`: with an essentially free invariant measure of full
  support, a witness forces `L^infinity(X, mu) ⋊ G` to be non-Connes-embeddable.

So a witness needs either (a) an action with no essentially free invariant probability measure of full support
(paradoxical or boundary-type dynamics), or (b) a measure crossed product that is itself not Connes-embeddable, which
already needs `G` or the orbit relation to be non-hyperlinear in a strong sense.

## Attempts

1. **Kun–Thom lamp action (region (b)).** Main has `kun-thom-product-action-alternating-full-group-is-nonsofic`: the
   alternating full group `A(Y)` of the Kun–Thom wreath `W` acting on `{0,1}^(G/Gamma) × G/K` contains the image of a
   finite-index subgroup of `W`. The product of the uniform Bernoulli measure and counting measure is `W`-invariant
   with full support. If `W/Z` is non-hyperlinear, `A(Y)` is a witness. By the transfer theorem, whenever the action
   is essentially free for that measure (not checked here), a non-hyperlinear `A(Y)` forces the crossed product to be
   non-Connes-embeddable. So this region gives nothing beyond hyperlinearity of the Kun–Thom wreath itself.
2. **Boundary and paradoxical actions (region (a)).** For `F_d` acting on its boundary there is no invariant measure,
   and main has `boundary-action-elementary-simple-kazhdan-not-mf` for the elementary groups over the crossed product
   ring. The full groups of such one-sided shift dynamics contain Thompson-type groups whose soficity and
   hyperlinearity are open. No mechanism for non-hyperlinearity of the full group itself was found; the transfer
   theorem gives no information there, because no invariant trace of the form `mu ∘ E` exists.
3. **What a mechanism must do.** In region (a) every trace on the crossed product that is faithful on full-group
   unitaries has to come from somewhere other than an invariant measure. A non-hyperlinearity proof has to show that
   no tracial matricial model of the full group can exist, while the crossed product carries no invariant trace at all.
   This matches the break line found by the permanence-stress lane: gluing across non-amenable pieces.
