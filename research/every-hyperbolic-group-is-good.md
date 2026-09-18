---
rg: 2
id: every-hyperbolic-group-is-good
kind: claim
title: Every word-hyperbolic group is good in Serre's sense
distinct_from:
  hyperbolic-finite-residual-is-torsion-free: that is the universal torsion-free-residual assertion, equivalent to universal residual finiteness; this is a profinite-cohomological assertion that implies it, with no converse known
  good-groups-have-no-persistent-finite-cohomology: that is a proved consequence of goodness for one group; this is the open assertion that every hyperbolic group is good
---

For every word-hyperbolic group `G`, every finite `G`-module `A` and every `q >= 0`, the
inflation map `H^q(G_hat;A) -> H^q(G;A)` is an isomorphism.

**Status: open.** By `good-cocompact-proper-groups-are-virtually-torsion-free` (H), this
implies that every hyperbolic group is virtually torsion-free and residually finite.
So it is at least as hard as Gromov's question. We did not check whether it is posed
as a named problem in the literature.

## Attempts

- **Through special cube complexes.** Hyperbolic virtually special groups are good
  (Kropholler–Wilkes, Theorem 9, recorded on
  `good-groups-have-no-persistent-finite-cohomology`). This covers exactly the
  cubulated hyperbolic groups, which are already residually finite. It dies at
  hyperbolic Kazhdan groups, which admit no proper cocompact cubulation, for example
  the density random groups above `1/3` (`gromov-density-random-groups-kazhdan-above-third`).
  No goodness theorem is known for them.
- **Only a weak form is needed downstream.** The route into
  `hyperbolic-finite-residual-is-torsion-free` uses only (G'). That is surjectivity of
  inflation with trivial `F_p` coefficients in large degrees, or even just onto the
  Chern–Quillen classes. The full isomorphism is never used.
- **The negative direction gives nothing by itself.** A residually finite hyperbolic
  group that is not good does not contradict residual finiteness. Non-goodness of a
  hyperbolic group decides neither root. What a counterexample to Gromov's question
  must fail is the specific surjectivity onto Chern–Quillen classes.
- **Entropy-measure transplant (swarm-0917-w9).** The idea was to replace finite quotients by a measurable
  object, lifts of p.m.p. actions across finite extensions, and to construct those lifts by ergodic methods.
  - `kazhdan-degree-two-goodness-iff-profinite-measurable-lifts` (ESTABLISHED, via Ioana's profinite cocycle
    superrigidity) shows the dictionary is exact in degree two for residually finite Kazhdan groups.
    - A lift of any free ergodic profinite action across a finite extension already forces virtual splitting.
    - Degree-two surjectivity of inflation for every finite-index `N` and finite `A` is equivalent to
      measurable lifts of `N ~> N̂`.
  - So in degree two the transplant gains nothing, exactly on the hyperbolic Kazhdan groups where the cubical
    route dies. Every measurable lift over a profinite action is a finite-quotient construction in disguise.
  - Lifts over Bernoulli-type or treeable actions do not help either. They carry no information about goodness:
    they force actual splitting (`central-bernoulli-lifts-force-splitting`) or always exist
    (`treeable-free-actions-lift-across-finite-normal-extensions`).
  - It dies at degree `>= 3`. Ioana's theorem controls 1-cocycles into groups, which reach degree two through
    extensions. No rigidity is known for measurable `q`-cochains with `q >= 3`. So the high-degree half used by
    `torsion-free-hyperbolic-mod-p-classes-die-virtually` has no measurable reformulation.

- **Goal relevance (2026-09-17, swarm-0917-w13-titz-pull, reframing). This node is inert for
  `torsion-free-sofic-exact-mf-radical-over-z`.** Neither a proof nor a disproof here can move the goal
  through the Titz--Witzel region. So the dispatcher's bounty on this node, which comes from that cone, is
  illusory.
  - *Result.* `fully-ramified-covers-cannot-create-titz-witzel-soficity` (ESTABLISHED) shows the following.
    Let `X' -> X_0` be any fully ramified tower over `Y_1^2`, for instance `Lambda \ D` for a torsion-free
    or normal finite-index `Lambda` in a complex of groups over `X_0`, and let it satisfy the flat-hitting
    condition (H). Then `beta(X') >= beta(X_0) + (1 - phi(X_0)) / [G : K]`. So sparse flat-hitting output
    forces the base to satisfy item 3 of `sparse-fully-branched-covers-iff-sofic-with-connected-links`,
    which is already equivalent to `titz-witzel-kernel-sofic`.
  - *Invariant.* The branched-sheet fraction `phi(X_0)` of the base.
  - *Step where every member dies.* Hitting an unbranched base component costs a whole fibre.
  - *Consequence.* Goodness, (V2), residual finiteness and cubulation of hyperbolic groups enter the cone
    only at the torsion-free or normal finite-index step, so they can never be the source of soficity of
    `K`. The flat-hitting node needs a partially ramified construction, and goodness is irrelevant to that.
  - Separately, `sp21-finite-congruence-kernel-forbids-p-goodness` already records CSP => non-good. There
    is no cheap route to a negative answer through arithmetic lattices of hyperbolic type, since uniform
    lattices in `Sp(n,1)` are hyperbolic and CSP for them is itself open.
