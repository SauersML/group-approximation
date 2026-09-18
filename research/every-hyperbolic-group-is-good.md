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
- **Symbolic-dynamics transplant (swarm-0917-w12).** The idea was to replace finite quotients by compact
  `G`-spaces on which a class dies, and to find finite orbits by symbolic dynamics.
  - `primitive-shifts-detect-virtual-vanishing` (ESTABLISHED, elementary) shows the dictionary is exact in
    every degree. Each class `x ∈ H^q(G;A)` has a primitive shift `Σ(z) = {ψ : ψ∘∂_q = z}`.
    - `Σ(z)` is an affine SFT with an invariant Haar measure.
    - It is the terminal effacer: `x` dies over `X` exactly when there is a `G`-map `X -> Σ(z)`.
    - `Σ(z)^H ≠ ∅` exactly when `res_H x = 0`.
  - So goodness is exactly the statement "every primitive shift has a finite orbit".
  - **Where it dies.** It dies at the step from an effacer to a finite-index subgroup. That step is the
    existence of a periodic point in `Σ(z)`, which is `res_H x = 0` itself.
    - SFT, invariant measure, minimality, freeness (Gao–Jackson–Seward products) and expansiveness all come
      free for effacers, so none of them carries information.
    - Profinite odometers efface only effaceable classes.
  - **The principles are the wrong strength.** The principles that would supply periodic points fail.
    - On `Γ(3) <= SL_3(Z)`, the persistent classes of `sl3z-level-three-fails-degree-two-goodness` give a
      measured affine SFT with no finite orbit. They also give a linear SFT, on a torsion-free Kazhdan group
      of type F, whose periodic points are not dense.
    - `linear-coset-shift-periodic-density-iff-separable` (ESTABLISHED) shows that periodic density for
      linear SFTs forces LERF. So it fails on the good, non-LERF, Rips-construction hyperbolic groups, and it
      is strictly stronger than goodness.
  - **What survives.** "Primitive shifts of degree `>= 3` on torsion-free hyperbolic groups have finite
    orbits". This is equivalent to `torsion-free-hyperbolic-mod-p-classes-die-virtually`, not a reduction
    of it.
  - Artifact: `research/artifacts/primitive-shift-goodness-dictionary-2026-09-18.md`.
