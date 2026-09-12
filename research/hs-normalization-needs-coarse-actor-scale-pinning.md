---
rg: 2
id: hs-normalization-needs-coarse-actor-scale-pinning
kind: claim
title: Vertex rounding closes HS normalization only together with a coarse actor gap and mass-weighted transport
distinct_from:
  hs-normalization-profile-rounding-crux: that is the refuted literal-commutant rounding lemma; this is the corrected conditional assembly, with a perturbation-stable rounding target and the two further inputs the median step consumes.
  kt-wreath-relative-canonical-actor-exactification: that exactifies the whole actor restriction, after which finite-dimensional commutant no-growth needs no median at all; this assumes only rounding of the Kazhdan vertex, and then needs a coarse actor gap to pin multiplicity scales.
  hs-expander-block-decomposition: that is the nested abelian Leavitt-pair decomposition consumed by the established median route; this uses isotypic central projections of a rounded vertex representation, whose blocks carry no scalar per-block vertex gap, together with a one-level actor decomposition.
  hs-one-level-expander-block-decomposition: that asks for a one-level block decomposition of one Kazhdan group; this is a conditional normalization statement that uses such a decomposition of the actor as one of three hypotheses.
artifacts:
  - research/artifacts/hs-median-assembly-audit-2026-09-12.md
  - research/artifacts/hs-scale-pinning-2026-09-12.md
---

**OPEN.** Let `Gamma < G` be an infranormal pair of Kazhdan groups, `t` a strict
compressor, and `Lambda = t Gamma t^(-1)`. Let `sigma_n : G -> U(n)` be
coordinates of a trace-preserving `sigma : G -> U(prod_U M_n)`. Assume the
following, along `U`.

- **(H1) Stable vertex rounding.** After `o(n)` padding there are genuine
  representations `pi_n : Gamma -> U(n')`, with `n'/n -> 1`, such that
  `max_(s in F_Gamma) ||sigma_n(s) - pi_n(s)||_2 -> 0`.
- **(H2) Coarse actor gap.** The approximate actor `sigma_n|G` admits a one-level
  decomposition as in `hs-one-level-expander-block-decomposition`: vanishing
  total boundary and a uniform scalar adjoint gap `kappa'_G` on every block.
  Its blocks almost commute, mass-weighted in 2-norm, with the center of
  `pi_n(Gamma)'`.
- **(H3) Mass-weighted transport of the aspect ratio.** Let `z_i` be the minimal
  central projections of `pi_n(Gamma)'`, with multiplicity `m_i` and irreducible
  dimension `d_i`. Put `zeta_n = sum_i (m_i / d_i) z_i`, and let `zeta'_n` be the
  same observable for `pi_n|Lambda`. Then `Ad sigma_n(t)` carries `zeta_n` to
  `zeta'_n` on matched atoms, up to `o(1)` in normalized `L^1`, with atoms of
  total trace `o(1)` left unmatched.

**Conclusion (open).** `sigma(G)` normalizes `sigma(Gamma)' cap prod_U M_n`.

The intended proof follows Kun--Thom's two median arguments.
- Restricting from `Gamma` to `Lambda` can only merge isotypic components
  (`m` grows) or split them (`d` shrinks). So `zeta` is one-sidedly monotone,
  and it is strictly monotone exactly where the commutant grows.
- Trace conservation along `t` makes the transported observable almost
  invariant.
- `median-poincare-concentration`, which assumes no unitarity, pins
  `f = zeta/(zeta + m_A)` at `1/2` on the coarse blocks of (H2).
- A macroscopic wall forces a factor `1 + c` jump of `zeta` on order-one mass,
  which the concentration excludes.

The steps and their uniformity checks are in the artifact. None is verified to
the standard of an established claim.

**Update (2026-09-12, lane `hs-scale-pinning`).**
- **(H3) is redundant.** In the multiplicative, all-scales form the median step
  consumes, (H3) follows from (H1) and property (T) of `Lambda`. The ESTABLISHED
  `vertex-rounding-reduces-ccr-to-commutant-excess` proves
  `sup_(a>0) ||F_a(zeta_B) - sigma_n(t) F_a(zeta_A) sigma_n(t)^*||_2 -> 0`, with
  `F_a(x) = x/(x+a)`.
- **The additive `L^1` form of (H3), as stated above, is too weak.** It is vacuous at
  large irreducible dimension: for an irreducible of dimension `n` splitting in halves,
  `||zeta_B - zeta_A||_1 = 1/n`, while the excess is `1/2`.
- **(CCR) is a finite-dimensional quantity.** The same claim shows that under (H1), (CCR)
  is the vanishing of the finite commutant excess of `pi_n(Gamma)' <= pi_n(Lambda)'`.
  `commutant-excess-bounded-by-aspect-ratio-jump-mass` (ESTABLISHED) bounds that excess
  by `4 tau(zeta_B >= (1+c) zeta_A)^(1/2) + 2c`. The last step of the intended proof is
  therefore proved.
- **The corrected conditional is (H1) + (H2') implies (CCR).**
  - (H2') is (H2) stated at a generating set `F_Gamma cup {t_i^(+-1)}` whose `t_i` are all
    strict compressors. A generator that is not a compressor has no supplied almost
    invariance of the median observable.
  - The only unwritten step is the mass-weighted block functional calculus (S4 in the
    scale-pinning artifact).
- **Cascades refute (H2'), not the assembly.** Under (H1), a cascade with order-one jump mass
  contradicts (CCR) through the excess lemma, so it forces (H2') to fail. A cascade needs a
  slowly varying, ungapped almost-central observable of the actor that the compressors
  shift.

## Attempts

- **Literal-commutant rounding.** Dead: `hs-literal-commutant-profile-rounding-is-false`.
  The target in (H1) is therefore a nearby genuine representation, not the exact
  commutant of the supplied matrices.
- **Actor exactification instead of (H1)-(H3).** If `sigma_n|G` itself rounds to
  genuine representations, finite-dimensional commutant no-growth gives the
  conclusion with no median (`kt-wreath-relative-canonical-actor-exactification`,
  step KRE3). This claim matters only where the vertex rounds and the actor does
  not.
- **(H1) plus flexible type matching, no scale pinning.** Dead as a proof strategy.
  - Property (T) of `Lambda` turns (H1) into a flexible unitary equivalence
    between `pi_n|Lambda` and `lambda -> sigma_n(t) pi_n(t^(-1) lambda t) sigma_n(t)^*`,
    off `o(1)` normalized dimension. Per-type multiplicities then agree up to
    `o(n)` weighted error.
  - That does not exclude merges on order-one mass. Take `L` levels of isotypic
    types in which restriction merges siblings: `m_parent = m_child1 + m_child2`,
    equal irreducible dimension, mass `1/L` per level.
  - The weighted discrepancy lives only on the two boundary levels and is `2/L`,
    while every level carries a wall.
  - A statistic must pin multiplicity scales inside each ambient block. That is
    the median step, and it needs (H2).
- **Trace or irreducible dimension as the size.**
  - Merges preserve both, and the trace is refinement-blind (`invariant-size-collapse`).
  - The observable monotone under merges and under splits is `zeta = m/d`.
- **The established median route.** `tracial-median-from-block-decomposition`
  consumes abelian fine blocks with a scalar per-block vertex gap
  (`hs-expander-block-decomposition`).
  - Isotypic central projections of `pi_n(Gamma)'` have no such gap once a
    multiplicity exceeds one, because `pi_n(Gamma)` fixes the multiplicity
    algebra. So (H1) does not instantiate that route.
  - The median step has to be rerun with `zeta` on the coarse actor blocks of (H2).
- **Coarse blocks from the literal actor commutant.** Dead for the same reason as
  the vertex case. The perturbation of `hs-literal-commutant-profile-rounding-proof`
  applies to the actor tuple, so (H2) must be a decomposition with a gap, not a
  center of the literal commutant.
