# HS median assembly audit, 2026-09-12

Lane `hs-median-assembly`.

**Question.** Does `hs-normalization-profile-rounding-crux`, together with
`tracial-median-concentration` and `median-poincare-concentration`, close
`kt-centralizer-normalization-hs`? Equivalently, by the dichotomy, does it close
`hyperlinear-groups-kill-rigid-compression-defects`?

**Answer: no.** Three findings.
1. The crux is false as stated (`hs-literal-commutant-profile-rounding-is-false`).
2. The established median route consumes a different prerequisite.
3. A perturbation-stable repair needs two further inputs. They are recorded as
   the open conditional `hs-normalization-needs-coarse-actor-scale-pinning`.

No route in Cairn consumed the crux, so no `invalidates:` was needed. The crux
node now carries `refuted_by:`.

Marks used below:
- `[U]`: a quantity must be uniform in the dimension `n`.
- `[L]`: an ultraproduct limit is exchanged with a finite-stage estimate.

## 0. Target and lift

- **Target.** For a trace-preserving `sigma : G -> U(prod_U M_n)`, the relative
  commutant `R = sigma(Gamma)' cap prod_U M_n` is normalized by `sigma(G)`.
  Minimal kernel, per strict compressor `t` with `Lambda = t Gamma t^(-1)`:
  (CCR) `sigma(Lambda)' cap M <= sigma(Gamma)' cap M`.
- **Lift.** Coordinates `sigma_n` have defects `-> 0` along `U`. A unitary `z` in
  `R` lifts to `z_n` with `max_s ||[z_n, sigma_n(s)]||_2 -> 0` along `U`.
- **[L1].** The rate depends on `z`: no single `delta_n` serves every element of
  `R`. Every finite-stage lemma must therefore hold with constants uniform in `n`
  and in the element, and the `U`-limit is taken after the estimate.
  - The crux asks for this (`f` uniform in `n`), so [L1] is not where it fails.
  - For finite-dimensional algebras, approximate centers are uniformly close to
    exact centers, so `Z(prod_U A_n) = prod_U Z(A_n)`. The obstruction is not the
    ultraproduct of centers.

## 1. Rounding the approximate commutant center (the crux)

- **The chain's step.** Almost-central projections of `A_n(delta)` round to
  central projections of `sigma_n(Gamma)' cap M_n` with a controlled profile. [U]
- **Refutation.** `hs-literal-commutant-profile-rounding-is-false`, in fixed
  dimension `2d`.
  - Take `pi = pi_1 (+) 1_d`, nontrivial irreducible `pi_1` of a finite quotient
    covered by the generating set, and `p = I_d (+) 0`.
  - The quotient gap `sqrt(2)` makes `p` `delta`-central in `A(delta)`.
  - A generic perturbation of the generators by `O(delta)` makes the literal
    commutant scalar.
  - Every central projection of the literal commutant is then `0` or `I`, at
    2-distance `1/sqrt(2)` from `p`.
- **Mechanism.** The literal commutant is discontinuous under operator-norm
  perturbation. This is the projection form of
  `generic-perturbations-destroy-exact-commutant-gap`. Neither the profile nor
  uniformity rescues it.
- **Repair.** Round to the commutant of a nearby genuine representation after
  negligible padding. That is (H1) of the conditional. The other perturbation-
  stable target, the robust low band, has no minimal central projections and no
  irreducible dimensions, so the profile cannot be stated there.

## 2. The size observable

- **What the chain says.** "Normalized block dimension" of rounded minimal
  central projections. There are two candidates, and neither is monotone under
  every way a commutant can grow along restriction `Gamma -> Lambda`:
  - **Irreducible dimension `d_i`:** a merge (`pi_1|Lambda ~ pi_2|Lambda`
    irreducible) keeps `d` and creates a wall.
  - **Multiplicity `m_i` (the commutant block rank):** a split keeps `m` and
    creates a wall.
- **The right observable.** `zeta = m/d` weakly increases under restriction, and
  strictly on the mass where the commutant grows.
- **Macroscopic walls.**
  - A split into `d_a + d_b` has wall mass about `(d_b/d)` times the block mass.
  - A merge has wall mass about the smaller merged mass.
  - So a wall of order-one 2-norm forces a factor `1 + c` jump of `zeta` on
    order-one mass. [U: `c` depends only on the wall size.]
- **[U] Refinement blindness.** `zeta` is not trace-sized. The dimensionless
  median transform `f = zeta/(zeta + m_A)` is what the concentration step must
  act on.

## 3. Compressor transport

- **Rounded data.** `Ad sigma_n(t)` sends the center of `pi_n(Gamma)'` to the
  center of the transported representation of `Lambda`.
- **Exact level.** The centers `Z(pi(Gamma)')` and `Z(pi(t^(-1) Gamma t)')`
  commute, because `Gamma <= t^(-1) Gamma t`. They are generally not nested:
  restriction merges and splits isotypic components.
- **Consequence.** The mass-weighted clause `(MW)` of
  `hs-per-atom-compressor-clause-is-vacuous`, "atoms go to atoms", is the wrong
  shape for isotypic atoms. What transports is `zeta`, one-sidedly. That is (H3).
- **Flexible intertwiner.**
  - Property (T) of `Lambda` gives an exact intertwiner between `pi_n|Lambda` and
    the transported representation off `o(1)` normalized dimension. The Kazhdan
    constant is fixed at the transported generating set. [U]
  - This supplies type matching, not scale pinning: see the cascade below.
- **Cascade.**
  - Setup: `L` levels of types in which restriction merges siblings, with
    `m_parent = m_child1 + m_child2`, equal `d`, and mass `1/L` per level.
  - Weighted type discrepancy: only at the two boundary levels, `2/L -> 0`.
  - Walls: on all mass.
  - So flexible matching alone cannot yield (CCR). A statistic that pins `zeta`
    inside each ambient block is required.

## 4. Median concentration by property (T) of the actor

- `median-poincare-concentration` (established, no unitarity assumed) pins a
  bounded observable with median `1/2` once a scalar Poincare inequality holds
  on a block.
- The blocks must be coarse actor blocks: a one-level decomposition of the
  approximate `sigma_n|G` with a uniform gap `kappa'_G`. [U] That is (H2),
  i.e. `hs-one-level-expander-block-decomposition` for `G`, plus compatibility
  with the rounded vertex center.
- The literal actor commutant cannot supply these blocks. The perturbation of
  section 1 applies to the actor tuple too.
- **[L2].** Trace conservation `tau(Ad sigma_n(t) f) = tau(f)` is exact at each
  finite stage. The positive/negative-part step gives normalized `L^1`
  invariance per coordinate, and only then is the `U`-limit taken.
- `tracial-median-from-block-decomposition` is not instantiated: its fine blocks
  need a scalar per-block vertex gap, which isotypic projections lack when
  `m > 1`.

## 5. Collapse

- One-sided monotonicity of `zeta` along `t`, almost-invariance in `L^1`, and
  median pinning together give `zeta`-ratios `-> 1` inside coarse blocks on most
  mass.
- By section 2, macroscopic walls die, which is (CCR).
- **[L3].** The contradiction in the Theorem-A endgame needs a lamp of fixed
  2-distance `sqrt(2)`. Negligible padding and the unmatched mass of (H3) change
  2-norms by `o(1)`, consistent with the small-block-surgery fence recorded on
  `kt-centralizer-normalization-hs`.

## 6. Regimes

| regime | rounding | needs medians? | status |
| --- | --- | --- | --- |
| literal commutant of supplied matrices | discontinuous | -- | refuted |
| actor exactification (KRE2) | genuine `G`-representations | no, finrank no-growth | open |
| vertex rounding only (H1) | genuine `Gamma`-representations | yes, with (H2), (H3) | open conditional |
| robust low band | no minimal central projections | profile undefined | no assembly known |

**Consistency check.** Property (T) of `Gamma` alone cannot be enough. The
one-compressor sofic wreath carries a rigid defect with only `Gamma` Kazhdan
(ladder artifact, Theorem 4 row). Any correct assembly must use property (T) of
the actor, or the full compression semigroup. (H2) is where it enters.
