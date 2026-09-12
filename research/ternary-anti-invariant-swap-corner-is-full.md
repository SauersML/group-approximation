---
rg: 2
id: ternary-anti-invariant-swap-corner-is-full
kind: claim
title: The swap-averaging idempotent is full in the anti-central summand of the ternary Leavitt group algebra
distinct_from:
  projective-ternary-swap-idempotent-is-full: that is the corner equation on the central summand F_3[PG], where the Leavitt evaluation vanishes; this is the corner equation on the complementary summand, through which the Leavitt evaluation factors and where its image equation holds.
  ternary-leavitt-swap-idempotent-is-full: that is the corner equation on the whole group algebra, which implies both halves; this asks only for the anti-central half, which already suffices for a counterexample.
artifacts:
  - research/artifacts/invariant-output-descent-and-sensitivity-2026-09-12.md
  - research/artifacts/gk-verify-pos-permanence-chain-2026-09-12.md
---

**OPEN.** Let `R = L_(F_3)(1,2)`, `G = R^x`, `S = F_3[G]`, `z = -1`, `eps_+- = 2(1 +- [z])`,
`w = s0 t1 + s1 t0` and `e_- = eps_- . 2(1 + [w])`. Exhibit `b, c` in `S_- = eps_- S` with

    c e_- b = eps_-.

By part 3 of `ternary-leavitt-swap-problem-splits-at-central-involution`, this is equivalent to a
unital two-pair Cohn family `gamma_i beta_j = delta_ij e_-` in the corner `T = e_- S_- e_-`.

**Why it suffices.** Put `A = e_- b + eps_+` and `C = c + eps_+`. Then `CA = 1`, and `AC != 1`
because `e_- != eps_-`. So `F_3[G]` is not directly finite, and
`stable-finiteness-failure-refutes-surjunctivity` gives an injective, non-surjective linear
automaton on the full shift `F_3^G`. It is the identity on the summand `x(gz) = x(g)` and strict on
the summand `x(gz) = -x(g)`. The route is `anti-invariant-swap-corner-refutes-ternary-surjunctivity`.

## Attempts

- *The image equation holds.* The Leavitt evaluation `pi : S -> R` factors through `S_-` and maps
  `T` onto `pi(e) R pi(e) ~= R`. There `b = s0 + s1` and `c = 2(t0 + t1)` satisfy the equation
  (Section 6 of the artifact). The lift from `R` to `S_-` is open, and direct finiteness does not
  pass to quotients (`direct-finiteness-not-inherited-by-quotients`). This is where it dies today.
- *Earlier misreading, withdrawn.* Proposition 7.4(d) of the artifact read a solution here as a
  strict map of a proper subshift only, and concluded that this half proves nothing. Correction
  7.4(e) of 2026-09-12 withdraws that: the subshift is a linear direct summand of the full shift.
- *Obstruction that binds.* A solution makes `F_3[G]` not stably finite, so `G` must not be linear
  sofic over `F_3` (`linear-sofic-group-algebra-is-stably-finite`). `G` is nonsofic
  (`d-ary-leavitt-groups-nonsofic-over-finite-fields`), so this does not exclude the target.
- *Exact reformulation, with no idempotent (2026-09-12, lane `gk-kdf-structure`).* This claim is
  equivalent to `ternary-twisted-algebra-has-swap-separated-one-sided-pair`: `a, c` in
  `S_- = F_3[G]/(1 + [z])` with `c a = 1` and `c [w] a = 0`. The two routes are
  `swap-separated-pair-gives-anti-invariant-corner` and
  `anti-invariant-corner-gives-swap-separated-pair`.
  - *Idempotent form.* An idempotent `p ~ 1` with `p [w] p = 0`.
  - *Cross-term form.* A one-sided pair `c a = 1` with `1 - m^2` invertible, where `m = c [w] a`.
    So a nilpotent swap cross term suffices.
  - *Consequences.* A solution need not lift the image solution `(s0 + s1, 2(t0 + t1))`: any
    one-sided pair of `S_-` whose swap cross term is controlled will do. The lift therefore
    splits into two sub-problems:
    - a direct-finiteness failure of `S_-`;
    - one cross term, which lies in the evaluation kernel when the pair lies over `(s0, t0)`.
  - Research artifact: `research/artifacts/ternary-swap-separated-pairs-2026-09-12.md`.
- *Digest (gk-archive, 2026-09-12).* **Proved:**
  - the split itself (`ternary-leavitt-swap-problem-splits-at-central-involution`), with the
    corrected reading that either half refutes (`anti-invariant-swap-corner-refutes-ternary-surjunctivity`,
    `projective-swap-corner-refutes-ternary-surjunctivity`);
  - nonsoficity of `G` and of `PG` through the scalar-avoiding embedding
    (`leavitt-units-embed-in-their-scalar-quotient`,
    `projective-leavitt-unit-groups-mod-scalars-are-nonsofic`), so Gromov--Weiss excludes neither host;
  - the binary normal forms, whose shape this problem shares
    (`leavitt-one-sided-pairs-are-unit-translates-of-s0-t0`,
    `leavitt-inverse-defects-are-visible-or-invisible`);
  - the idempotent-free reformulation above.

  **Dead:**
  - lifting along a quotient, because direct finiteness does not descend
    (`direct-finiteness-not-inherited-by-quotients`);
  - K_0-type invariants, because every defect has zero class;
  - trace, augmentation and finite-dimensional representations, which were checked on the projective
    half;
  - (T)-based rank rounding as a route to an obstruction, which fails over every finite field
    (`kazhdan-group-rank-models-admit-no-expander-decomposition`).

  **Binding gate:** linear soficity of `G` over `F_3` (`linear-sofic-group-algebra-is-stably-finite`).
  Its F_2 twin is `binary-leavitt-unit-group-is-f2-linear-sofic`.

  **Exact open step:** one pair `c a = 1` in `S_-` with `c [w] a = 0`, or with `1 - m^2` invertible.
  Siblings: the binary lifts `left-invertible-lift-of-s0-in-leavitt-group-algebra` and
  `leavitt-evaluation-kernel-unitization-not-directly-finite`, and the projective half
  `projective-ternary-klein-idempotent-is-full`.
- *Untested ideas reported by lanes, not yet nodes (gk-archive, 2026-09-12).*
  - *gk-kdf-structure.* Two ways past the rank-rounding counterexample are untried:
    - the compressor group's own property (T) used together with the compression itself;
    - a size function not built from atoms.

    In the rank ultraproduct the relative commutant can be diffuse
    (`kazhdan-rank-ultraproducts-can-have-diffuse-commutants`). Whether it is commutative, and whether
    it carries a size that forbids strict compression, is open. Both questions bear on the `F_3`
    linear-sofic gate that binds this claim.
  - *gk-kdf-lift.* For pairs lying over `(s0, t0)`, lifts `a`, `b` with `b a - 1` nilpotent already
    give a left inverse `(b a)^-1 b`. That shortcut was never tried on the ternary half.
- *Self-similarity (gk-l3-corner, 2026-09-12).* The attempt: make the image solution exact using
  the `delta` matrix-ring amplification, the corner embedding `iota` and the Klein splitting. Where
  each part dies:
  - *Amplification.* It lifts `Theta`: `pi o Phi = Theta o M_2(pi)`. It carries every lift defect
    injectively, so the recursion from `S_-` to `M_2(S_-)` is stationary.
  - *Equivariance.* No nonzero element of `k[G]` is an exact `delta`- or `iota`-equivariant lift of
    `s_i` or `t_i` (`self-similar-leavitt-intertwiners-have-no-exact-lift`). An exact family must
    break equivariance, with the breaking terms in `ker pi`.
  - *Dyadic constants.* Every amplification matrix unit lies in the locally finite dyadic constant
    subgroup, whose group algebra is stably finite. A witness needs units of non-uniform prefix depth.
  - *`iota` and the Klein splitting.* `iota` mixes `S_+` and `S_-`, and the Klein splitting sees
    only `S_+`.

  Section 2 of `research/artifacts/leavitt-self-similarity-exactness-2026-09-12.md`.
- *Idempotent-free forms (gk-l3-units, 2026-09-12).*
  - This claim is equivalent to `ternary-anti-central-summand-has-cohn-family`: a unital two-pair
    Cohn family in `S_-` itself, or four elements of `S_-` with invertible Gram matrix.
  - The tool is the diagonal endomorphism `delta(g) = s0 g t0 + s1 g t1`, which fixes `z` and
    centralizes `w` and `d`, so `S_-` contains `M_2(S_-)` unitally
    (`anti-central-ternary-summand-contains-its-matrix-ring`; routes
    `anti-central-cohn-family-gives-swap-corner-fullness` and
    `swap-corner-fullness-gives-anti-central-cohn-family`).
  - The canonical trace has `tau(1_-) = 2`. It forbids an exact lift of the binary Leavitt family
    `(s_i, t_i)` into `S_-`, and allows the quaternary family `(s_i s_j, t_j t_i)`, which suffices
    (`anti-central-ternary-summand-has-no-binary-leavitt-family`,
    `ternary-anti-central-summand-has-quaternary-leavitt-family`).
