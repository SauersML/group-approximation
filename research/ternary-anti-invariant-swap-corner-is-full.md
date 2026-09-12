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
