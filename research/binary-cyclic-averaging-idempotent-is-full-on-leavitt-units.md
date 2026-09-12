---
rg: 2
id: binary-cyclic-averaging-idempotent-is-full-on-leavitt-units
kind: claim
title: The averaging idempotent of a ternary permutation unit is full in the binary Leavitt unit group algebra
refuted_by:
  - binary-leavitt-units-carry-nonaugmentation-rank-function
distinct_from:
  leavitt-visible-cyclic-corner-is-full-on-some-host: that is the twisted corner on the visible factor of some host; this is the untwisted corner 1 + g + g² in F_2[R^x] itself, which ascends to the host (4, 2, 3) but is not known to follow from it.
  thompson-v-order-three-averaging-idempotent-is-full: that is an order-three prefix-code element of Thompson's V; this is the permutation unit of a ternary Leavitt family in R^x, whose averaging idempotent has image equivalent to 1 in R.
artifacts:
  - research/artifacts/quaternary-twisted-corner-census-2026-09-12.md
---

**OPEN.** Let `R = L_(F_2)(1,2)` with the ternary family `s_1 = s0`, `s_2 = s1 s0`, `s_3 = s1 s1`
(and `t_1 = t0`, `t_2 = t0 t1`, `t_3 = t1 t1`), let `g = s_2 t_1 + s_3 t_2 + s_1 t_3`, and
`e = 1 + [g] + [g²]` in `F_2[R^x]`. Exhibit `b, c` in `F_2[R^x]` with `c e b = 1`.

**What it gives.**
- `c e` and `e b` form a strict one-sided pair, so `F_2[R^x]` is not directly finite and `R^x` is not
  surjunctive (route `binary-cyclic-corner-fullness-gives-kaplansky-failure`).
- Multiplying by the visible scalar idempotent of `F_4[L_(F_4)(1,2)^x]` gives a solution of the twisted
  corner at `(q, d, m) = (4, 2, 3)` (route `binary-cyclic-corner-ascends-to-quaternary-twisted-corner`).

## Attempts

- **The image equation holds.** `b = s_1 + s_2 + s_3` and `c = t_1 + t_2 + t_3` give `c pi(e) b = 1` in
  `R`. Direct finiteness does not pass back from quotients, so the lift is the problem.
- **The augmentation does not obstruct.** `epsilon(e) = 1 = epsilon(1)`, so `F_2[R^x]` keeps its
  augmentation state and fullness asks only for a complement class of augmentation zero.
- **What does obstruct, if it exists.** Through the ascent to `(4, 2, 3)`, any state on the visible factor
  over `F_4`, or any characteristic-two rank model of a subgroup containing the scalars `F_4^x`, `g`,
  `δ = ω s_1 t_1 + ω² s_2 t_2 + s_3 t_3` and the witness supports with nonzero visible scalar component,
  kills this corner (`twisted-rank-models-kill-visible-cyclic-corner-witnesses`). No such state or model
  is known.
- **Permutation-module form (w4-binary-cyclic, 2026-09-12).** `c e b = 1` holds iff `F_2[R^x]` is a
  direct summand of the right permutation module `F_2[⟨g⟩\R^x]`, i.e. iff that module has a unimodular
  element. A single coset never is one.
  - Source: Proposition 0.1 of `research/artifacts/binary-cyclic-corner-rank-function-dichotomy-2026-09-12.md`.
  - Among averaging corners of finite subgroups containing `g`, this target is the weakest (Proposition 0.2).
- **A witness leaves one rank function (w4-binary-cyclic).** By
  `simple-group-rank-functions-are-augmentation-or-detecting`, a solution makes the augmentation rank the
  only Sylvester matrix rank function on `F_2[R^x]`. So any other rank function refutes this claim
  (`binary-leavitt-units-carry-nonaugmentation-rank-function`).
  - **Dead sources:** evaluation to `R`, homomorphisms to `M_n(D)`, and monomial models.
  - **Sufficient source:** linear soficity over `F_2`.
  - **Support filter:** on a witness subgroup `Γ = ⟨g, supp b, supp c⟩`, `g` must die in every finite,
    sofic or linear sofic quotient of `Γ` (Corollary 1.4). So no witness lives in a residually finite or
    virtually free subgroup containing `g`.
- **Finite-subgroup classes stay measure-consistent (w4-binary-cyclic).** Put `D(h) = Σ s_i h t_i` and take
  the nine-cylinder group `⟨g, D(g)⟩ ≅ C_3²`. Then:
  - `[1 − e] = 3[e − e_(C_3²)]` in `K_0`;
  - the halving map `x -> e D(x)` shifts `[e_(C_3^k)]` to `[e_(C_3^(k+1))]`.

  Every such relation matches the lifted trace `3^(-k)`, so finite-subgroup bookkeeping never produces
  the complement (artifact Section 3).
- **Lifts of the image solution (w4-binary-cyclic).** WLOG `b = e z` and `c = w e`, so the equation reads
  `w e z = 1`.
  - Neither `w` nor `z` can be a single group element.
  - `π(e) = bc` is the all-ones matrix in the ternary picture `R ≅ M_3(R)`, and `π(g) b = b`.
  - No group-level candidate survives the support filter yet; the artifact's Section 3.4 records where it stops.
