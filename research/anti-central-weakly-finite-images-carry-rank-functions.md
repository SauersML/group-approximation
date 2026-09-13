---
rg: 2
id: anti-central-weakly-finite-images-carry-rank-functions
kind: claim
title: A weakly finite image of the ternary anti-central summand with faithful states carries a Sylvester rank function
distinct_from:
  anti-central-rank-condition-gives-weakly-finite-image: that produces the weakly finite image with faithful states from a state; this asks that such an image carry a Sylvester matrix rank function, the step that must invent ranks for nilpotents.
  sylvester-rank-functions-on-leavitt-units-are-regular: that asks every rank function on the binary group algebra to factor through a regular rank ring; this is the ternary existence question on a weakly finite quotient, before any rank function is known.
artifacts:
  - research/artifacts/state-upgrade-rank-condition-gap-2026-09-12.md
---

**OPEN.** Step (U1b) of the state upgrade. Let `W` be a nonzero weakly finite quotient of
`S_- = eps_- F_3[G_3]` on which every state of `(K_0(W), [W])` is faithful on idempotent matrices, with
`G_3` embedded in `W^x` and `z -> -1`. Then `W` carries a Sylvester matrix rank function.

**Payoff.** With `anti-central-rank-condition-gives-weakly-finite-image` (established), it gives
`ternary-anti-central-states-give-sylvester-rank-functions` (U1), through route
`sylvester-rank-functions-from-weakly-finite-images`.

**What it must supply** (`rank-functions-extending-a-state-are-pinned-on-regular-elements`).
- **Regular elements are determined.** A state fixes the rank of every regular element, and weak
  finiteness adds nothing for them.
- **Nilpotent data is free.** For order-three unipotents `g`, the rank `N(g - 1)` can be anything in
  `[0, 2/3]` on `F_3[<g>]`. (U1b) must choose these Jordan types consistently.

## Attempts

- 2026-09-12 `w4-upg-state` (artifact Section 4): kill test for the general ring statement.
  - **The configuration.** A weakly finite ring `W ⊇ M_4(K)` with faithful states, holding `u ∈ M_4(W)`
    with `u^3 = 0` and `L u R = diag(1,1,1,0)`.
  - **Why it would kill (U1b).** No Sylvester rank function exists there: `N(u) <= (2/3)·4 < 3`.
  - **Open.** Whether such a `W` exists is not known.
  - **The `1 x 1` case collapses.** If `L u R = 1` in a weakly finite ring, then `uR` is a unit, `u` is
    right invertible, and `u^3 = 0` kills the ring.
  - **A possible first lemma.** A rank-level analogue of the retract trick of
    `rank-condition-rings-have-weakly-finite-images`, killing "Frobenius-violating" configurations the
    way that result kills class-zero idempotents. No such lemma is known.
- 2026-09-12 `w5-upg-flatten` (artifact `research/artifacts/separated-triangular-certificates-flatten-2026-09-12.md`).
  - **The kill test configuration cannot exist** (`nilpotent-jordan-certificates-flatten-to-minors`,
    Section 2). If `u^k = 0` and `f <~ u`, then `f^((+)k) <~ I_((k-1)n)` through minors alone. For
    `diag(1,1,1,0) <~ u` with `u^3 = 0` in `M_4(W)` this gives `I_9 <~ I_8`, so `W` fails the rank condition.
    Weak finiteness is not needed. This is the rank-level retract lemma asked for above.
  - **Consequence.** The outer s-rank already obeys `rho^s(u) <= (k-1)n/k`. So the free Jordan data of
    order-three unipotents never makes the choices inconsistent one element at a time.
  - **Exact form of (U1b)** (`k0-state-extends-to-rank-function-iff-triangular-monotone`, Section 4). `W`
    carries a rank function iff some state on `(K_0(W), [W])` is monotone for the triangular preorder on
    idempotents.
  - **Sufficient condition** (`outer-state-rank-is-rank-function-iff-subadditive`, Section 3). Some state has
    a subadditive outer s-rank.
  - **What remains.** A violation needs a triangular step whose carried minor mixes the two diagonal
    blocks, or both with one padding block. Separated steps are removable
    (`separated-triangular-steps-flatten-to-minors`), and no mixed certificate is known over any ring with
    the rank condition.
- 2026-09-12 `w6-upg-separate` (artifact `research/artifacts/two-root-certificates-separate-2026-09-12.md`).
  - **Census: no mixing step.** [TRI] Theorem A and D.2, [RR] Propositions 6, 8 and Corollary 9,
    push-through and the rank-gate counting step contain no triangular step. The only triangular steps in the
    two-root defect arguments are the Frobenius steps behind the commuting Jordan bound. Those flatten on
    idempotent minors (`commuting-jordan-certificates-flatten-to-minors`).
  - **Transfer.** The gate criterion and the characteristic-three lower bounds hold for matrix states
    (`two-root-gate-lower-bounds-hold-for-matrix-states`), and matrix states exist iff the rank condition
    holds.
  - **Why this does not decide (U1b).** A rank function on `W` must also obey Jordan upper bounds on the values
    of non-idempotents such as `D`, `N_12` and `P_k`. Matrix states can break those bounds (Example 3.3:
    `d(u) = 1` on `F_3[u]/(u^3)`), and idempotent-minor flattening does not reach values. Still OPEN.
  - **Next test.** Does `D` have a nonzero idempotent minor over `W`? If not, no state bounds the rank of `D`
    from below.
  - **Rank condition without rank functions.** No such ring is recorded locally. The literature was not read.
- 2026-09-12 `w7-matrix-state-deficit` (artifact `research/artifacts/matrix-state-deficit-item-two-2026-09-12.md`,
  Sections 5–6).
  - **Next test (idempotent minors of `D`): not decided.**
    - `D` has a nonzero idempotent minor over a ring iff `WD` contains a nonzero idempotent (Lemma 5.1).
    - For any quotient `W` of `S_-`, either `WDW = W`, giving `I_1 <~ D^((+)k)` for some `k`, or `W/WDW` is nonzero
      and fails the rank condition (Lemma 5.2). The second case uses Theorem 2.3.4 of the `w6-upg-separate`
      artifact, with the empty prefix.
    - Over `S_-` the second case holds: the evaluation into `L_(F_3)(1,2)` kills `D` and sends `eps_-` to `1`. For
      the largest weakly finite image neither case is decided.
  - **Rank condition without rank functions: posed as open in the literature.**
    - Hung–Li (arXiv:2201.01432) ask whether the rank condition implies a Sylvester rank function (Question 3.4),
      and whether stable finiteness does (Question 3.5).
    - They note a positive answer for von Neumann regular rings.
    - A positive answer to Question 3.5 would give (U1b).
    - No counterexample ring was found. Schofield's Chapter 7 and the Jaikin-Zapirain survey were not read.
  - **Deficit side.** The matrix-state deficit target is equivalent to the counterexample
    (`ternary-anti-central-matrix-state-defects-have-a-strict-deficit`). So no proof of it can serve as a source of a
    mixing step for (U1b) without first proving the counterexample.
- 2026-09-12 `w7-wdw-fullness` (artifact `research/artifacts/weakly-finite-image-defect-fullness-2026-09-12.md`; all
  held OPEN).
  - **Lemma 5.2, case 2, identified.**
    - `S_- D S_-` is the kernel of the Leavitt evaluation
      (`ternary-anti-central-defect-ideal-is-the-evaluation-kernel`). So for every quotient `W`, `W/WDW` is `0` or
      `L_(F_3)(1,2)`.
    - For the largest weakly finite image, case 1 is `ternary-defect-is-full-in-largest-weakly-finite-image`, which
      refutes Gottschalk at stage one. Case 2 maps `W_max` onto `L_(F_3)(1,2)`.
  - **From `D^((+)k)` to `D`: fails in general.**
    - A weakly finite skew Laurent domain over `F_3` has a full non-unit `D = 1 + x`, with `I_1 <~ D^((+)3)` and no
      nonzero idempotent minor (artifact Proposition 4.1).
    - Artinian rings pass by Brauer's lemma, so finite-block models do not see the gap.
  - **Special structure of `S_-` recorded.**
    - `W_max ≅ M_2(ē W_max ē)`, with a unital `W_max -> ē W_max ē`, so the halving acts on states of `W_max`.
    - Nonzero weakly finite images are faithful on `G`.
  - **Where it stops.** Neither case forces or forbids a rank function on `W_max`. No mechanism for Question 3.4 on
    `S_-`.
