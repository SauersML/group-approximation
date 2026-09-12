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
