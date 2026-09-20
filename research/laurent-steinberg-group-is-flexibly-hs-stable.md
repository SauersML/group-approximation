---
rg: 2
id: laurent-steinberg-group-is-flexibly-hs-stable
kind: claim
title: For some n >= 3 and some prime power q >= 3, the Steinberg group St_n(F_q[t,t^-1]) is flexibly Hilbert--Schmidt stable
distinct_from:
  free-algebra-elementary-group-is-flexibly-hs-stable: that asks for stability of E_n of a free algebra; this asks only for stability of one of its relative quotients (free-algebra-relative-quotient-is-laurent-steinberg), so it is strictly implied by that claim.
  sl3-laurent-f2-is-flexibly-hs-stable: that is SL_3 over F_2[t,1/t], where K_2 vanishes and the group is linear and residually finite; this is the Steinberg group for q >= 3, which carries the invisible central symbol {t,a}.
  laurent-sl4-matricially-stable: that is operator-norm matricial stability of the linear group SL_4(F_q[t,t^-1]); this is flexible HS stability of its finite central extension St_n(F_q[t,t^-1]).
  hyperlinear-flexibly-hs-stable-group-is-residually-finite: that is the general obstruction; this is the stability hypothesis for one explicit non-residually-finite Kazhdan group.
---

**OPEN.** For some `n >= 3` and some prime power `q >= 3`, the group `St_n(F_q[t,t^-1])` is
flexibly HS stable in the Dogon--Vigdorovich sense, as in
`free-algebra-elementary-group-is-flexibly-hs-stable`.

**Why it matters.** `St_n(F_q[t,t^-1])` is finitely generated, Kazhdan and not residually finite
(`laurent-steinberg-groups-are-deligne-type`). So by
`hyperlinear-flexibly-hs-stable-group-is-residually-finite`, this claim makes it non-hyperlinear.
That is the goal route `nonhyperlinear-via-laurent-steinberg-flexible-stability`.

**Relation to the free-algebra claim.** By route
`laurent-steinberg-stability-from-free-algebra-stability`,
`free-algebra-elementary-group-is-flexibly-hs-stable` at `(A, n)` implies this claim at the same
`n` and at every `q >= 3` of characteristic `p` (for `A = F_p`), or at every `q >= 3` (for
`A = Z`). This claim is the weaker hypothesis. It concerns one explicit finite central extension of
an S-arithmetic lattice, by `Z/(q-1)`, rather than a universal lattice.

**Refutation screen.** Any of the following refutes this claim at `(n, q)`, and with it the
free-algebra claim at the matching `(A, n)`:
- a proof that `St_n(F_q[t,t^-1])` is hyperlinear, or even `||.||_2`-approximated;
- an asymptotic representation of it that no padded genuine representation rounds.

For `q` odd the group is of Deligne-type, so this is the positive-characteristic analogue of the
open question whether Deligne's cover of `Sp_(2g)(Z)` is hyperlinear.

## Attempts

- **Where the obstruction sits (2026-09-20, `swarm-0917-w23-w23-nh-follow`).** Every
  finite-dimensional unitary representation of `St_n(F_q[t,t^-1])` kills `K_2 = ⟨c⟩`.
  - The image of a genuine representation `λ` is finitely generated and linear, hence residually
    finite (Mal'cev). Since `c ∈ ker_RF`, this gives `λ(c) = 1`, and a corner `P*λP` sends `c`
    to `P*P = 1`.
  - Stability therefore forces every asymptotic representation `σ_m` to satisfy
    `||σ_m(c) - 1||_2 -> 0`.
  - So a necessary condition is that the symbol is invisible in every HS model. That condition
    alone already rules out hyperlinearity, because a separating family would keep
    `||σ_m(c) - 1||_2` bounded below. This is the RF node specialised to one explicit element.
- Not attempted: a direct rounding argument. It would have to use more than property (T) and a
  regular limit trace, for the reason recorded under "Why a proof is hard" on the free-algebra
  claim.
