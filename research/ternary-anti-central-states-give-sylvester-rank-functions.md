---
rg: 2
id: ternary-anti-central-states-give-sylvester-rank-functions
kind: claim
title: If the ternary anti-central summand satisfies the rank condition, it carries a normalized Sylvester rank function
distinct_from:
  ternary-anti-central-states-force-nontrivial-rank-models: that asks a state to force a matricial rank model, steps U1 and U2 together; this is step U1 alone, a Sylvester rank function with no approximation requirement
  anti-central-state-obstruction-equals-stable-finiteness: that shows a state exists iff the unit class is not nonpositive; this asks that such a state be realized by a Sylvester matrix rank function
artifacts:
  - research/artifacts/strategist-neg-counterexample-plans-2026-09-12.md
---

**OPEN.** Let `S_- = eps_- F_3[L_(F_3)(1,2)^x]`. If `(K_0(S_-), [eps_-])` has a state, then `S_-` has a
Sylvester matrix rank function `N` with `N(eps_-) = 1`.

A state exists iff `[eps_-]` is not `<= 0`, that is, iff `S_-` satisfies the rank condition (no
`S_-^(n+1)` is a direct summand of `S_-^n`). So this claim asks that the rank condition on `S_-` yield a
normalized Sylvester matrix rank function.

**Why it matters.** A rank function always gives a state, so this claim is exactly what makes the two
statements coincide:
- `ternary-anti-central-unit-class-is-nonpositive` (the counterexample);
- `sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one` (no rank function on `S_-`).

So the linear ternary counterexample becomes a pure rank-function question, with no lifting of the corner
equation.

**Risk.** For general rings, the rank condition is not known here to give a Sylvester matrix rank function,
and it is plausibly false. Check the literature before a proof attempt: Malcolmson's criteria, Schofield's
*Representations of rings over skew fields*, and Jaikin-Zapirain's survey of Sylvester rank functions. A
general proof is unlikely, so a proof would need input specific to `S_-`, such as a `K_0`-order embedding
into a regular ring.

## Attempts

- 2026-09-12 `w3-strategist-neg`: proposed as step (U1) of Plan 1 (artifact Sections 2 and 4.4).
  - **First lemma to try.** A unital, `K_0`-order-embedding map from `S_-` into a regular ring (universal
    localization). Then states extend, and Goodearl's pseudo-rank correspondence gives rank functions.
  - **First kill test.** A ring satisfying the rank condition with no Sylvester matrix rank function, whose
    obstruction can be transported to `S_-`.
