---
rg: 2
id: leavitt-visible-colimit-factors-admit-k0-states
kind: claim
title: For every characteristic and arity the colimit Leavitt-visible factor admits a K_0 state
refuted_by:
  - leavitt-visible-cyclic-corner-is-full-on-some-host
  - ternary-anti-invariant-swap-corner-is-full
distinct_from:
  leavitt-visible-states-are-factorwise-and-colimit-stable: that is the established reduction of the state question to one colimit ring per characteristic and arity; this is the open assertion that every such ring has a state.
  projective-ternary-group-is-f3-linear-sofic: that is linear soficity of the ternary scalar quotient, whose rank functions live on the trivial-character factor; this asks for states on the Leavitt-visible factors, which have no finite-dimensional or augmentation-type maps at q = 3.
artifacts:
  - research/artifacts/ternary-anti-central-invariant-census-2026-09-12.md
---

**OPEN.** For every prime `p` and arity `d >= 2`, the colimit factor `A_iota(infinity)` of
`leavitt-visible-states-are-factorwise-and-colimit-stable` admits a state on `(K_0, [1])`.
Equivalently, it satisfies the rank condition.

**What it would do.**
- *Refutations.* By the colimit claim, it refutes `leavitt-visible-cyclic-corner-is-full-on-some-host`
  and every instance of it, including the ternary swap corner.
- *Scope.* It would close the linear cyclic-corner route to
  `some-finite-field-leavitt-unit-group-nonsurjunctive` in every characteristic, but it would not
  refute that root: a one-sided pair whose complement does not dominate the unit escapes it.

## Attempts

- *Natural sources of a state, and why each fails today.*
  - **Finite-dimensional images:** none at `q = 3`
    (`ternary-anti-central-summand-has-no-finite-dimensional-images`).
  - **Augmentation-type maps:** they vanish on the visible factor for `q > 2`.
  - **Rank functions from linear-sofic approximations with the scalars acting by `iota`:** these form
    the open `F_q`-linear soficity gate of the hosts. Property (T) gives no rank rounding over finite
    fields (`kazhdan-group-rank-models-admit-no-expander-decomposition`).
  - **Properly infinite images,** such as the Leavitt evaluation: they carry no state.
- *Where it dies.* No state is known on any finite stage `A_iota(q)` with `q > 2`.
