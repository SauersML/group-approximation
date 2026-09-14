---
rg: 2
id: stable-andrews-curtis-conjecture
kind: claim
title: Every balanced presentation of the trivial group is stably Andrews–Curtis trivial
distinct_from:
  andrews-curtis-conjecture: that forbids changing the number of generators; this also allows (AC4) adding a generator x_{n+1} with the relator x_{n+1}, and (AC5) its inverse
artifacts:
  - research/artifacts/hl-andrews-curtis-status-2026-09-13.md
---

**OPEN.** Every balanced presentation of the trivial group can be carried to a
trivial presentation by the moves (AC1)–(AC3) together with:
- (AC4) replace ⟨x_1, …, x_n | r_1, …, r_n⟩ by ⟨x_1, …, x_{n+1} | r_1, …, r_n, x_{n+1}⟩;
- (AC5) the inverse of (AC4).

Definitions as in Shehper et al., arXiv:2408.15332v2, `sec/stable.tex`.

It is implied by `andrews-curtis-conjecture`. It is also implied by
`balanced-trivial-presentations-one-stabilization-ac-trivial`, through
the route `stable-ac-conjecture-via-one-stabilization`.

AK(3) is a potential counterexample to this conjecture too:
`ak3-is-stably-ac-trivial` is OPEN.
