---
rg: 2
id: non-weakly-sofic-iff-non-finite-field-linear-sofic-group
kind: claim
title: Some group is not weakly sofic iff some group is not linear sofic over finite fields
distinct_from:
  non-weakly-sofic-group-exists: that is the existence of a non-weakly-sofic group, which is open; this proves that it is equivalent to the existence of a group that is not linear sofic over finite fields, and establishes neither side.
  non-finite-field-linear-sofic-group-exists: that is the open existence statement on the linear side; this is the equivalence between it and the Glebsky--Rivera root.
  fg-simple-weakly-sofic-groups-are-finite-field-linear-sofic: that is the theorem for finitely generated simple groups; this is its existence-level consequence through Schupp's embedding.
---

**ESTABLISHED (2026-09-13, lane `ex3-weak-sofic-fg-dichotomy`, unreviewed)** by
`non-weakly-sofic-iff-non-finite-field-linear-sofic-group-proof`.

The following are equivalent:
1. Some countable group is not weakly sofic (`non-weakly-sofic-group-exists`, Glebsky--Rivera Conjecture 4.5).
2. Some countable group is not linear sofic over finite fields (`non-finite-field-linear-sofic-group-exists`).
3. Some two-generator simple group is not linear sofic over finite fields.
4. Some two-generator simple group is not weakly sofic.

**In words.** The most general finite-approximation question, arbitrary finite groups with arbitrary invariant lengths,
has the same answer as the rank-metric question over finite fields. The only approximations a counterexample must
defeat are normalized-rank models over finite fields.

**Credit.** The reduction to groups `PSL_n(q)` is Nikolov--Schneider--Thom's (arXiv:1703.06092v2, Theorem 4 and its
proof). Its combination with the adjoint and with Schupp's embedding is recorded in
`research/artifacts/fg-simple-weak-soficity-finite-field-linear-2026-09-13.md`, Section 4. The novelty check was
bounded, and experts may know the statement.
