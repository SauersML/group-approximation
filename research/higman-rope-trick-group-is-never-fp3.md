---
rg: 2
id: higman-rope-trick-group-is-never-fp3
kind: claim
title: "The Higman rope-trick group of an infinite one-relator-quotient is never of type FP_3(Q)"
invalidates:
  - type-fn-hosts-via-higman-rope-trick
---

Let `G = F/R` be a quotient of a free group with `G` infinite and `R != 1`,
and let `Hig_i(G)` be the Higman rope-trick group used to embed `G` into a
group with better finiteness. Then `H_3(Hig_i(G); Q)` is infinite
dimensional, so `Hig_i(G)` is never of type `FP_3(Q)`, a fortiori never of
type `FP_3`, `F_3`, or `F_infinity`.

Source: Francesco Fournier-Facio and Matthew C. B. Zaremsky, *Finiteness
properties and Higman's rope trick*, arXiv:2607.21727 (2026-07-23),
Theorem B. (This post-dates the July 12, 2026 problem list.)

**Significance for Zaremsky Problem 1.1.** The rope trick is the natural
universal device for embedding an arbitrary group into an overgroup while
trying to raise finiteness type. Theorem B shows it stops at `FP_2`: the
rope-trick overgroup is never `FP_3`. So this construction cannot answer the
`F_3` (or `F_{n+1}`, `F_infinity`) embedding question, and it is a concrete
obstruction to the most natural positive attempt. It bounds the method, not
all overgroups, so Problem 1.1 remains open; it is recorded on
`some-type-fn-group-embeds-in-no-type-fn-plus-1-group` as the reason the
obvious construction fails.

The same paper's Theorem A gives a reduction in the *positive* direction
(if every finitely generated recursively presented group embeds in a
recursively presented `FP_n` group, then every finitely presented group
embeds in an `F_n` group); its Questions 1.3 and 1.4 restate the `F_3`/`F_∞`
and `FP_3`/`FP_∞` embedding questions. Those belong to the positive-side lane.

Provenance note: the exact statement of Theorem B was relayed from the
literature-status lane and should be confirmed line-by-line against the
arXiv source by a verifier before this node is used as a solved-problem
input.
