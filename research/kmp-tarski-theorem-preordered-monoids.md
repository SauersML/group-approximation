---
rg: 2
id: kmp-tarski-theorem-preordered-monoids
kind: claim
title: Tarski's theorem for preordered abelian monoids - a nonzero element is non-paradoxical iff some state takes the value 1 on it (Kwasniewski-Meyer-Prasad Corollary 2.16)
distinct_from:
  kmp-plain-paradox-groupoid-dichotomy: that imports the groupoid C*-algebra dichotomy from the same paper; this is the monoid-level Tarski theorem with no groupoid or C*-algebra.
---

**Import (Kwaśniewski–Meyer–Prasad, arXiv:2502.17190v3, 28 Jul 2026).**

In a preordered abelian monoid `S`:
- `x` is *stably dominated* by `y`, written `x <s y`, if `(n+1)x ≤ ny` for some `n ≥ 1`. A nonzero `x` is
  *paradoxical* if `x <s x` (Definition 2.6).
- A *state* is an additive, order-preserving map `ν : S → [0, ∞]` with `ν(0) = 0` (Definition 2.9).

**Corollary 2.16 (Tarski's Theorem).** A nonzero `y ∈ S` is not paradoxical iff there is a state `ν` with `ν(y) = 1`.

This applies in particular to the Murray–von Neumann monoid `V(R)` of a unital ring with the algebraic preorder.

**Review (un-verify, 2026-09-13): PASS (import).** Definitions 2.6 and 2.9, Remark 2.10 and Corollary 2.16 checked verbatim against the text of arXiv:2502.17190v3 (28 Jul 2026). See `research/artifacts/un-review-2026-09-13-part2.md` §1.
