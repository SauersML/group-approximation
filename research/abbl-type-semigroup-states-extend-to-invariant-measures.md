---
rg: 2
id: abbl-type-semigroup-states-extend-to-invariant-measures
kind: claim
title: Every state on the type semigroup of an ample second countable groupoid extends to an invariant Borel measure
---

Let `G` be an ample second countable groupoid and let `f : S(G) -> [0, ∞]` be a monoid homomorphism,
that is, a finitely additive invariant positive measure on the compact open subsets of `G^(0)`. Then
`f` extends to a `G`-invariant Borel measure `μ_f` on `G^(0)`. Its restriction to the union of the
compact open sets `K` with `f([1_K]) < ∞` is unique and regular.

Consequence used in `un-paradox`: if `G^(0)` is compact and carries no invariant probability measure,
no state on `S(G)` normalizes `[1_(G^(0))]`.

**Review (un-verify, 2026-09-13): PASS (import).** Lemma 2.3, the definition of F(S) and the presentation relations checked verbatim against arXiv:2001.00376v3. See `research/artifacts/un-review-2026-09-13-part3.md` §3.
