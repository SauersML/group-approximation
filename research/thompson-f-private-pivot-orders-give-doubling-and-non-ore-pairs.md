---
rg: 2
id: thompson-f-private-pivot-orders-give-doubling-and-non-ore-pairs
kind: claim
title: An order on the positive monoid of F giving every element two private points in S·m makes S doubling, and with nonvanishing minors gives an explicit non-Ore pair
distinct_from:
  thompson-f-nonamenable-iff-some-monomial-set-doubles: that says non-amenability is equivalent to doubling of some monomial set; this gives a local combinatorial sufficient condition for doubling, and turns it into explicit non-Ore pairs.
  monoid-ring-no-common-multiple-iff-harmonic-splitting: that is the dual criterion for a non-Ore pair; this is a triangular certificate for injectivity of (u, v) -> a u − b v.
  thompson-f-ore-obstructions-must-see-finite-support: that rules out leading-term obstructions for one bi-order; this uses a total order on each degree layer only to pick private points, not to take leading terms.
artifacts:
  - research/artifacts/hl-f-p22-invariant-2026-09-13.md
---

**ESTABLISHED** through `thompson-f-private-pivot-orders-proof` (direct proof; not independently
reviewed; no priority claimed).

Let `M` be the positive monoid of `F`, `S ⊆ M` a finite set of monomials of one degree, and `<` any
total order on `M`. For `w ∈ M` the set `{m : w ∈ S m}` is finite; let `m_<(w)` be its maximum. Call `w`
*private for `m`* when `w ∈ S m` and `m_<(w) = m`.

1. **Doubling.** If every `m ∈ M` has at least two private points in `S m`, then `|S Y| ≥ 2|Y|` for every
   finite `Y ⊆ M`. By item 1 of `thompson-f-nonamenable-iff-some-monomial-set-doubles`, `F` is then not
   amenable.
2. **Explicit non-Ore pairs.** Suppose that for every `m` two private points `s_1 m ≠ s_2 m` are chosen,
   and `a = Σ α_s s`, `b = Σ β_s s` in `K[S]` satisfy `α_(s_1) β_(s_2) − α_(s_2) β_(s_1) ≠ 0` for every
   pair `(s_1, s_2)` that occurs. Then `a u = b v` with `u, v ∈ K[M]` forces `u = v = 0`.
3. **Natural orders fail at once for `S = S_(3,5)`.**
   - Lexicographic, reverse-lexicographic and sum-then-lex orders on normal forms, and their reversals,
     all leave some degree-one element with a single private point.
   - Increasing orders fail at `m = x_0`; decreasing orders fail at `m = x_4`.
   - This is an exact computation on MSI, recorded in the artifact.

**Relation to the root.** An order satisfying item 1 for `S_(3,5)` would prove `thompson-f-is-not-amenable`.
No such order is known. Item 3 rules out the natural lexicographic families, so a certificate of this shape
needs a non-local order.
