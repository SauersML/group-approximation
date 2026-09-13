---
rg: 2
id: thompson-f-nonamenable-iff-some-monomial-set-doubles
kind: claim
title: Thompson's group F is non-amenable iff some set of positive monomials of one degree doubles every finite subset of the positive monoid
distinct_from:
  thompson-f-amenable-iff-group-ring-is-ore: that turns amenability into the Ore condition for all pairs in K[F]; this turns it into a counting property of the monomial sets S_(m+1,m+d+1) alone, which decides whether the survey's cardinality method can solve P_(d,m).
  thompson-f-is-not-amenable: that is the named open problem; this is an equivalent reformulation of it and proves neither answer.
  thompson-f-evacuation-schemes-need-capacity-three: that bounds evacuation capacities on one Cayley graph; this is an exact expansion criterion in the positive monoid.
artifacts:
  - research/artifacts/thompson-f-monomial-doubling-2026-09-13.md
---

**ESTABLISHED** through `thompson-f-nonamenable-iff-some-monomial-set-doubles-proof`
(direct proof from standard facts; not independently reviewed; no priority claimed).

Let `M` be the positive monoid of `F`, with normal forms `x_(i_1) ... x_(i_d)`,
`i_1 <= ... <= i_d`, and relations `x_j x_i = x_i x_(j+1)` for `i < j`. Following
V. Guba, *Amenability problem for Thompson's group F: state of the art*, arXiv:2305.07113v4,
§3, `S_(m+1,m+d+1)` is the set of normal forms of degree `d` with `i_1 <= m`,
`i_2 <= m+1`, ..., `i_d <= m+d-1`. Problem `P_(d,m)` asks for nonzero `u, v` with `a u = b v`
for given `a, b` in `K[S_(m+1,m+d+1)]`. Call a finite `S ⊆ M` *doubling* if `|S Y| >= 2|Y|`
for every finite nonempty `Y ⊆ M`.

1. If `F` is amenable, no finite `S ⊆ M` is doubling.
2. If `F` is not amenable, then `S_(m+1,m+d+1)` is doubling for some `d, m >= 1`.
3. If a finite `S ⊆ M` is not doubling, then for every field `K` and all nonzero `a, b` in
   `K[S]` there are nonzero `u, v` in `K[M]` with `a u = b v`, supported in one finite `Y`
   with `|S Y| < 2|Y|`.

**Consequence.** `F` is amenable iff the cardinality method (item 3) solves every Problem
`P_(d,m)`. So a proof that the method fails for a single `(d,m)` is already a proof of
`thompson-f-is-not-amenable`. In particular, showing that the nine monomials of `P_(2,2)`
(`S_(3,5)`) double every finite subset of `M` is exactly as hard as a non-amenability
proof restricted to that set, and no easier than the root.

**Relation to the literature.** Item 3 is the cardinality argument the survey uses for
`P_(1,m)` and `P_(2,1)` (survey Theorems `xmy`, `s24`). The survey quotes Donnelly
(Integers 2014) for the criterion "`F` is non-amenable iff there is `ε > 0` with
`|A Y| >= (1+ε)|Y|` for all finite `Y ⊂ F`, `A = {x_0, x_1, x_2}`". That source was not
read here, and item 2 is proved without it.

**Scope.** This proves neither answer. The exact computation of how close `S_(3,5)` comes
to doubling on finite universes is `thompson-f-monomial-doubling-ratio-is-a-finite-computation`
and the artifact.
