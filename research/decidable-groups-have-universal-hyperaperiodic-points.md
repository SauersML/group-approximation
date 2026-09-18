---
rg: 2
id: decidable-groups-have-universal-hyperaperiodic-points
kind: claim
title: Every infinite finitely presented group with solvable word problem has a computable hyperaperiodic point that is universal at the origin with computable modulus
distinct_from:
  decidable-fp-groups-have-effective-minimal-free-subshifts: that is (M2), which asks for a minimal free effective subshift and implies this statement (a point of such a subshift works); this asks only for one computable point whose orbit closure is free and which exhibits all its own patterns near one position, with no minimality or recurrence elsewhere.
  gjs-countable-groups-have-free-minimal-subflows: that gives hyperaperiodic points non-effectively; this needs a computable one with a computable universality modulus.
---

**OPEN.** This is the premise of `free-products-with-z-inherit-m2-from-universal-points`.

**Statement.** Let `A` be an infinite finitely presented group with solvable word problem.
Then there are a finite alphabet `C`, a computable `y ∈ C^A` and computable functions `R`,
`R_U` such that:
- **(H):** for each `s ∈ A∖{1}` and each `g ∈ A`, some `a ∈ B(R(s))` has
  `y(ag) ≠ y(asg)`;
- **(U):** every radius-`r` pattern occurring anywhere in `y` occurs at some `g` with
  `r < |g| ≤ R_U(r)`.

Here `R` only needs to exist; computability is not used by the theorem.

**Known instances.**
- *Every group satisfying (M2).* Any point of an effectively closed minimal free subshift is
  hyperaperiodic and uniformly recurrent, and the decidable language gives a computable
  `R_U`. By `effectively-rf-groups-have-effective-minimal-free-subshifts`, this covers every
  infinite fp residually finite group and every infinite f.g. linear group.
- *Not known here:* any infinite group that is not residually finite and has no (M2)
  instance. That includes `St_10(R_L)`, Thompson's `V`, and Clapham envelopes of simple
  Kazhdan groups.

**How it relates to (M2), and how hard it is.**
- *(U) plus a central modulus gives minimality.* If `y` also has central repetitivity (every
  central disk recurs within a computable radius of every point), then (U) makes every
  pattern recur uniformly. So for the computable strongly aperiodic, strongly repetitive
  points of Álvarez López (Attempt 7 of `decidable-fp-groups-have-effective-minimal-free-subshifts`),
  (U) is *equivalent* to the missing global modulus, i.e. the seam problem. It is not easier
  there.
- *What `free-products-with-z-inherit-m2-from-universal-points` removes* is the need for any
  repetitivity. A point for (U)+(H) may be deliberately non-repetitive: a "library region"
  near the origin, with a far structure that only reuses library patterns. So all the seams
  can be concentrated at one place, which no centrally repetitive hierarchy allows.
- *A sufficient condition.* Suppose `A` has an effectively closed strongly aperiodic subshift
  `Z` with decidable language and a computable point. Suppose also that `Z` has a
  *separated gluing* property: any finite family of `L(Z)`-patterns placed pairwise far apart
  extends to a point of `Z`. Then gluing one sample of each `L_r(Z)`-pattern near the origin
  gives (U)+(H).
  - Strong irreducibility would give such gluing, but over `Z^d` it forces periodic points,
    so the gluing has to be genuinely non-uniform.
- (U) constrains ONE position. The swarm's local-lemma kill,
  `local-lemma-cannot-certify-multiscale-recurrence` (bh-free-37, b81707e5f), concerns
  recurrence events at every position at infinitely many scales, so it does not apply
  directly.
- A natural design:
  - freeze, near the origin, a sample of every "locally valid" pattern of an aperiodicity
    constraint system of ABT type;
  - fill the rest by a computable local lemma (Rumyantsev–Shen, context only).

**Where that design stops (Attempt 1, bh-g1-effective, 2026-09-18).**
- (U) needs every pattern of the FINAL `y` to be among the samples. So the library must
  contain every window of every completion, i.e. it must be closed under the completion
  process.
- Take the library to be all locally valid windows. Freezing a locally valid sample can
  leave a straddling constraint whose frozen part has no disagreement while its free part is
  a single position.
  - For large alphabets each such event is unlikely.
  - But there is one such event for every `s` with `R(s)` large, and the dependency sum over
    all `s` diverges.
- Requiring "strong" validity instead (every constraint with a θ-fraction of its region
  inside already satisfied inside) makes the local lemma work. But then windows of the
  completion need not be strongly valid, so they may be missing from the library.
- In groups of exponential growth, "a θ-fraction of a ball inside another ball" is badly
  behaved near the boundary, so a growth-independent choice of θ is not available.

Both halves are recorded; no refutation is claimed.

**Lesson for general BH.** After `free-products-with-z-inherit-m2-from-universal-points`,
the (M2) gate for the master route is exactly this single-position universality statement.
The open core is a *library-closed* completion scheme: a finite library of patterns per
scale, closed under the completion that produces the far-away part of `y`. That is the
same small-library, cross-depth locality that `annular-free-product-germ-hosts-are-not-finitely-presented`
(bh-free-22) and the master route's conjecture G2-fp ask for, now in its simplest
(single-point, zero-dimensional) form.
