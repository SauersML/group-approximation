# Referee report (gq-referee-b, scope lens): frame designs for the ring gate are bracketed

**Reviewed.** `frame-designs-for-the-ring-gate-are-bracketed` and its `-proof` (lane gq-infinite-primes, 48c3f0945),
read on origin/main. I checked each item against the cited node as I refereed it.

**Verdict: FAIL as written, repairable.** Items 1–6 and item 8 match their nodes. Two statements do not hold as
worded:
- the Statement's "fails the K-budget in cases 2–7" is wrong for the inhomogeneous branch of item 7;
- the completeness claim "A frame design escapes items 1–8 only if it is one of (a)–(f)" omits at least two cases.

The corrections are listed below. No mathematics needs to change, only the bookkeeping.

## Items against their nodes

| Item | Result | Detail |
|---|---|---|
| 1 | **Match** | The frame node needs `R` simple and `φ` injective. Both are in the Frame-designs definition and the widened gate. |
| 2 | **Match** | Item 1 of the uhf node works over any `B`, then `rational-k1-detection`. |
| 3 | **Match** | This is the index-1 case of the uhf node, item 3. Index `≠ 1` is item 2. |
| 4 | **Match** | This is the post-fix text (0c5da8d82): ranks divisible by `j`, and all ranks when unit-class projectives are free. It also needs `[1_B]` of infinite order, which is (R1). Item 3a was not re-refereed by me. |
| 5 | **Match** | Corner node 7(a)–(c). |
| 6 | **Match** | The mixed-degree node, conditional on (CSL). Bullet 1 of (CSL) is derivable from ABC; see my report on that node. |
| 8 | **Match**, with fixes W2–W4 | The five register results. |

**Item 8 in detail.** The qualification that "the first three exclude divisibility; the last two exclude simplicity"
is accurate for the five nodes.
- `single-register-rings-divide-unit-at-finitely-many-primes` excludes divisibility.
- `top-determined-register-rings-cannot-divide-the-unit` and `dilation-letters-cannot-divide-the-unit-class` do so too,
  by their titles; I have not refereed them.
- `register-comparison-presentations-are-not-simple` (I refereed it PASS, 86f70e504) and
  `sl2-vacuum-hosts-admit-verma-type-modules` exclude simplicity.

## Corrections

- **W1 (item 7 and the Statement).** The inhomogeneous branch of `unit-symmetries-of-a-core-are-graded-or-inessential`
  is a **reduction**, not a failure of the budget.
  - It shows that `R` is free of finite rank over a finitely generated core `A`.
  - The gate conditions pass to `A`, with `m[1_A]` in place of `[1]`.
  - The design then fails or succeeds with `A`, so the symmetry is inessential.
  - Change "fails the K-budget in cases 2–7" to "fails in cases 2–6 and in the graded branch of case 7; in the
    inhomogeneous branch of case 7 it reduces to its core".
  - Add the reduced cores to "What remains" as a pointer.
- **W2 (the Statement header for item 8).** "In case 8 it fails gate condition 4" contradicts the item-8 body, where the
  last two sub-items fail simplicity. Align the header with the body.
- **W3 (the proof's `requires`).** `sl2-vacuum-hosts-admit-verma-type-modules` is cited in item 8 but missing from the
  `requires` list.
- **W4 (item 8, (P)).** "Proved in the spine form" should add the scope amendment: with every `δ_n ∈ B⁺`
  (852a0771f / db70a3dbb).
- **W5 ("What remains", a missing case).** Item 5 needs a positive fixed vector that spans `[1_B]` modulo
  `im(1 − A)`. Item 6 needs `A` invertible, a corner isometry, and (CSL). So the following design escapes both, yet is
  not listed in (a)–(f):
  - a multi-type matricial design with a positive fixed vector `v ≥ 0` that does **not** span `[1_B]` modulo
    `im(1 − A)`, that is, `rank coker(1 − A) ≥ 2`;
  - with `A` singular, or no corner isometry, or (CSL) failing.

  In that design, the corner node's dichotomy leaves `Λ_e` not finitely generated, but that does not reach
  `ker(Q^x → K_1(R))` without the relation `t[1] = n[e]`. (c) mentions only *non-positive* fixed classes. Extend (c)
  to "every multi-type matricial design not covered by items 5–6". This also covers the corner node's own "Open" line,
  "`rank coker(1 − A) ≥ 2` without the span condition".
- **W6 ("What remains", a second missing case).** Item 4 assumes `sr(B)` finite, which is (R2). Rank-one bases with
  infinite stable range are not listed. (d) covers only the rank-prime-to-`j` case.
  - Add "(g) rank-one bases with infinite stable range".
  - Rank-one bases with `[1_B]` torsion in `K_0(B)` are already excluded by item 2's argument, since `[1_R]` is then
    torsion.

## Items (a)–(f) as listed

Each matches the Open lines of its node:
- (a) is gate Attempt 12, case 2;
- (b) is the rank `≥ 2` non-matricial, non-register case;
- (c) is to be extended per W5;
- (d) is the rank-one fix;
- (e) is the ungraded quotients;
- (f) is the non-`σ`-simple cores.

The closing sentence, that stably finite IBN rings are outside the frame class, is fine as a pointer.
