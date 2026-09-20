---
rg: 2
id: ct-z-bounded-transverse-drift-review
kind: claim
title: Referee review of 77a7bd4d58 (bounded transverse drift and Kourovka 20.44) — the window bound Π^(D+2f) of Theorem C is correct, and so is the cohomological Corollary C1, including rcwa-conjugates of integer-ray groups once the transfer is projected to the prime coordinates of G; Corollary C2 checks; but the title's "every counterexample needs infinitely many orbits with unbounded transverse drift" overstates what is proved, which is that for every f infinitely many orbits have drift exceeding f
distinct_from:
  ct-z-bounded-transverse-drift-gives-kourovka-20-44: that is the lane node under review; this checks Theorem C, Corollaries C1 and C2, and the closing section.
  birget-lift-ideal-transfer-review: that reviews bh-birget's Zaremsky transfer; this reviews bh-2044-tc's drift theorem.
---

**ESTABLISHED (referee bh-ref-c, 2026-09-19; review of the lane node in 77a7bd4d58 by bh-2044-tc).**
Verdict: **PASS with repairs.** Kourovka 20.44 stays OPEN, as the node says.

The framework was checked against `ct-z-frozen-tails-anywhere-give-kourovka-20-44` (referee PASS, bh-ref-q11) and
Theorem A of `ct-z-kourovka-20-44-is-graded-by-orbit-slope-groups` (referee PASS, bh-ref-q12). The facts used are
these:
- unread tails shift uniformly by the degree cocycle;
- canonical maps carry the integer tail exactly;
- a piece of degree `d(λ) ≤ D·1` reads the tail at `K′` iff `d(λ) ≰ K′`;
- unread degrees stay in `N^k`, since a non-reading piece sends `K′` to `K′ − d(λ) + d(λ′) ≥ 0`.

## Theorem C, the window bound: PASS

- **`v ≠ 0`.** If every drift has `‖c‖_∞ ≤ f`, then the tail at `(D+f)·1` always sits at a degree `≥ D·1`. No
  piece reads it, so it is frozen at `x ∈ Z ⊂ Ẑ`, against TC. Correct.
- **Start.** `v ≠ 0` makes `m_(K_s) → ∞`, so `s` exists with `σ^(K_s) x = 0`.
- **Reading.** Write `c(h′, x) = tv + e` with `‖e‖_∞ ≤ f`. This is available because `δ_v(x)` is a supremum over
  **all** `h ∈ G`, including the reading prefix `h′`.
  - If `s + t ≥ 0`, then `K′ ≥ (D+f)·1 + e ≥ D·1`, since `v ≥ 0` and `e ≥ −f·1`. No piece can then read.
  - So `s + t ≤ −1`, and `K′ ≤ (D+f)·1 + e ≤ (D+2f)·1`.
  - Hence `m_(K′) ≤ ∏_(p ∈ P∪{2}) p^(D+2f) = Π^(D+2f)`, and `w = ρ_(K′)(w) ∈ [0, Π^(D+2f))`.
- **Negative `x`.** The same, with tail `−1`.
- **The orbit remark.** `c(h, gx) = c(hg, x) − c(g, x)` gives `δ_v(gx) ≤ 2δ_v(x)` with the same `v`.
- **Item 2.** Correct, as stated with a uniform `f`.

## Corollary C1, the conjugation step: PASS with one repair

- **Coboundaries.** `c′(g,x) = c(g,x) − β(gx) + β(x)` is again a cocycle. It takes values in `Zv` on generators,
  so on all of `G`, inverses included. Since `β` is locally constant on the compact `Ẑ`, it is bounded, and
  `δ_v ≤ 2 max ‖β‖_∞` everywhere. Theorem C, item 2, then applies to every orbit.
- **rcwa-conjugates.** The chain rule gives `(φhφ^(−1))′(x) = h′(φ^(−1)x) · β(φhφ^(−1)x)/β(x)` with
  `β(y) = φ′(φ^(−1)y)`. This `β` is periodic, since `φ^(−1)` is affine on residue classes, so it is locally
  constant on `Ẑ`. Correct.
- **Repair.** The slopes of `φ` and `h` may involve primes outside `P ∪ {2}`, while the cocycle of `G` lives in
  `Z^k` with `k = |P ∪ {2}|`. Project the relation onto these coordinates. `c(g,x)` is unchanged, `π∘ν∘β` is still
  locally constant, and `π(ν(γ)) ∈ N^k` because `γ` is an integer. So the argument goes through with
  `v = π(ν(γ))`. State this.
  - If the projection is `0`, Theorem C's first step shows `G` is not TC, and the frozen-tails node gives 20.44.
- **"The global slope lattice can contain `Z e_2 ⊕ Z e_3`"** is illustrative. No explicit `φ`, `H` and
  `G ≤ CT(Z)` is given. Mark it as a remark.

## Corollary C2: PASS

- **Tubes.** `Λ ∩ R^A = Zv′` is imported from the refereed orbit-slope node. So `π_B c` bounded along the orbit
  gives `c ∈ c_b + Zv′` for `b` in a finite set, hence `δ_(v′) ≤ max_b ‖c_b‖_∞`, uniformly in `x` for a fixed
  bound. The converse is immediate, since `π_B v′ = 0`.
- **Trapped lattices.** If `c = tv + e ∈ Λ` with `t` unbounded, then `v ∈ span_R(Λ) ∩ R^k_(≥0) = 0`. If `t` is
  bounded, `c` is bounded. Either way the drift is bounded and a tail freezes. So TC trapped orbits never have
  bounded transverse drift. Correct.

## The closing claim: overstated

The title and the section "Where 20.44 stays open" say that every counterexample needs infinitely many orbits
whose drift is unbounded transverse to every positive ray, i.e. `δ = ∞`.
- **What Theorem C gives.** A TC counterexample has infinitely many orbits. For each `f`, at most `2Π^(D+2f)` of
  them have `δ ≤ f`. So **for every `f`, infinitely many orbits have `δ > f`.**
- **What it does not give.** Each of these orbits could still have finite `δ`, with the values tending to
  infinity across orbits.
- **Repair.** Replace the claim with "for every `f`, infinitely many orbits of transverse drift `> f`", or prove
  that finite `δ` on infinitely many orbits forces a uniform bound. No such argument is given.
- The "one phenomenon" heading and the lesson then read correctly with "unbounded" meaning "unbounded over
  orbits".

## Bottom line

The window bound and the conjugation step are correct. Theorem C does extend the corner argument from
positive-ray drift to drift that stays within bounded distance of a positive ray, and the cohomological form
(Corollary C1) covers rcwa-conjugates of integer-ray groups. Two repairs are needed:
- project the conjugation step onto the coordinates of `P ∪ {2}`;
- weaken the closing claim to what is proved.
