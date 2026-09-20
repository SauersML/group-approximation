---
rg: 2
id: ct-p-z-mixed-ray-frozen-tails-force-finite-orbits
kind: claim
title: "Kourovka 20.44 on a mixed-sign ray (e.g. slopes in (3/2)^Z): a frozen tail forces a finite orbit of size at most A(n), independent of the tail; so if any point of the profinite integers has a frozen tail, orbit minima have positive lower density, and a counterexample must be totally consumable (every orbit reads every depth)"
distinct_from:
  ct-p-z-ray-cocycle-subgroups-satisfy-kourovka-20-44: that is the positive-ray case, where frozen tails travel to infinity and are an invariant of infinite orbits; here the ray has mixed signs, frozen tails cannot travel, and they force finite orbits.
  ct-z-orbit-transversal-counterexamples-need-unbounded-orbits: that bounds orbits of bounded size in any CT_P(Z); here the orbits of frozen-tail points may be arbitrarily large, but their size is bounded by a function of the frozen degree alone.
---

**ESTABLISHED** (lane proof; **Referee PASS** bh-ref-d 2026-09-19, review `research/ct-p-z-mixed-ray-nodes-review.md` at a3b10b78df; the one discussion sentence it flagged is now marked heuristic). Elementary. No priority claimed.
- **What it settles.** Kourovka 20.44 (S. Kohl) for every finitely generated `G` on a
  mixed-sign ray in which some point has a frozen tail.
- **What stays open.** The totally consumable case (item 3).
- **Where it sits.** Between the positive-ray theorem
  (`ct-p-z-ray-cocycle-subgroups-satisfy-kourovka-20-44`) and Kohl's rank-2 group `G_T`
  (`ct-z-orbit-transversal-dichotomy-is-collatz-hard`).

## Setting

Notation, tracking and reading are as in `ct-p-z-ray-cocycle-subgroups-satisfy-kourovka-20-44`:
- degrees `n ∈ N^k`, `m_n = ∏ p^(n_p)`, and tails `σ^n`;
- tables with inverse tables, and the depth `D`;
- `C_n`, the set of points from which the tail at degree `n` can be read, a union of classes
  mod `M_n = m_n Π^D`.

**Mixed-sign ray.**
- Every piece has `d(μ) − d(λ) ∈ Zv`, where `v ∈ Z^k` has a positive and a negative coordinate.
- **Example.** `P = {3}` and `v = (−1, 1)`, with degrees written `(e_2, e_3)`. The slopes are
  then exactly the powers of `3/2`.
- **Generators.** These include the class transpositions `τ_{r(2m), s(3m)}` with
  `r(2m) ∩ s(3m) = ∅`, e.g. `τ_{0(4), 1(6)}`, and all slope-1 class transpositions.
- **Segments.** For `n ∈ N^k` put `Seg(n) = (n + Zv) ∩ N^k`. It is finite: if `v_i > 0 > v_j`,
  then `n + tv ≥ 0` forces `−n_i/v_i ≤ t ≤ n_j/|v_j|`.
  - Put `A(n) = Σ_{p ∈ Seg(n)} m_p`.
  - For `v = (−1, 1)`, `Seg(n)` is the level set `e_2 + e_3 = |n|`, and
    `A(n) ≤ (|n| + 1) 3^|n|`.

## Theorem

1. **Frozen tails force finite orbits.** Let `x ∈ Z`, and let `n` be non-consumable from `x`.
   Then the orbit `G·x` has at most `A(n)` points. The bound does not depend on the tail
   `σ^n x`.
2. **Frozen somewhere ⟹ 20.44.** Suppose some point of `Ẑ` has a non-consumable degree `n`. Then
   `G` has infinitely many orbits. For `N ≥ M_n`, at least `δ_n N / (2A(n))` of their minima lie
   in `[0, N]`, where `δ_n = μ(Ẑ ∖ C_n) ≥ 1/M_n`. The same holds on `[−N, −1]`.
3. **What remains.** Otherwise `G` is *totally consumable*: `C_n = Ẑ` for every `n`.
   - By compactness each `n` is then read from every point by a word from a fixed finite set.
   - By 1, every infinite orbit of any mixed-ray group reads every depth.
   - A counterexample to 20.44 on a mixed-sign ray must therefore be totally consumable.

## Proof

**1.**
- Let `y = P(x)`. No word reads the tail at `n`, so `P` carries it unchanged to a degree
  `p = n + tv`, and `p ∈ N^k`.
- So `p ∈ Seg(n)` and `σ^p y = σ^n x =: z`, an integer. Hence `y = ρ + m_p z` with
  `0 ≤ ρ < m_p`.
- The pairs `(p, ρ)` number at most `A(n)`, and `z` is fixed. ∎

**2.**
- `Ẑ ∖ C_n` is a nonempty union of classes mod `M_n`. So `[0, jM_n)` contains exactly
  `δ_n j M_n` of its integers, and every orbit through one of them has at most `A(n)` points,
  by 1.
- So at least `δ_n j M_n / A(n)` distinct orbits meet `[0, jM_n)`, and their minima are
  distinct points of `[0, jM_n)`.
- Take `j = ⌊N/M_n⌋`. Negatives are the same. ∎

**3.**
- Each set "a fixed word `P` reads `n`" is clopen. These sets cover the compact space `Ẑ`, so
  finitely many of them do. ∎

## Where the difficulty sits (`v = (−1, 1)`)

**Escape toward the 3-adic end.**
- In a totally consumable group, the zero tail of `x ∈ N_0` at a degree `n` with `m_n > x`
  walks along its level segment `e_2 + e_3 = L`. It can be read only near one of its ends.
- **The 2-adic end** (`e_3 < D`). There the configuration is `< 3^D 2^L`. For the anchor
  `n = (0, L)`, `3^L > x`, this is `≤ 2·3^D (x+1)^(log 2/log 3)`: a strict descent for large `x`.
- **The 3-adic end** (`e_2 < D`). There the only bound is `2^D 3^L`, which gives no descent.
- **So (heuristic).** If every integer's anchor tail were read at the 2-adic end, then iterating
  the descent would plausibly make every orbit meet a fixed finite set, and `G` would have finitely
  many orbits. This is argued in one line only and is not proved here (referee repair, a3b10b78df).
- The open case is exactly the one where tails escape toward the expanding, 3-adic end: the
  mixed-sign form of the Collatz escape.

**The typical totally consumable element is a drift walk.**
- For slopes `(3/2)^(±1)` and `1`, measure preservation forces
  `Σ μ_i (2/3)^(j_i) = 1 = Σ μ_i`.
- By convexity the forward walk then has nonnegative mean log-slope, and so does the backward
  walk.
- This is the regime of Collatz's own permutation `n ↦ 2n/3, (4n ∓ 1)/3`, whose cycle
  structure is unknown (Kohl, Math. Z. 264 (2010), §1). That permutation has a rank-2 cocycle.
- Heuristically such walks have positive-density orbit minima, which agrees with 20.44. Proving
  it needs control of every depth at once, which is the Terras barrier.

**The updated line.**

| Degree cocycle | Frozen tails | Kourovka 20.44 |
|---|---|---|
| positive ray | travel to infinity; invariant of infinite orbits | true |
| mixed-sign ray | trapped on finite segments; finite orbits | true unless totally consumable |
| rank 2 (`G_T`) | not controlled; carries reach every depth | ⟺ finitely many 3x+1 components |

## Lesson for general BH

**Whether frozen information is invariant or finite depends on the sign pattern of the drift.**
- On a positive ray, frozen tails travel to infinity, so they are invariants of infinite
  orbits.
- On a mixed-sign ray they are trapped on finite segments, so they force finite orbits, of a
  size bounded by the frozen degree alone.

**Both regimes are tame.** All the hardness sits in total consumability: dynamics that read
every depth. This is the arithmetic counterpart of "one-stack vs. two-stack".

**For host design.** Subgroups placed on a mixed-sign drift are finite-orbit-controlled as soon
as some information is frozen. Hardness, such as undecidable orbits, periodic monsters and
Collatz-type problems, needs dynamics that consume every depth.
