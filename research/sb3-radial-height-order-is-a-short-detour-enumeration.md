---
rg: 2
id: sb3-radial-height-order-is-a-short-detour-enumeration
kind: claim
title: The radial height-spread order is a short-detour enumeration of the Stallings–Bieri group SB_3
---

Let SB_3 = ker(F_2^3 → Z), with every generator sent to 1. It acts simply transitively on the height-0
vertices v = (x_1, x_2, x_3) of T^3, where T is the Cayley tree of F_2 = ⟨a, b⟩ with h(a) = h(b) = 1.
Take the generating set { x_i y_j^{-1} : i ≠ j, x, y ∈ {a, b} }. Order the vertices by the key
(Σ |x_i|, −Σ |h(x_i)|, (|x_1|, |x_2|, |x_3|)) lexicographically, breaking ties arbitrarily.

**Claim.** This is a short-detour enumeration in the sense of
`short-detour-enumeration-gives-contractible-qi-2-complex`, with constant L = 10.

## Attempts

- Condition 1 (every v ≠ o has an earlier neighbour) is proved in
  `research/artifacts/zp-sb3-short-detour-2026-09-13-part2.md` §2. Condition 2 is open.
- Computational evidence (part 3 of the same artifact):
  - an exhaustive census of the 14908 vertices with all |x_i| ≤ 3, and random samples of 20000 vertices
    with |x_i| ≤ 6 and 4000 with |x_i| ≤ 9;
  - every earlier neighbour is reached from one of them within detour depth ≤ 5, through strictly earlier
    vertices;
  - there are no exceptions.
- Radial orders in the distance vector alone always fail condition 1 (part 2 §1), so the height term
  is essential.
- Proof plan (part 3 §3): a finite configuration census over the last few letters of each coordinate and
  clipped heights, reduced by symmetry and a hub neighbour, or a human case analysis built on the star
  lemma of part 1.
- 2026-09-13, computer-assisted proof complete but UNREVIEWED:
  `research/artifacts/zp-sb3-short-detour-2026-09-13-part4.md`.
  - Configurations record the last 2 letters of each coordinate and heights clipped at ±3.
  - Moves into unknown prefixes are forbidden, and undetermined comparisons count as "not earlier". The
    set of earlier neighbours is exact.
  - All 197416 feasible configurations have an earlier neighbour, and all earlier neighbours are reached
    within 6 steps through strictly earlier vertices. So L = 12.
  - The proof route is held back until z-verify-topology reviews the artifact (soundness argument §2 and
    script §5), so that the Problem 1.3 root does not compile as established before a PASS.
- 2026-09-17, referee review PASS (swarm-0917-w6-w6-z-last1):
  `research/artifacts/zp-sb3-short-detour-review-2026-09-17.md`.
  - The soundness of the finite reduction was re-derived (review §3): coverage, abstract paths are real,
    earlier-marking is sound, and E(v) is exact. No gap was found.
  - The published script, re-run verbatim, gives bad 0 on 197416 configurations.
  - An independent re-implementation, written from the statement with interval heights, reproduces the
    197416 count. Over all e_0 ∈ E(v), the maximum least eccentricity is 3 and bad is 0. So L = 6, which
    covers the stated L = 10; the published 6-step bound alone gave only L = 12.
  - Real-vertex censuses with no abstraction (all 14908 vertices with |x_i| ≤ 3, and 4000 random vertices
    with |x_i| ≤ 10) find no failure.
  - Scripts and logs: `experiments/sb3-short-detour-review-2026-09-17/`.
  - Route: `sb3-radial-height-order-census-proof`.
