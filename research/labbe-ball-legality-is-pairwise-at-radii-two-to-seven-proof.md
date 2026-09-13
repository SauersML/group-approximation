---
rg: 2
id: labbe-ball-legality-is-pairwise-at-radii-two-to-seven-proof
kind: route
title: Exact enumeration of Labbé's ball language from the self-similar morphism, with a completeness argument
target: labbe-ball-legality-is-pairwise-at-radii-two-to-seven
requires: []
artifacts:
  - research/artifacts/fp-simple-relation-climbing-2026-09-13.md
  - experiments/fp-simple-relation-climbing/labbe_lang.py
  - experiments/fp-simple-relation-climbing/labbe_orders.py
---

**Input (read from source).** Labbé arXiv:1802.03265.
- The tile list `tilesU` (strings right, top, left, bottom) and the tables `alpha`, `beta`,
  `gamma` come from `for_article1.sage`, lines 50–85. Images are lists of columns, each listed
  bottom to top.
- Proposition `prop:pre-main` (TeX line 2269): `omega = alpha∘beta∘gamma` is expansive and
  recognizable in `Omega_U`, and
  `Omega_U = omega(Omega_U) ∪ sigma^(e_1) omega(Omega_U) ∪ sigma^(e_2) omega(Omega_U) ∪ sigma^(e_1+e_2) omega(Omega_U)`.

**Completeness.**
1. **Images of legal patches are legal.** `omega(Omega_U) ⊆ Omega_U`, so `omega^j(Q)` is legal for
   every legal patch `Q`.
2. **Every legal ball patch is found.**
   - Iterating the displayed equation, every tiling is a translate of `omega^j(y)` for some
     `y ∈ Omega_U`. It is therefore partitioned into level-`j` supertiles `omega^j(y_v)`.
   - The minimal side of `omega^j(a)` over tiles `a` is `1, 1, 2, 3, 5, 8, 13, 21` for
     `j = 0..7`.
   - Once that side is at least `2r+1`, a ball `B(r)` meets at most two columns and two rows of
     supertiles. It then lies inside `omega^j(Q)` with `Q` the legal `2 x 2` pattern
     `y|{u, u+e_1, u+e_2, u+e_1+e_2}`.
   - With `j = 7`, `L_(B(r))` for `r <= 7` is the set of `B(r)`-patterns of the patches
     `omega^7(Q)`, `Q ∈ L_(2x2)`.
3. **The legal `2 x 2` patterns.** They form the least set containing the `2 x 2` factors of a
   large supertile and closed under taking `2 x 2` factors of `omega`-images.
   - By minimality every legal `2 x 2` pattern occurs in `omega^m(0)` for large `m`.
   - The closure seeded from `omega^7(0)` and the closure seeded from `omega^9(0)` both have 50
     elements.
   - Every computed image passes the Wang edge-matching test.

**Enumeration.**
- `labbe_lang.py` computes `L_(B(7))` and restricts it to smaller radii (item 1). It then tests
  translates `g` with `0 < |g|_1 <= 3` against `L_(B(R+3))` (item 2).
- It builds every pattern on `B(r+1)` whose five sub-balls are legal, by joining extensions
  over the boundary sphere, and compares with `L_(B(r+1))` (item 3). Every legal pattern appears
  among the candidates, which checks the join.
- `labbe_orders.py` restricts each hidden illegal pattern to all unions of `k` sub-balls, using
  legal restrictions of `L_(B(r+1))`. Every one already has an illegal union of two sub-balls
  (item 4).
- Both scripts are deterministic and take under 2 seconds with `/usr/bin/python3.11`.
