---
rg: 2
id: higman-a-has-order-2e-in-gamma-3-2e-mod-r-for-e-le-10
kind: claim
title: In Gamma(3,2^e)/<<[a,c]^2>> the generator a has order exactly 2^e for every e <= 10, certified by 2-quotients of class 14, 16 and 18 at e = 8, 9, 10; so a has order at least 2^10 in H4(3)/<<[a,c]^2>>, and the d^64 cap at e = 9 is not class-uniform
distinct_from:
  higman-b-twist-hypothesis-holds-exactly-for-e-at-most-8: that certifies ord(a) = 2^e only for e <= 7, proves ord(a) >= 2^7 for e >= 7, and bounds ord(a) by 2^8 in 2-quotients of class <= 10 at e = 9; this certifies ord(a) = 2^e at e = 8, 9, 10, and shows that the class-10 bound is not uniform in the class.
  higman-torsion-generator-quotients-factor-through-tree-lattices: that proves ord(a) = 2^e in Gammabar_e for e <= 5 and the reduction of infinite order to infinitely many e; this extends the certified range to e <= 10 by 2-quotient computation, without any embedding.
  higman-power-pair-collapse-is-base-uniform-up-to-torsion: that leaves open whether H4(3)/<<[a,c]^2>> has generators of infinite order; this does not settle that, and proves only the lower bound ord(a) >= 2^10 there.
artifacts:
  - experiments/higman-anupq-2quotients-2026-09-18/mk.sh
  - experiments/higman-anupq-2quotients-2026-09-18/parse.py
  - experiments/higman-anupq-2quotients-2026-09-18/summary-output.txt
  - experiments/higman-anupq-2quotients-2026-09-18/g9low.in
  - experiments/higman-anupq-2quotients-2026-09-18/g9low.out
  - experiments/higman-anupq-2quotients-2026-09-18/g9loop.in
  - experiments/higman-anupq-2quotients-2026-09-18/g9loop.out
  - experiments/higman-anupq-2quotients-2026-09-18/g8loop.in
  - experiments/higman-anupq-2quotients-2026-09-18/g8loop.out
  - experiments/higman-anupq-2quotients-2026-09-18/bbrels.py
  - experiments/higman-anupq-2quotients-2026-09-18/rels-e8.txt
  - experiments/higman-anupq-2quotients-2026-09-18/bb8.in
  - experiments/higman-anupq-2quotients-2026-09-18/bb8.out
  - experiments/higman-anupq-2quotients-2026-09-18/qb8.in
  - experiments/higman-anupq-2quotients-2026-09-18/qb8.out
  - experiments/higman-anupq-2quotients-2026-09-18/et9low.in
  - experiments/higman-anupq-2quotients-2026-09-18/et9low.out
  - experiments/higman-anupq-2quotients-2026-09-18/et9.in
  - experiments/higman-anupq-2quotients-2026-09-18/et9.out
  - experiments/higman-anupq-2quotients-2026-09-18/et3.in
  - experiments/higman-anupq-2quotients-2026-09-18/et3.out
  - experiments/higman-anupq-2quotients-2026-09-18/et10.in
  - experiments/higman-anupq-2quotients-2026-09-18/et10.out
  - experiments/higman-anupq-2quotients-2026-09-18/et10b.in
  - experiments/higman-anupq-2quotients-2026-09-18/et10b.out
  - experiments/higman-anupq-2quotients-2026-09-18/qb9.sh
  - experiments/higman-anupq-2quotients-2026-09-18/rels-e9.txt
  - experiments/higman-anupq-2quotients-2026-09-18/bb9.in
  - experiments/higman-anupq-2quotients-2026-09-18/bb9.out
  - experiments/higman-anupq-2quotients-2026-09-18/qb9.in
  - experiments/higman-anupq-2quotients-2026-09-18/qb9.out
  - experiments/higman-anupq-2quotients-2026-09-18/rels-e9-L2.txt
  - experiments/higman-anupq-2quotients-2026-09-18/q9L2.in
  - experiments/higman-anupq-2quotients-2026-09-18/q9L2.out
  - experiments/higman-anupq-2quotients-2026-09-18/evalk.py
  - experiments/higman-anupq-2quotients-2026-09-18/ballk.py
  - experiments/higman-anupq-2quotients-2026-09-18/rels-e10.txt
  - experiments/higman-anupq-2quotients-2026-09-18/rels-e10-L4.txt
  - experiments/higman-anupq-2quotients-2026-09-18/qb10.in
  - experiments/higman-anupq-2quotients-2026-09-18/qb10.out
  - experiments/higman-anupq-2quotients-2026-09-18/qb10b.in
  - experiments/higman-anupq-2quotients-2026-09-18/qb10b.out
---

**ESTABLISHED** (proposed) by `higman-a-has-order-2e-in-gamma-3-2e-mod-r-for-e-le-10-proof`.
- Items 0–3 are certified finite computations. Each is the largest 2-quotient of given class of an
  explicit finite presentation, computed by the ANU p-Quotient Program (standalone `pq`,
  ANUPQ 3.3.3), combined with a one-line hand argument.
- Item 4 is read off from the same computations.

**Setting.**
- `H4(3) = < a, b, c, d | b^a = b^3, c^b = c^3, d^c = d^3, a^d = a^3 >`, with `x^y = y^-1 x y`.
- `R = [a,c]^2`.
- `Gamma_e = Gamma(3,2^e) = H4(3)/<<a^m, b^m, c^m, d^m>>` with `m = 2^e`, and
  `Gammabar_e = Gamma_e/<<R>>`.
- "Class" means class in the lower exponent-2 central series, as in `pq`.

**Statement.**
0. **e = 10.** Let `P_10` be `Gammabar_10` with 500 further relators added, all words in `b, d`
   (the file `rels-e10.txt`). The largest class-18 2-quotient of `P_10` has order `2^10034`, and
   `a^512 != 1` in it. `P_10` is a quotient of `Gammabar_10`, whatever the added relators are. Hence
   `ord(a in Gammabar_10) = 2^10`.
   - The added relators are short relations of the level-3 truncation of `Bbar_10`, found by a
     table-free search. 24 of the 500 already fail at level 4, since the level-3 and level-4
     truncations differ at `e = 10`. So `P_10` may be a proper quotient of `Qbar_B`. The
     certificate does not need the added relators to hold.
   - A second run corroborates this. It uses 500 relators that also hold at level 4
     (the first 500 lines of `rels-e10-L4.txt`), and gives the same `ord(a)` profile, with orders `2^491 .. 2^5944` at
     classes 12–17.
1. **e = 9.** The largest class-16 2-quotient of `Gammabar_9` has order `2^21418`, and `a^256 != 1`
   in it. Hence `ord(a in Gammabar_9) = 2^9`.
   - Independently, the largest class-16 2-quotient of `Qbar_B = Gammabar_9/<<Lambda_B>>` has order
     `2^3521`, with `a^256 != 1`. It is computed from 1000 relators of `Bbar_9`, whose largest
     2-quotient is exactly `Bbar_9` (order `2^22`).
   - So `ord(a in Qbar_B) = 2^9` at `e = 9`: the B-tree kernel quotient does not lose `a` at
     `e = 9`, although `(H_9)` fails there.
2. **e = 8.** The largest class-14 2-quotient of `Gammabar_8` has order `2^6510`, and `a^128 != 1`
   in it. Hence `ord(a in Gammabar_8) = 2^8`.
   - Independently, the largest class-14 2-quotient of `Qbar_B = Gammabar_8/<<Lambda_B>>` (w14) has
     order `2^1272`, with `a^128 != 1`.
   - So `ord(a) = 2^8` also in `Qbar_B`, and in the embedded edge image `Abar_8` of w14 item 3.
3. **Consequences.**
   - With w11 (`e <= 5`) and w14 (`e = 6, 7`): `ord(a) = 2^e` in `Gammabar_e` for every `e <= 10`.
   - `Gammabar_e` maps onto `Gammabar_10` for `e >= 10`, and `H4(3)/<<R>>` maps onto both, with
     `a -> a`. So `ord(a) >= 2^10` in `Gammabar_e` for every `e >= 10`, and in
     `H4(3)/<<[a,c]^2>>`. The previous bound was `2^7`.
   - The same holds for `c`, by the automorphism `sigma^2 : a <-> c, b <-> d` of `Gamma_e`, which
     maps `R` to `[c,a]^2 = R^-1`.
4. **Class profile, and the fate of the d^64 cap.**
   - In `Gammabar_9`, the class-`k` quotient first reaches `ord(a) = 2^j` at

     | j | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
     |---|---|---|---|---|---|---|---|---|---|
     | first class k | 1 | 2 | 3 | 4 | 7 | 9 | 11 | 14 | 16 |

     The orders at classes 1..16 are `2^4, 2^10, 2^19, 2^32, 2^52, 2^84, 2^141, 2^231, 2^395,
     2^672, 2^1172, 2^2046, 2^3642, 2^6510, 2^11776, 2^21418`.
   - The first certifying class is therefore exactly 14 at `e = 8` and exactly 16 at `e = 9`.
     Every 2-quotient of `Gammabar_9` of class at most 15 has `ord(a) <= 2^8`, and every one of
     class at most 13 has `ord(a) <= 2^7`. This is sharper than w14 item 6 (class `<= 10`), and it
     is a property of the class tower, not of the `d^64` relation.
   - w14's test group `Etest2`, built from `b^64 = S^-5` and `d^64 = sigma^2(S)^-5`, has `Abar` as
     a quotient. Classes 1–10 reproduce w14's GAP orders exactly. Classes 11–14 have orders `2^328,
     2^540, 2^918, 2^1548`, with `ord(a) = 2^8, 2^8, 2^9, 2^9`. So the cap of w14 item 6 breaks at
     class 13. Adding `U^2`, `V^2` and `[U,V]` (true in `Qbar_B`) changes the orders at classes 13–15
     to `2^916, 2^1546, 2^2654` but not the break.
   - The `e = 10` analogue `Etest10` (`b^64 = S^-5` with `(b d)'' = b^832`, and `U^16`, `V^16`) has
     the same 2-quotient orders as `Etest2` through class 14. Its class-15 and class-16 quotients
     have orders `2^2658` and `2^4560`, both with `ord(a) = 2^9`.
   - At `e = 10`, the quotient `P_10` of item 0 has `ord(a) = 2^7` at classes 12–13. It first
     reaches `2^8, 2^9, 2^10` at classes 14, 16, 18. Its orders at classes 12–18 are `2^488, 2^790, 2^1280, 2^2120, 2^3524,
     2^5940, 2^10034`.

**What this does to the target question.** The target question asks whether `a` has infinite order
in `H4(3)/<<[a,c]^2>>`. By w11 it suffices that `ord(a) = 2^e` in `Gammabar_e` for infinitely many
`e`.
- The brief's alternative is decided on the "break" side. No class-independent cap at `2^8` exists
  at `e = 9`: the relation `d^64 = sigma^2(S)^-5` does not stop the 2-quotient method, and
  `Gammabar_9` itself has a 2-group quotient with `ord(a) = 2^9`.
- The certified range is now `e <= 10`, with first certifying classes `c(e) = 9, 11, 14, 16, 18`
  for `e = 6, 7, 8, 9, 10` (at `e = 10`, in the quotient `P_10`). These grow by 2 or 3 per step,
  while `log2` of the quotient order grows by a factor of about 1.7–1.8 per class.
- The lower bound is `ord(a) >= 2^10` in `H4(3)/<<[a,c]^2>>`. Infinite order is still open.

**Next step.** Extend to `e = 11` and look for a uniform mechanism.
- `e = 11` needs `ord(a) = 2^11` in some 2-quotient. Extrapolating, that needs class 20. The
  `P_10` orders grow by a factor of about 1.7 per class, so class 20 is about `2^29000`, which is
  beyond this run's 2 GB cap (class 18 at `2^10034` used a 1.6 GB workspace). Two options:
  - add more relators of `Bbar_11`, from `ballk.py` at level 4 or 5 and checked by `evalk.py`,
    to shrink the quotient;
  - run `pq` itself, unchanged, with a much larger workspace.
- A proof for all `e` needs a reason why `ord(a)` in the class-`k` 2-quotient of `H4(3)/<<R>>`
  grows without bound. At `e = 10` the class-`k` quotient of `P_10` has `ord(a) = 2^(k/2+1)` for even
  `k = 12..18`. A natural first step is to identify a uniform finite 2-group family in which `a`
  has order `2^e`, for example iterated wreath or self-similar quotients read off from the class-18
  presentation.

**Dead ends recorded here.** See proof §6:
- the `Gammabar_9` class-17 quotient, killed after 20 minutes;
- `Etest2` and `Etest3` as a way to prove a ceiling;
- relators of a truncated level. Relators of the level-2 quotient `G_2` of `Bbar_9` (order `2^18`)
  cut `ord(a)` in `Gammabar_9` down to `2^6` through class 15. Only relators of the full `Bbar_e` are
  safe to add.
