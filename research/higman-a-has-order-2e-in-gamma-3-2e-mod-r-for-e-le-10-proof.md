---
rg: 2
id: higman-a-has-order-2e-in-gamma-3-2e-mod-r-for-e-le-10-proof
kind: route
title: Proof via largest lower exponent-2 central class quotients computed by the standalone ANU p-Quotient Program, with a relator-sufficiency check for the B-tree kernel quotient at e = 8, 9 and table-free B-tree relators at e = 10
target: higman-a-has-order-2e-in-gamma-3-2e-mod-r-for-e-le-10
requires:
  - higman-b-twist-hypothesis-holds-exactly-for-e-at-most-8
  - higman-torsion-generator-quotients-factor-through-tree-lattices
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

Notation is that of the target, of `higman-b-twist-hypothesis-holds-exactly-for-e-at-most-8` (w14)
and of `higman-torsion-generator-quotients-factor-through-tree-lattices` (w11). All files are in
`experiments/higman-anupq-2quotients-2026-09-18/`.

## 0. The tool and what it certifies

`pq` is the standalone ANU p-Quotient Program, ANUPQ 3.3.3, built from the GAP package source. For a
finite presentation `G = <X | W>` and a class `k` it computes a consistent power-commutator
presentation of `P_k(G) = G/lambda_(k+1)(G)`. Here `lambda` is the lower exponent-2 central series,
so `P_k(G)` is the largest 2-group quotient of `G` of lower exponent-2 class at most `k`. Option 23
of the interactive menu collects a word in the defining generators and prints its normal form in
`P_k(G)`, or `IDENTITY`.

`mk.sh E C0 C1 GENS RELS` writes the keyword input used for every run:
- compute `P_C0`;
- at each class, display the order and collect `x1^(2^(j-1))` for `j = JMIN..E` (`x1` is the first
  generator, always `a`);
- then take the next class, up to `C1`.

`parse.py` reads a `pq` log. For each class it prints `log2 |P_k|` and the order of `a`: the least
tested power that collects to `IDENTITY`, or else twice the largest tested power.
`summary-output.txt` is `parse.py` applied to every log.

**Certificate lemma.** Let `G` satisfy `a^(2^e) = 1`, and let `P` be a finite quotient of `G` in
which `a^(2^(e-1)) != 1`. Then `ord(a in G) = 2^e`.

*Proof.* `ord(a in G)` divides `2^e` and is a multiple of `ord(a in P)`, which is `2^e`. ∎

Every 2-group quotient of `G` of class at most `k` is a quotient of `P_k(G)`. So an order bound read
off from `P_k(G)` holds for all such quotients (used in §4).

## 1a. e = 10 (item 0)

**Relators without tables.** At `e = 10`, the level tables of `levels_ck.py` are too large.
`evalk.py` evaluates a word in `b, d` at any level `k` of the same B-tree closed form, with no
tables. A level-`k` element is stored as the arrays of its `s`-values at depths `0..k-1`, and
right multiplication by `b^j` or `d^j` is applied recursively, using

- `(s,h).b^j = (s, h_r . d^(j 3^r))`;
- `(s,h).d^j = (s+j, h_(T^j r) . b^j)`, where `T = 3^-1 mod 2^e` and `r` runs mod `M = 2^(e-4)`.

At `e = 9` it reproduces the table results: the level-3 relators all hold at level 4, and only 52 of
200 level-2 relators hold at level 3.

`ballk.py e k NREL MAXBALL` runs a breadth-first search on the positive Cayley graph of the level-`k`
group, with elements evaluated by `evalk`. Every coincidence `g x = h` gives the relator
`w(g) x w(h)^-1`. Each relator is re-checked with `evalk.trivial`, and `b^n`, `d^n` are printed
first. At `e = 9` it reproduces `bbrels.py`'s output exactly.

**The added relators.** `rels-e10.txt` is the first 500 relators of `ballk.py 10 3` (level 3). The
largest is 83 letters. Level 3 is not all of `Bbar_10`:
- `evalk.py 10 4 rels-e10.txt` finds that 476 of the 500 hold at level 4 and 24 fail;
- of the first 1200 level-3 relators, 1149 hold at level 4 (`rels-e10-L4.txt`);
- so `G_3 != G_4` at `e = 10`, and level 3 is not known to be `Bbar_10`.

`pq` on `<b, d | relators>` gives `2^31` for the first 500 to 3002 level-3 relators, and `2^36` for
500 or 1149 relators from `rels-e10-L4.txt`. No sufficiency claim is made, and none is needed below.

**The certificate.** `qb10.in` is `Gammabar_10`, that is
`{ b^a = b^3, c^b = c^3, d^c = d^3, a^d = a^3, a^1024, b^1024, c^1024, d^1024, [a,c]^2 }`, together
with the 500 words of `rels-e10.txt`. The presented group `P_10` is a quotient of `Gammabar_10` with
`a -> a`, whatever the extra words are. `qb10.out` gives:

| class | 12 | 13 | 14 | 15 | 16 | 17 | 18 |
|---|---|---|---|---|---|---|---|
| log2 order | 488 | 790 | 1280 | 2120 | 3524 | 5940 | 10034 |
| log2 ord(a) | 7 | 7 | 8 | 8 | 9 | 9 | 10 |

At the class-18 step the log reads `Group: G to lower exponent-2 central class 18 has order
2^10034`, followed by `The input word is 512 1` and a nonempty normal form beginning
`.5949 .5950 .5960`. Class 18 took 493 s with a 400M-word workspace under a 2 GB cap, and the run
was stopped after it.

`P_k(P_10)` is a finite quotient of `Gammabar_10` in which `a^512 != 1`. By the certificate lemma,
`ord(a in Gammabar_10) = 2^10`. ∎

**Corroboration.** `qb10b.in` uses instead the first 500 relators of `rels-e10-L4.txt`, which all
hold at level 4. `qb10b.out` gives orders `2^491, 2^793, 2^1283, 2^2124, 2^3528, 2^5944` at classes
12–17, with the same `ord(a)` profile `2^7, 2^7, 2^8, 2^8, 2^9, 2^9`. Replacing the 24 relators that
fail at level 4 by valid ones changes the exponent by only 3 or 4, and does not change `ord(a)`.

## 1. e = 9 (item 1)

`g9low.in` (classes 1–12) and `g9loop.in` (classes 12–16) use the generators `{a,b,c,d}` and the
relations
`{ b^a = b^3, c^b = c^3, d^c = d^3, a^d = a^3, a^512, b^512, c^512, d^512, [a,c]^2 }`.
This is exactly `Gammabar_9`. In `pq`, `b^a` is `a^-1 b a` and `[a,c] = a^-1 c^-1 a c`, matching the
target's conventions.

`g9loop.out`, at the class-16 step:
- `Group: G to lower exponent-2 central class 16 has order 2^21418`;
- `The input word is 256 1`, followed by a nonempty normal form (it begins `.19697 ...` in the
  displayed tail), not `IDENTITY`.

The class-15 step reports order `2^11776` with `a^256 = IDENTITY`. The run was stopped during
class 17 (`Terminated`, 20 minutes wall clock, 3m44s CPU on a loaded machine). The class-16 data is
complete before that point.

By the certificate lemma, `ord(a in Gammabar_9) = 2^9`. ∎

**Through Qbar_B at e = 9.** This is the pipeline of §2 below, with `e = 9`.
- `levels_ck.py 9 3` builds the level-3 tables of `Bbar_9`, of order `2^22` (w14's order).
- `bbrels.py 9 3 998` gives `rels-e9.txt`: `b^128`, `d^128` and 998 cycle relators, each re-checked
  on the tables. The maximum length is 128.
- *Sufficiency.* `bb9.out` reports `Group completed. Lower exponent-2 central class = 7,
  Order = 2^22`. So the 2-group quotients of `Gamma_9/<<rels-e9, R>>` are those of `Qbar_B`, as in
  §2. With 502 relators (`NREL = 500`) the order is `2^30`, so that set is not sufficient.
- `qb9.in` is `Gammabar_9` together with `rels-e9`. `qb9.out` gives:

  | class | 12 | 13 | 14 | 15 | 16 | 17 |
  |---|---|---|---|---|---|---|
  | log2 order | 485 | 787 | 1277 | 2117 | 3521 | 5936 |
  | log2 ord(a) | 7 | 7 | 8 | 8 | 9 | 9 |

So `ord(a in Qbar_B) = 2^9` at `e = 9`. The first certifying class is 16, the same as for
`Gammabar_9`, but the quotient is 6 times smaller in the exponent. At `e = 9`, `(H_9)` fails
(w14), so this says nothing about the edge image `Abar_9`. ∎

## 2. e = 8 (item 2)

**Direct.** `g8loop.in` is the same presentation with exponent 256. At class 14 its log reports
order `2^6510`, and `a^128` has a nonempty normal form. So `ord(a in Gammabar_8) = 2^8`.

**Through Qbar_B.** w14 §8 proves `Lambda_B = <<relators of Bbar_8>>_Gamma`. It computes `Bbar_8`
exactly, as a group of order `2^17` given by its right regular representation (`levels_ck.py`, level
tables `L3`).

`bbrels.py 8 3 300` reads those tables and runs a breadth-first search on the Cayley graph. It
outputs `b^64`, `d^64` and the first 300 distinct cycle relators, which are freely and cyclically
reduced and deduplicated up to rotation and inversion. It re-evaluates every relator on the tables
and asserts that it is trivial in `Bbar_8`. The result is `rels-e8.txt`: 302 relators, of maximum
length 64.

*Sufficiency.* `bb8.out` runs `pq` on `<b, d | rels-e8>` and reports
`Group completed. Lower exponent-2 central class = 6, Order = 2^17`. So the largest 2-quotient of
`<b,d | rels-e8>` has order `2^17`.

It maps onto `Bbar_8`, because the relators hold there and `Bbar_8` is a 2-group generated by
`b, d`. It therefore equals `Bbar_8`.

Hence in every 2-group quotient of `Gamma_8/<<rels-e8, R>>`, the image of `<b,d>` satisfies all
relators of `Bbar_8`, so `Lambda_B` dies there. The 2-group quotients of `Gamma_8/<<rels-e8, R>>`
are therefore exactly those of `Qbar_B`.

`qb8.in` is `Gammabar_8` together with `rels-e8`. Its log gives:

| class | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 |
|---|---|---|---|---|---|---|---|---|
| log2 order | 195 | 306 | 480 | 782 | 1272 | 2112 | 3514 | 5928 |
| log2 ord(a) | 6 | 7 | 7 | 7 | 8 | 8 | 8 | 8 |

Classes 11–13 reproduce w14's GAP values `2^306, 2^480, 2^782` exactly.

Class 14 gives `ord(a in Qbar_B) = 2^8`. Under `(H_8)`, which w14 item 3 proves, `Abar_8` embeds in
`Qbar_B` with `a -> a`. So `ord(a in Abar_8) = 2^8` as well. ∎

## 3. Consequences (item 3)

- **e <= 5:** w11 gives `ord(a in Gammabar_e) = 2^e`.
- **e = 6, 7:** w14 §8 certifies this through `Qbar_B`, which is a quotient of `Gammabar_e`.
- **e = 8, 9, 10:** §§1a, 1 and 2 above.

For `e >= 10`, adding `x^1024` to the relators of `Gammabar_e` gives `Gammabar_10`. So
`Gammabar_10` is a quotient of `Gammabar_e`, and of `H4(3)/<<R>>`, with `a -> a`. Therefore
`ord(a) >= ord(a in Gammabar_10) = 2^10` in all of them.

The map `sigma^2 : a -> c, b -> d, c -> a, d -> b` permutes the defining relations of `Gamma_e`:
`b^a = b^3` goes to `d^c = d^3`, and so on. It sends `R` to `[c,a]^2 = R^-1`, so it induces an
automorphism of `Gammabar_e` and of `H4(3)/<<R>>` exchanging `a` and `c`. Hence `ord(c) = ord(a)`. ∎

## 4. Class profile of Gammabar_9 (item 4, first two bullets)

From `g9low.out` and `g9loop.out`:

| class k | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| log2 order | 4 | 10 | 19 | 32 | 52 | 84 | 141 | 231 | 395 | 672 | 1172 | 2046 | 3642 | 6510 | 11776 | 21418 |
| log2 ord(a) | 1 | 2 | 3 | 4 | 4 | 4 | 5 | 5 | 6 | 6 | 7 | 7 | 7 | 8 | 8 | 9 |

By the remark after the certificate lemma, every 2-quotient of `Gammabar_9` of class at most 15
has `ord(a) <= 2^8`, and every one of class at most 13 has `ord(a) <= 2^7`.

`g8loop.out` gives `Gammabar_8` at classes 10–14 with the same orders
(`2^672, 2^1172, 2^2046, 2^3642, 2^6510`) and `ord(a) = 2^6, 2^7, 2^7, 2^7, 2^8`.

`Gammabar_8` is a quotient of `Gammabar_9`, so for classes at most 13 `ord(a) <= 2^7` there too.
The first certifying class is therefore exactly 14 at `e = 8` and exactly 16 at `e = 9`.

For `k <= 9` every class-`k` 2-quotient has exponent dividing `2^k`, which divides `512`. So the first
nine columns are also the class profile of `H4(3)/<<R>>` itself. They agree with w10's
`diag_tower-output.txt` for `ord(a)` (for example `2^6` at class 9).

## 5. The test groups (item 4, last two bullets)

**Etest2** is w14 §9's group
`< a, c | a^512, c^512, R, U^a = U^3, c^U = c^257, U^8, V^c = V^3, a^V = a^257, V^8 >`, with
`U = S^-5` and `V = sigma^2(S)^-5`. `S` is the syllable-length-8 word
`a^-171 c^-211 a^-77 c^-213 a^-171 c^-83 a^-77 c^-85` of w13's `hfail-output.txt`.

`et9.in` enters it with the generators `{a,c,u,v}`, defining `u` and `v` by those words. `pq`
eliminates them as definitions. `et9.out`, classes 8–14:

| class | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
|---|---|---|---|---|---|---|---|
| log2 order | 77 | 124 | 197 | 328 | 540 | 918 | 1548 |
| log2 ord(a) | 8 | 8 | 8 | 8 | 8 | 9 | 9 |

`et9low.in` is the same input run over classes 1–10. It gives `2, 5, 9, 14, 22, 32, 51, 77, 124,
197` and `ord(a) = 2^1, ..., 2^8, 2^8, 2^8`, which is w14's GAP table exactly. At class 13, `a^256`
has a nonempty normal form.

So the ceiling of w14 item 6 is not uniform in the class: `Etest2` has a 2-group quotient with
`ord(a) = 2^9`. This says nothing about `Gammabar_9` by itself, because `Etest2` maps onto `Abar`
and not the other way. The statement about `Gammabar_9` is §1.

**Etest3** (`et3.in`) adds `U^2`, `V^2` and `[U,V]`, which hold in `Qbar_B` by w14 §7. Its orders
at classes 10–15 are `2^197, 2^328, 2^540, 2^916, 2^1546, 2^2654`, and `ord(a)` is `2^9` from
class 13 on.

**Etest10** (`et10.in`) is w14's `e = 10` analogue:
- `S = a^341 c^301 a^435 c^299 a^341 c^429 a^435 c^939`;
- `U = S^-5`, `V = sigma^2(S)^-5`, `U^16`, `V^16`, `a^1024`, `c^1024`, and the same four
  semidirect relations.

Classes 8–14 have the same orders as `Etest2`, and `ord(a) = 2^9` from class 13 on. A continuation
run (`et10b.in`, from class 14) gives order `2^2658` at class 15 and `2^4560` at class 16, both with
`ord(a) = 2^9`. It was stopped after class 16, since §1a settles `e = 10` directly.

## 6. Limits and dead ends

- **Gammabar_9 class 17.** Stopped after 20 minutes. Extrapolating the growth factor of about 1.8
  per class in `log2 |P_k|`, it has order about `2^38000`, and class 18 about `2^70000`. So the
  direct route does not reach `e = 10`; §1a goes through the B-tree relators instead.
- **Test groups as ceilings.** A ceiling for `Etest2` or `Etest3` would have been the only way to
  cap `Gammabar_9` from these relations. Both break at class 13, and §1 makes the question moot at
  `e = 9`.
- **Truncated-level relators.** `q9L2.in` adds to `Gammabar_9` 500 relators of the level-2 quotient
  `G_2` of `Bbar_9`. This is a proper quotient of `Bbar_9`, of order `2^18`. In `q9L2.out`,
  `ord(a) = 2^6` at every class from 12 to 15. So relators of a proper quotient of `Bbar_e` can kill
  `a`. This does not affect §1a: there `a` survives, and the certificate lemma needs no validity of
  the added words. But a search for lower bounds should use relators checked at the deepest level
  it can reach.
- **e = 11.** Extrapolating §1a, this needs class 20, at about `2^29000`, which is beyond the 2 GB
  cap.
