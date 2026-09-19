---
rg: 2
id: higman-b-twist-hypothesis-holds-exactly-for-e-at-most-8-proof
kind: route
title: Proof via the self-similar word-tree model of the B-action, exact level verification, all-element defect computation, the relative subgroup A.<b^64,d^64> at e = 9, and 2-quotient certificates
target: higman-b-twist-hypothesis-holds-exactly-for-e-at-most-8
requires:
  - higman-gamma-3-2e-is-a-reducible-lattice-for-e-at-most-7
  - higman-edge-relator-twist-breaks-tree-lattice-freiheitssatz
artifacts:
  - experiments/higman-b-automaton-2026-09-18/mult.py
  - experiments/higman-b-automaton-2026-09-18/check_ball.py
  - experiments/higman-b-automaton-2026-09-18/check_ball-output.txt
  - experiments/higman-b-automaton-2026-09-18/levels.py
  - experiments/higman-b-automaton-2026-09-18/levels_np.py
  - experiments/higman-b-automaton-2026-09-18/levels_ck.py
  - experiments/higman-b-automaton-2026-09-18/run9.sh
  - experiments/higman-b-automaton-2026-09-18/verify.py
  - experiments/higman-b-automaton-2026-09-18/verify_all.sh
  - experiments/higman-b-automaton-2026-09-18/verify_all-output.txt
  - experiments/higman-b-automaton-2026-09-18/lev8.out
  - experiments/higman-b-automaton-2026-09-18/lev9.out
  - experiments/higman-b-automaton-2026-09-18/rel.py
  - experiments/higman-b-automaton-2026-09-18/rel-e7-output.txt
  - experiments/higman-b-automaton-2026-09-18/rel-e8-output.txt
  - experiments/higman-b-automaton-2026-09-18/rel-e9-output.txt
  - experiments/higman-b-automaton-2026-09-18/symsec.py
  - experiments/higman-b-automaton-2026-09-18/symsec-output.txt
  - experiments/higman-b-automaton-2026-09-18/orbits.py
  - experiments/higman-b-automaton-2026-09-18/ord2.g
  - experiments/higman-b-automaton-2026-09-18/e567.out
  - experiments/higman-b-automaton-2026-09-18/e8.out
  - experiments/higman-b-automaton-2026-09-18/relators.py
  - experiments/higman-b-automaton-2026-09-18/abar_e5.g
  - experiments/higman-b-automaton-2026-09-18/abar_e6.g
  - experiments/higman-b-automaton-2026-09-18/qbexport.py
  - experiments/higman-b-automaton-2026-09-18/bbar_e5.g
  - experiments/higman-b-automaton-2026-09-18/bbar_e6.g
  - experiments/higman-b-automaton-2026-09-18/bbar_e7.g
  - experiments/higman-b-automaton-2026-09-18/qbpq.g
  - experiments/higman-b-automaton-2026-09-18/qbpq-e6.out
  - experiments/higman-b-automaton-2026-09-18/qbpq-e7.out
  - experiments/higman-b-automaton-2026-09-18/qbpq-e8.out
  - experiments/higman-b-automaton-2026-09-18/abarpq.g
  - experiments/higman-b-automaton-2026-09-18/abarpq-e7.out
  - experiments/higman-b-automaton-2026-09-18/abartest.g
  - experiments/higman-b-automaton-2026-09-18/abartest-e9-output.txt
  - experiments/higman-b-automaton-2026-09-18/abartest2-e9-output.txt
  - experiments/higman-b-automaton-2026-09-18/abartest10.g
  - experiments/higman-b-automaton-2026-09-18/abartest10-e10-output.txt
---

Notation is that of the target and of `higman-gamma-3-2e-is-a-reducible-lattice-for-e-at-most-7`
(the w13 node). `m = 2^e`, `n = m/4`, `M = 2^(e-4)` (`e >= 5`), `t = 3^-1 mod m`. The unit `3` has
order `n` modulo `m` and order `M` modulo `n`. All scripts are in
`experiments/higman-b-automaton-2026-09-18/`.

## 0. What is used from the w13 node

- Exact factorization `Gamma = A · B`, `A ∩ B = 1`, and the push rules
  `b^q a^i = a^i b^(q 3^i)`, `b^q c^k = c^(k t^q) b^q`, `d^q c^i = c^i d^(q 3^i)`,
  `d^q a^k = a^(k t^q) d^q` (its section 0).
- The vertices of `T_B` at distance `L` from `v = L1` are the cosets `alpha L1` with `alpha` the
  reduced words `a^(x1) c^(x2) a^(x3) ...` of syllable length `L`, `x1 in Z/m`, `x2, x3, ... != 0`.
- `b^n, d^n in Lambda_B` (its item 1), `Lambda_B <= B` normal in `Gamma`.
- For `beta in B`, `beta R = S_beta beta^R` with `S_beta in A`, `beta^R in B` (push `beta` through
  the eight syllables of `R = a^-1 c^-1 a c a^-1 c^-1 a c`), and `beta'' = beta^R beta^-1`, so that
  `beta R beta^-1 = S_beta beta''` (its item 3).
- The reduction lemma (its item 3): under `(H_e)`, `Abar_e = < a, c | a^m, c^m, S_beta >` embeds in
  `Qbar_B` with index `|Bbar|`. Its proof uses only the exact factorization of `Q_B = A · Bbar` and
  the fact that `M := <<R>>_{Q_B}` is generated, as a normal subgroup of `A`, by the `S_beta`.

## 1. Closed form of the B-action (Lemma 1)

**Lemma 1.** Write a vertex of `T_B` as its word `x = (x1, x2, ..., xL)`. Put
`J_i = x1 + x3 + ... + x_(2i-1)` and `K_i = x2 + x4 + ... + x_(2i)` (`K_0 = 0`). Then
- `b^u` fixes the odd coordinates and sends `x_(2i) -> x_(2i) · t^(u 3^(J_i))`;
- `d^u` fixes the even coordinates and sends `x_(2i-1) -> x_(2i-1) · t^(u 3^(K_(i-1)))`.

*Proof.* `beta · alpha L1 = alpha' beta' L1 = alpha' L1` when `beta alpha = alpha' beta'` with
`beta' in B <= L1`. Push `b^u` through `a^(x1)`: it becomes `b^(u 3^(x1))` and `a^(x1)` is unchanged.
Push `b^(u 3^(x1))` through `c^(x2)`: `c^(x2)` becomes `c^(x2 t^(u 3^(x1)))` and the `b`-power is
unchanged. Iterating, the `b`-power in front of `x_(2i)` is `b^(u 3^(J_i))`, which gives the formula
for `b^u`. The case of `d^u` is the same with the roles of the parities exchanged (`d^u` first meets
`a^(x1)` with exponent `u`, so `K_0 = 0`). Units are multiplied into nonzero coordinates, so reduced
words go to reduced words. ∎

`mult.py` implements Lemma 1. `check_ball.py` compares it with the syllable-by-syllable push of the
w13 script `pathstab.py` on 3000 random vertices of distance up to 9 and random `u`, for both `b^u`
and `d^u`: 0 mismatches for `e = 5..10` (`check_ball-output.txt`).

## 2. The extended word tree (Lemma 2)

Let `W` be the rooted `m`-ary tree of all finite words over `Z/m` (zero letters allowed). The
formulas of Lemma 1 make sense on `W`. They define an action of `B = Z/m * Z/m`: `b^u b^v = b^(u+v)`
because `b` fixes the odd coordinates, so the `J_i` do not change; `b^m` acts trivially because
`t^m = 1`; the same holds for `d`. The action preserves lengths and prefixes, so `B` acts on `W` by
tree automorphisms, and `T_B`'s vertex set (words with `x2, x3, ... != 0`) is an invariant subset on
which it is the tree action.

**Lemma 2.** The kernel of `B` on `W` is `Lambda_B`.

*Proof.* The kernel on `W` is contained in the kernel on the subset `T_B`, which is `Lambda_B`.
Conversely let `beta in Lambda_B` and `w in W`. The multiplier applied to a coordinate by `b^u` or
`d^u` is `t^(u 3^J)` for a prefix sum `J` of the other parity, and `t` has order `n`, so it depends on
`J` only modulo the order `M` of `3` modulo `n` (here we use that `u 3^J` matters only mod `n`).
Replace every zero letter of `w` in positions `>= 2` by `M`; call the result `w'`, a vertex of `T_B`.
Along any word in `b^(±1), d^(±1)`, the images of `w` and `w'` stay congruent modulo `M`
coordinatewise, agree at the positions where `w` is nonzero, and have `0` resp. `M · (unit)` at the
other positions: this holds at the start, and each generator multiplies coordinates by units depending
only on prefix sums modulo `M`. Since `beta w' = w'`, the nonzero coordinates of `w` are fixed by
`beta`, and the zero coordinates stay `0`. So `beta w = w`. ∎

## 3. Self-similarity, level groups and the stabilization lemma

**Sections.** For `g in B` and a letter `x`, write `g(x w) = g(x) · g|_x(w)`. From Lemma 1, with the
shifted word `w` read with its own parities:
- `b^u(x w) = x · d^(u 3^x)(w)`: the odd coordinates of `w` are the even ones of `x w`, multiplied by
  `t^(u 3^x 3^(K))` with `K` the even prefix sum of `w`;
- `d^u(x w) = (x t^u) · b^u(w)`.

So `b^u|_x = d^(u 3^x)`, `d^u|_x = b^u`, and `(gh)|_x = g|_(h(x)) h|_x`: the action on `W` is
self-similar and every section of an element of `B` is again (the image of) an element of `B`.
(Along the word of `R`, the Gamma-side section of the push rules is the image of this one under
`sigma^2`, which swaps `b` and `d` once per letter; eight letters give no swap, so `beta^R` is the
section of `beta` at the vertex `R = (-1,-1,1,1,-1,-1,1,1)` of `W`.)

**Level groups.** Let `G_k` be the image of `B` in `Sym((Z/m)^k)` and `St_k` its kernel. Since `b^n`
and `d^n` act trivially on `W` (Lemma 2 and w13 item 1), `d^(u 3^x)` depends on `3^x mod n`, hence
on `x mod M`. So an element of `G_k` is a pair `(s, (h_r)_{r in Z/M})`, `s in Z/n`, `h_r in G_(k-1)`,
acting by `x w -> t^s x · h_(x mod M)(w)`. From `(gh)|_x = g|_(h(x)) h|_x`:
- `g o b = (s, r -> h_r o d^(3^r))`,
- `g o d = (s + 1, r -> h_(t r mod M) o b)`.

`G_k` is the closure of `{1}` under `o b` and `o d` (a finite group: every inverse is a positive
power).

**Lemma 3 (stabilization).** If `|G_k| = |G_(k+1)|` for some `k`, then `Bbar ≅ G_k`.

*Proof.* `g in St_(j+1)` iff `g in St_1` and every section `g|_x` lies in `St_j`. If
`St_k = St_(k+1)` (equivalently `|G_k| = |G_(k+1)|`), then for `g in St_(k+1)` the sections lie in
`St_k = St_(k+1)`, so `g in St_(k+2)`. By induction `St_k = St_j` for all `j >= k`, so
`St_k = ∩_j St_j`, which is the kernel on `W`, which is `Lambda_B` by Lemma 2. ∎

## 4. Exact computation of Bbar_e for e = 5..9 (item 1)

`levels_ck.py e K` builds `G_1, G_2, ...` in turn. Each `G_k` is found as the closure of `{1}`
under the two rules of section 3, applied to rows `(s, h_0, ..., h_(M-1))` whose entries `h_r` are
ids in `G_(k-1)`. It stores the right multiplication tables `Rb`, `Rd` and the rows. Rows are
deduplicated by a 64-bit hash during the search, so the search itself is not trusted. Instead
`verify.py` (and the same check at the top of `rel.py`) verifies each level exactly, with no
hashing:
- row 0 is the identity;
- for every row `g`, the rows `Rb[g]` and `Rd[g]` are exactly `g o b` and `g o d` as given by the
  rules of section 3, computed from the level `k-1` tables (the trivial group for `k = 1`);
- the rows are pairwise distinct (lexicographic sort).

By induction on `k`, the level `k-1` tables are the exact Cayley graph of `G_(k-1)`. Distinct rows
are then distinct elements of `G_k`. The row set contains `1`, is closed under `o b` and `o d`, and
consists of elements of `G_k`, so it is all of `G_k`. Hence the tables are the exact Cayley graph
of `G_k`.

Results, with `|G_1|, |G_2|, ...` up to the first repetition:

| e | M | `|G_1|, |G_2|, ...` | stable | `|Bbar|` | ord `b` |
|---|---|---|---|---|---|
| 5 | 2 | `2^3, 2^6, 2^6` | `k = 2` | `2^6` | 8 |
| 6 | 4 | `2^4, 2^9, 2^9` | `k = 2` | `2^9` | 16 |
| 7 | 8 | `2^5, 2^12, 2^13, 2^13` | `k = 3` | `2^13` | 32 |
| 8 | 16 | `2^6, 2^15, 2^17, 2^17` | `k = 3` | `2^17` | 64 |
| 9 | 32 | `2^7, 2^18, 2^22, 2^22` | `k = 3` | `2^22` | 128 |

The data are in `verify_all-output.txt` (e = 5..8, rebuilt from scratch and each level verified)
and `lev9.out` plus `rel-e9-output.txt` (e = 9: level 3 checked by `verify.py`, level 4 by
`rel.py`). By Lemma 3, `|Bbar_e|` is as in the table. For `e = 5, 6, 7` it agrees with w13's
permutation-group orders (`d1.g`, `d3.g`), which were computed on `T_B` directly.

In every case `ord b = n = m/4` in `Bbar`. This is `b^q in Lambda_B iff n | q` (w13, item 5).

**Corroboration (not load-bearing).** `orbits.py` builds the permutation action of `b, d` on a
union of `B`-orbits of random vertices of `T_B`, using the closed form of Lemma 1. `ord2.g` then
computes its order (`e567.out`, `e8.out`). Such an image is a quotient of `Bbar`. It has order
`2^6, 2^9, 2^13, 2^17` for `e = 5..8` at distance 4, so it *is* `Bbar`. GAP gives:
- for `e = 5`: abelian of exponent 8;
- for `e = 6, 7, 8`: nilpotency class `e - 4`, derived length 2 and exponent `m/4`.

## 5. Reducibility for e = 8, 9 (item 2)

By section 4, `Bbar_8` and `Bbar_9` are finite. The argument of w13 item 2 applies verbatim:
- `Lambda_A = sigma^-1(Lambda_B)`, so `[A : Lambda_A] = [B : Lambda_B]`;
- `Lambda_A x Lambda_B` has index `|Bbar|^2` in `Gamma_e`;
- each factor is an infinite (w13 item 1) finite-index subgroup of `Z/m * Z/m`, so it is virtually
  free of rank at least 2.

So `Gamma(3,256)` and `Gamma(3,512)` are reducible lattices. By w13's downward inheritance, so is
every `Gamma(3,2^e)` with `e <= 9`.

## 6. (H_e) holds exactly for e <= 8 (item 3)

`beta^R` is the section of `beta` at the vertex `R` of `W` (section 3). If `beta in Lambda_B` then
`beta` fixes `W` pointwise (Lemma 2), so all its sections lie in `Lambda_B`. Together with
`(gh)|_x = g|_(h(x)) h|_x`, this shows that `beta'' mod Lambda_B` depends only on `beta mod Lambda_B`.
So `(H_e)` is a statement about the `|Bbar|` elements of `G_K`.

`rel.py e K` evaluates, for every `g in G_K`:
- `g^R`, as the model section along the eight letters of `R`. It uses `pi^-1`, the isomorphism
  `G_(K-1) -> G_K`, which is inverted exactly (`pi` is a bijection at a stable level);
- `g'' = g^R g^-1`, with the product taken along a BFS spanning tree of the Cayley graph.

Results:
- at `e = 7` and `e = 8`: `g'' = 1` for all `2^13`, resp. `2^17`, elements (`rel-e7-output.txt`,
  `rel-e8-output.txt`). So `(H_7)` and `(H_8)` hold;
- at `e = 9`: `g''` is nontrivial for `2621440` of the `2^22` elements (section 8).

**Cross-check against an independent computation.** `symsec.py` computes the sections of the free
word `b d` symbolically, for any `e`. At `e = 9` and `e = 10` the letters of `(b d) · R` that it
prints equal the exponents of w13's `S_(b d)` in `hfail-output.txt`, and
`(b d)'' = b^64 = b^320 mod n` at `e = 9`. The same value at `e = 9` is found independently by
`rel.py`: `(b d)'' = b^64` (`rel-e9-output.txt`).

Combining these:
- `(H_e)` holds for `e = 3..6` (w13) and for `e = 7, 8` (here);
- `(H_e)` fails for every `e >= 9` (w13, item 5).

So `(H_e)` holds if and only if `e <= 8`. By w13's reduction lemma:
- for `e = 7, 8`, `Abar_e = <a, c | a^m, c^m, S_beta (beta in Bbar_e)>` embeds in `Qbar_B` with
  index `|Bbar_e|`;
- `relators.py` writes the relators. Up to rotation and inversion they number 64, 512, 8192 and
  90112 for `e = 5..8`.

`symsec.py` also gives `(b d)'' = b^q` modulo `n`, with `q = 64, 64, 320, 832, 1856, 3904, 3904,
3904` for `e = 9..16`. That is, `q = 64 v` with `v` odd, and `n` does not divide `q`. This is the
B-side form of w12's `b^(64v) in Abar`.

## 7. The relative Freiheitssatz at e = 9 (item 4)

Let `e = 9`. Put `u = b^64` and `v = d^64` in `Bbar = Bbar_9`, and `Bbar_0 = <u, v>`.

**(a) The defects.** `rel.py 9 4` (`rel-e9-output.txt`) finds:
- `beta''` takes exactly four values on `Bbar`:
  - `1`, `3 · 2^19` times;
  - `u`, `2^19` times;
  - `v`, `2^19` times;
  - a fourth value, `3 · 2^19` times;
- `Bbar_0` has order 4 and contains every `beta''`, so the fourth value is `uv`. Since `ord b = 128`,
  `Bbar_0 = (Z/2)^2`;
- `u` and `v` are central in `Bbar`;
- `Bbar_0` is closed under the swap `sigma^2` and under all one-letter sections;
- the smallest subgroup that contains all `beta''` and is closed under swap and sections is
  `Bbar_0` itself (`sec_closed_hull`).

**(b) `H := A · Bbar_0` is a subgroup of `Q_B`, and `H = A ⋊ Bbar_0`.** In `Q_B`, the push rules of
section 0 with `q = 64` give `u a = a b^192 = a u` and `u c = c^(t^64) u`. The first holds because
`b` has order 128 in `Bbar`. Moreover `t^64 = 3^-64 = 257 mod 512`, since `v_2(3^64 - 1) = 8`.
Likewise `v c = c v` and `v a = a^257 v`. So `u` and `v` normalize `A`, with
`u a u^-1 = a`, `u c u^-1 = c^257`, `v a v^-1 = a^257` and `v c v^-1 = c`.

The factorization `Q_B = A · Bbar` is exact (`A ∩ B = 1` in `Gamma` and `Lambda_B <= B`). So
`A ∩ Bbar_0 = 1`, and `H ≅ (Z/512 * Z/512) ⋊ (Z/2)^2` with this action.

**(c) `M := <<R>>_(Q_B) <= H`.** Every `q in Q_B` is `alpha beta` with `alpha in A <= H` and
`beta in Bbar`. So `M` is the `H`-normal closure of the `beta R beta^-1 = S_beta beta''`
(`beta in Bbar`), and each of these lies in `A · Bbar_0 = H` by (a). Hence
`M = << S_beta beta'' : beta in Bbar >>_H <= H`.

**(d) Consequences.**
- `H/M -> Q_B/M = Qbar_B` is injective with index `[Bbar : Bbar_0] = 2^20`, by exactness.
- The relators give `u = S_beta^-1` for any `beta` with `beta'' = u` (for example `beta = b d`),
  and likewise for `v`. So `H/M` is generated by `a, c`: it is the image `Abar^Q` of `A` in
  `Qbar_B`.
- Eliminating `u, v` gives a presentation of `Abar^Q`:
  - generators `a, c`, with `U := S_(bd)^-1` and `V := sigma^2(S_(bd))^-1`;
  - relators `a^512`, `c^512`, `U^2`, `V^2` and `[U, V]`;
  - `[U, a]`, `U c U^-1 c^-257`, `[V, c]` and `V a V^-1 a^-257`;
  - `S_beta · w(beta'')` for `beta in Bbar`, where `w(1) = 1`, `w(u) = U`, `w(v) = V` and
    `w(uv) = UV`.
- In particular `ord(a in Qbar_B) = ord(a in Abar^Q)`.

This is the exact replacement of `(H_e)` at `e = 9`. The embedded subgroup changes from
`Abar_e` (index `|Bbar|`) to `Abar^Q = H/M` (index `|Bbar|/4`). The twisted relators acquire the
four-valued tail `w(beta'')`, and there are seven semidirect-product relations.

**The obstruction it records.** `Bbar_0` is minimal, so no subgroup `A · Bbar_1` with
`Bbar_1 < Bbar_0` contains `M`. Moreover `A · Bbar_0` does not lose `a`: `ord(a)` through `H/M` is
*equal* to `ord(a)` through `Qbar_B`. So the relative step gives an equivalent 2-generated problem,
not a lower bound by itself. A lower bound needs a finite quotient of `Abar^Q`, and section 9 shows
that none of nilpotency class at most 10 is 2-power with `ord(a) = 2^9`.

## 8. Qbar_B directly, and the lower bound (item 5)

**Lemma.** `Lambda_B = << rho : rho a relator of Bbar_e in b, d >>_Gamma`. Hence
`Qbar_B = Gamma_e / << rho's, R >>`, a quotient of `Gammabar_e`.

*Proof.* `Lambda_B` is normal in `Gamma` and contains the `rho`'s. Conversely,
`Lambda_B = <<rho's>>_B`, which lies in `<<rho's>>_Gamma`. ∎

`qbpq.g` reads `bbar_e<e>.g`, the right regular representation written by `qbexport.py`. It takes
a presentation of `Bbar_e` from GAP and checks it on the permutations. It then computes
2-quotients of `Qbar_B`, re-checking every relator in any quotient where `ord(a) = 2^e`:
- `e = 6`: class 9, order `2^123`, `ord(a) = 2^6`: a certificate (`qbpq-e6.out`);
- `e = 7`: class 11, order `2^302`, `ord(a) = 2^7`: a certificate (`qbpq-e7.out`). So `ord(a) = 2^7`
  in `Gammabar_7`. This was already implied by class 11 of w10's `diag_tower.g`, but the certificate
  here uses a different group;
- `e = 8`: classes 11, 12, 13 have orders `2^306`, `2^480`, `2^782`, all with `ord(a) = 2^7`
  (`qbpq-e8.out`). Class 14 exceeds the 1200 s budget.

`Gammabar_e` maps onto `Gammabar_7` for `e >= 7`, with `a -> a`. So `ord(a in Gammabar_e) >= 2^7`
for every `e >= 7`. No better lower bound is proved here for `e >= 8`.

`abarpq.g` on `Abar_7` (8192 relators) reaches only class 5 (`ord(a) = 2^4`) in the budget
(`abarpq-e7.out`). So for 2-quotients, the `Abar_e` form is slower than `Qbar_B` itself.

## 9. A class bound for 2-quotients at e = 9 (item 6)

In `Gamma_9`, w13's `hfail-output.txt` gives `(b d) R (b d)^-1 = S · b^320`, with `S = S_(bd)` an
explicit word of syllable length 8 in `a, c`. Hence in `Gammabar_9`:
- `b^320 = S^-1`, so `U := S^-5 = b^1600 = b^64` lies in the image `Abar` of `A`;
- the defining relations of `Gamma` give `a^-1 U a = U^3`, `U^-1 c U = c^(3^64) = c^257` and
  `U^8 = 1`;
- applying `sigma^2` (which maps `R` to `R^-1`) gives the same with `a <-> c`, for
  `V := sigma^2(S)^-5 = d^64`.

So `Abar <= Gammabar_9` is a quotient of
`Etest2 = < a, c | a^512, c^512, R, U^a = U^3, c^U = c^257, U^8, V^c = V^3, a^V = a^257, V^8 >`
(`abartest.g` with `BOTH := true`).

`EpimorphismPGroup` gives the largest class-`k` 2-quotient of `Etest2` (`abartest2-e9-output.txt`):

| class k | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---|---|---|---|---|---|---|---|---|---|
| log2 order | 2 | 5 | 9 | 14 | 22 | 32 | 51 | 77 | 124 | 197 |
| log2 ord(a) | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 8 | 8 |

Class 11 exceeds the 1200 s budget.

**Consequence.** Let `P` be a 2-group quotient of `Gammabar_9` of class at most 10. The image of `A`
in `P` is a 2-group of class at most 10 that is a quotient of `Etest2`. It is therefore a quotient
of the class-10 quotient above, so `ord(a in P) <= 2^8`. The same holds for 2-quotients of
`Qbar_B`, which is a quotient of `Gammabar_9`. It also holds for 2-quotients of `Abar^Q`, which is
itself a quotient of `Etest2`: its relators of section 7(d) imply those of `Etest2`, because
`U^2 = 1` turns `[U,a] = 1` into `U^a = U^3`, and `R in M`.

Hence **no 2-quotient of class at most 10 certifies `ord(a) = 2^9` in `Gammabar_9`**.

The `d`-side relations are what cause this. With only `U` (`abartest.g` without `BOTH`), class 9
already has `ord(a) = 2^9` (`abartest-e9-output.txt`). For comparison, the first certifying class
is 9 at `e = 6` and 11 at `e = 7`.

The `e = 10` analogue is `abartest10.g`, built from `(b d) R (b d)^-1 = S · b^832` and
`U = S^-5 = b^64`, with `U^16 = 1`. Through class 8 it gives the same orders (log2
`2, 5, 9, 14, 22, 32, 51, 77`) and `ord(a) = 2^8` at class 8. Class 9 exceeds the budget
(`abartest10-e10-output.txt`).

## 10. Dead ends

- **Hash-deduplicated search as proof.** It is replaced by the exact verification of section 4.
- **`Abar_e` 2-quotients at `e >= 7`.** The relator count makes them slower than `Qbar_B`
  (section 8).
- **`Qbar_B` 2-quotients at `e = 8`.** They stay at `ord(a) = 2^7` through class 13, while the
  order grows by a factor of about `2^200` to `2^300` per class. This is class growth, not a proven
  bound.
- **`Etest2` beyond class 10.** Stopped by the budget. Whether `ord(a) = 2^8` persists in every
  class is open.
