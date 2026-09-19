---
rg: 2
id: higman-j-odometer-models-restrict-to-single-cycle-models-proof
kind: route
title: Proof by restriction to the stabilizer of a level-J vertex (a Reidemeister-Schreier step done on the tree), a 2-adic reduction of the exponents, an exact SAT extension test cross-checked against the lifter, a GAP check of a level-8 model with a = x -> x + 4, and GAP's 2-quotient algorithm
target: higman-j-odometer-models-restrict-to-single-cycle-models
requires:
  - higman-h4-3-two-orbit-odometer-models-stop-at-level-seven
  - higman-h4-3-has-no-odometer-models-beyond-level-five
artifacts:
  - experiments/higman-subtree-reduction-2026-09-19/glift.c
  - experiments/higman-subtree-reduction-2026-09-19/satlift.py
  - experiments/higman-subtree-reduction-2026-09-19/exact.sh
  - experiments/higman-subtree-reduction-2026-09-19/randgrid.sh
  - experiments/higman-subtree-reduction-2026-09-19/results.txt
  - experiments/higman-subtree-reduction-2026-09-19/model-j2-level8.g
  - experiments/higman-subtree-reduction-2026-09-19/verify.g
  - experiments/higman-subtree-reduction-2026-09-19/verify-j2-level8-output.txt
  - experiments/higman-subtree-reduction-2026-09-19/pq.g
  - experiments/higman-subtree-reduction-2026-09-19/pq-output.txt
  - experiments/higman-subtree-reduction-2026-09-19/pq4.g
  - experiments/higman-subtree-reduction-2026-09-19/pq48.g
---

The notation is that of the target claim. Lemmas 1 to 3 and the Corollary are proved in full. Items 3 to 6 of the
claim are computations, reproducible from the listed artifacts; item 5 is in addition a certificate that GAP checks
independently.

**Conventions.** As in `higman-h4-3-two-orbit-odometer-models-stop-at-level-seven-proof`: permutations act on the
right, `x^y = y^-1 x y`, `W_k` acts on `Z/2^k`, and `g` is a tree automorphism exactly when `x = y mod 2^m`
implies `xg = yg mod 2^m`. Bit `j` of `xg` is `x_j XOR s_g(j, x mod 2^j)` for switch bits `s_g`. A `J`-odometer
model of level `k` is a homomorphism `phi` from `H4(3)` (or from `H4(3)/<<R>>`, `R = [a,c]^2`) to `W_k` with
`a -> (x -> x + 2^J)`. For `n_1, ..., n_4` odd put
`H(n_1,n_2,n_3,n_4) = < a,b,c,d | b^a = b^(n_1), c^b = c^(n_2), d^c = d^(n_3), a^d = a^(n_4) >`, so
`H4(3) = H(3,3,3,3)`, and let `w_0(n_1,...,n_4)` be the largest level carrying a `0`-odometer (single-cycle) model
of `H(n_1,...,n_4)`, with no `R` imposed (`infinity` if there is none).

## Lemma 1 (subtree reduction)

Let `J <= k` and let `phi` be a `J`-odometer model of `H4(3)` of level `k`. Fix a level-`J` vertex `i`. Let
`m_b, m_c, m_d` be the lengths of the orbits of `i` under the level-`J` images of `b, c, d`. Identify the subtree
`T_i` below `i` with the level-`(k-J)` tree by `y <-> i + 2^J y`. Then `a`, `b' = b^(m_b)`, `c' = c^(m_c)` and
`d' = d^(m_d)` fix `i`. Their restrictions to `T_i` form a `0`-odometer model of level `k - J` of
`H(3, 3^(m_b), 3^(m_c), 3^(m_d))`. If `m_c = 1` and `phi` kills `R`, the restricted model also kills `R`.

*Proof.* Each `m` is the least positive power fixing `i`. `a` fixes every level-`J` vertex. So all four elements
lie in `Stab(i)`, and restriction to `T_i` is a homomorphism `Stab(i) -> Aut(T_i)`. The identification is a
tree isomorphism, because the ancestor of `i + 2^J y` at level `J + r` is `i + 2^J (y mod 2^r)`. Under it `a`
becomes `y -> y + 1`, a single `2^(k-J)`-cycle. The relations of `H4(3)` give, in `Stab(i)`:
- `(b')^a = (b^a)^(m_b) = (b')^3`;
- `(c')^(b') = c^(m_c 3^(m_b)) = (c')^(3^(m_b))`, since `c^(b^j) = c^(3^j)` by induction on `j`;
- `(d')^(c') = (d')^(3^(m_c))` in the same way;
- `a^(d') = a^(3^(m_d))`.

These identities hold after restriction. If `m_c = 1` then `c' = c`, so `[a, c']^2 = R`. ∎

This is the Reidemeister-Schreier step of the brief, done on the tree. The four elements `a, b', c', d'` are
Schreier generators of the stabilizer of `i`. We do not need the full Schreier presentation, only the four
relations above, which the restriction satisfies.

**Corollary.** Let `phi` be a `J`-odometer model of level `k`. For every level-`J` vertex `i`,
`k - J <= w_0(3, 3^(m_b(i)), 3^(m_c(i)), 3^(m_d(i)))`. Orbit lengths in `W_J` are powers of two at most
`2^J`, so `log2 ord(a) = k - J <= max { w_0(3, 3^(m_b), 3^(m_c), 3^(m_d)) : m_b, m_c, m_d in {1, 2, 4, ..., 2^J} }`.
When `phi` kills `R`, the vertices with `m_c(i) = 1` give the sharper bound with `R` imposed.

*Proof.* Every vertex gives a restricted model of level `k - J` by Lemma 1, and `ord(a) = 2^(k-J)`. ∎

## Lemma 2 (the exponents matter only 2-adically)

Let `n_i = n'_i mod 2^(k+1)` for each `i`. Then the level-`k` `0`-odometer models of `H(n_1,...,n_4)` and of
`H(n'_1,...,n'_4)` coincide.

*Proof.* Every element of `W_k` has order dividing `2^k`, so `g^n = g^(n')` whenever `n = n' mod 2^k`. ∎

So `w_0` depends on the `n_i` only through their classes in the 2-adic integers. As `s -> infinity`,
`3^(2^s) -> 1`, and `H(3,3,3,3^(2^s))` approaches the degenerate group where `d` commutes with `a`. This matches
the growth in item 4 of the claim.

## Lemma 3 (the SAT extension test is exact, and canonical bases suffice)

`satlift.py J K` takes a level-`B` model and builds a CNF. Its variables are the switch bits `s_g(j, y)` for
`g in {b, c, d}`, `B <= j < K` and `y < 2^j`.
- `a` is fixed. Its switch at bit `j >= J` is the carry out of bits `J..j-1`.
- For each relator `w` and each point `x` of `Z/2^K`, the image `x w` is followed letter by letter.
- Bits below `B` of every path point are constants from the base model. Higher bits are literals, built with the
  gates `xor`, `and` (carry and borrow) and `mux` (switch lookup). An inverse letter uses its own output bits as
  selectors, which is correct because `s_g(j, .)` is read at the image point for `g^-1`.
- A power `g^e` is walked `e mod 2^(K+1)` times, by Lemma 2.
- The clauses assert `x w = x` bit by bit.

The CNF is satisfiable exactly when the base extends to a level-`K` model. Every satisfying assignment is
rebuilt into permutations of `Z/2^K`. These are checked directly as tree automorphisms satisfying every relator,
and the script asserts this check.

Only canonical representatives of the base classes are tested, and this is enough. Lemma 1 of
`higman-h4-3-two-orbit-odometer-models-stop-at-level-seven-proof` says that restriction maps the centralizer of
the `J`-odometer at level `K` onto the centralizer at level `B`. So each conjugating element of the lower level
lifts, and conjugate bases extend together.

Calibration against the lifter `glift.c`, which is `jlift.c` of w18 with general exponents:
- `H(3,3,3,3)` from the 16 level-2 classes:
  - `K = 5`: with `R`, exactly 1 class extends, and it is the common level-2 restriction of all 736 of
    `glift`'s level-5 classes; without `R`, 2 classes extend;
  - `K = 6`: none extend, with or without `R`, as `glift` finds;
- `J = 1`, `K = 8` with `R`: none of the 20 tested level-3 bases extend, as `w18` finds.
- `glift` itself reproduces w17's and w18's counts exactly:
  - `J = 0`: `8, 16, 48, 192, 736, 0` with `R` and `8, 16, 72, 544, 9728, 0` without `R`;
  - `J = 1` with `R`: `8, 80, 332, 1908, 24336, 318432, 11776, 0`.

## Lemma 4 (the cap, item 3)

Let `x^y = x^3` in a group, with `y^(2^m) = 1` and `x` of 2-power order. Then `x^(2^(m+2)) = 1`.

*Proof.* Conjugating `2^m` times gives `x = x^(y^(2^m)) = x^(3^(2^m))`, so `x^(3^(2^m) - 1) = 1`. For `m >= 1`,
`v_2(3^(2^m) - 1) = v_2(3 - 1) + v_2(3 + 1) + (m - 1) = m + 2` by the lifting-the-exponent lemma. For `m = 0`
it is `v_2(2) = 1`. Since `ord(x)` is a power of two, it divides `2^(m+2)`. ∎

Apply it to `a^d = a^3`, `d^c = d^3` and `c^b = c^3` in a finite 2-group. This gives
`ord(a) <= 4 ord(d)`, `ord(d) <= 4 ord(c)` and `ord(c) <= 4 ord(b)`, which is item 3. The first inequality is
w18's ladder.

## Computations

All runs are single-threaded, under `nice -n 10 timeout 1200`. `results.txt` collects their outputs.

**Item 4.** `exact.sh e=n1,n2,n3,n4 3 K noR` does two things:
- It lists the canonical level-3 single-cycle classes with `glift 0 3 noR e=... dump`. There are 108 for
  `(3,3,3,9)`, 72 for `(3,3,9,3)` and 88 for `(3,9,3,3)`.
- It runs `satlift.py 0 K` on each class.

The results at `K = 7`:
- `(3,3,3,9)`: 0 of the 108 classes extend;
- `(3,3,9,3)`: 0 of the 72 classes extend;
- `(3,9,3,3)`: 6 of the 88 classes extend.

By Lemma 3 this proves `w_0(3,3,3,9) <= 6` and `w_0(3,3,9,3) <= 6`. The random probe reaches level 6 for
both, and those models give the matching lower bounds. For `(3,9,3,3)`, the `K = 8` test did not finish
within 1200 s, so only `w_0 >= 7` is known.

`randgrid.sh` runs the random existence probe `glift 0 10 noR e=3,3^mb,3^mc,3^md rand=8,1 first`. This probe
keeps random lifts without isomorph rejection. Every model it keeps satisfies the lifting system exactly, so
each "deepest" entry is a proved lower bound on `w_0`. The triple `(2,4,4)` found nothing within the time
limit, and it is left out of the table. For `(4,4,2)` the probe reached its own limit, level 10.

**Item 5.**
- `glift 2 2 dump` lists the 80 canonical level-2 classes of `2`-odometer models of `H4(3)/<<R>>`. Of these,
  37 are transitive at level 2, and hence at every level, because `a` is transitive below each level-2 vertex.
- `satlift.py 2 8` finds level-8 extensions of the first three transitive classes. Each took between 59 s and
  181 s.
- The first of these extensions is `model-j2-level8.g`, which grows from the base `b = id`,
  `c = (1 3)`, `d = x -> x + 1` on `Z/4`.
- `verify.g` (w18's script, unchanged) checks it independently. The relators of `H4(3)` and `R` are
  trivial, the generators are tree automorphisms, and `a` has four orbits of length 64. The group is a
  transitive 2-group of order `2^41` and 2-class 20, with `ord(a,b,c,d) = (64,4,4,16)`.

Two other runs support the rest of item 5, and neither is exhaustive:
- A satisfiable run from the level-2 class `b = c = id`, `d = x -> x + 2` gives an intransitive model of order
  `2^42`. It is a pair of `J = 1` models of level 7, as w18's level-1 lemma predicts.
- The random probe `glift 2 10 rand=32,11 first` keeps at most 32 random lifts per class. Its classes at
  level 8 number 2400 on the first pass and 3968 on later passes. It has none at level 9.

`satlift.py 2 9` did not finish within 1200 s on the first transitive class.

**Item 6.** `pq.g` calls `EpimorphismPGroup(G, 2, cl)` for `G = H4(3)/<<R>>` and records `|P_cl|` and the
orders of the images of `a, b, c, d`. Classes 1 to 11 finished within one 1200 s run; class 12 did not. Class 11 alone takes 167 s.
An attempt to cut `P_11` down to a small quotient that still has `ord(a) = 128` did not finish. The attempt
factored out a complement of `<a^64>` in `Omega_1(Z(P_11))`, which has rank 501, and it timed out on the
first quotient. The
runs with the extra relators `b^4, c^4` and `b^4, c^8` are `pq4.g` and `pq48.g`, the same script with those
relators added; both reached class 12. Every finite 2-quotient of
`G` is a quotient of some `P_cl`, so `ord(a) = 128` in `P_11` exhibits a finite 2-quotient with
`ord(a) = 128`. The tier is computed: it rests on GAP's `p`-quotient implementation.
