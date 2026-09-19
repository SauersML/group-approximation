---
rg: 2
id: higman-j-odometer-models-restrict-to-single-cycle-models
kind: claim
title: A tree model of H4(3) with a acting as x -> x + 2^J restricts on every level-J subtree to a single-cycle model of H(3, 3^(m_b), 3^(m_c), 3^(m_d)); J = 2 models reach level 8 with ord(a) = 64, while the class-11 2-quotient of H4(3)/<<[a,c]^2>> already has ord(a) = 128
distinct_from:
  higman-h4-3-two-orbit-odometer-models-stop-at-level-seven: that enumerates the J = 1 family exhaustively; this reduces every J to single-cycle models of twisted Higman groups, builds a GAP-checked transitive J = 2 model at level 8, and shows by the 2-quotient algorithm that no J <= 2 odometer family reaches the orders of a that finite 2-quotients reach.
  higman-h4-3-has-no-odometer-models-beyond-level-five: that is the J = 0 wall w_0(3,3,3,3) = 5; this varies the exponents to (3, 3^(m_b), 3^(m_c), 3^(m_d)), which is what the subtree of a J-odometer model sees.
  higman-power-pair-collapse-is-base-uniform-up-to-torsion: that asks whether H4(3)/<<[a,c]^2>> has generators of infinite order; this does not settle it, and gives finite 2-quotients with ord(a) = 128 as evidence that the tree-model walls come from the odometer shape, not from a.
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

**ESTABLISHED** (proposed; items 1 to 3 proved, items 4 to 6 computed, item 5 certified) by
`higman-j-odometer-models-restrict-to-single-cycle-models-proof`.

**Setting.** `H4(3) = < a,b,c,d | b^a = b^3, c^b = c^3, d^c = d^3, a^d = a^3 >` and `R = [a,c]^2`, as in the
target. For odd `n_i` put `H(n_1,n_2,n_3,n_4) = < a,b,c,d | b^a = b^(n_1), c^b = c^(n_2), d^c = d^(n_3),
a^d = a^(n_4) >`. A `J`-odometer model of level `k` is a homomorphism to the Sylow 2-subgroup `W_k` of
`S_(2^k)`, acting on `Z/2^k`, with `a -> (x -> x + 2^J)`. Then `ord(a) = 2^(k-J)`. Write `w_J` for the largest
such `k` for `H4(3)/<<R>>`, and `w_0(n_1,...,n_4)` for the largest level of a single-cycle (`J = 0`) model of
`H(n_1,...,n_4)` with no `R` imposed. Known values are `w_0 = 5` for `H4(3)` and `w_1 = 7`, both from
exhaustive searches by earlier lanes.

**Statement.**
1. **Subtree reduction.** Let `phi` be a `J`-odometer model of level `k`, and let `i` be a level-`J` vertex
   whose orbits under `b, c, d` at level `J` have lengths `m_b, m_c, m_d`.
   - `a, b^(m_b), c^(m_c), d^(m_d)` fix `i`.
   - On the subtree below `i` they form a single-cycle model of level `k - J` of
     `H(3, 3^(m_b), 3^(m_c), 3^(m_d))`.
   - If `m_c = 1`, the restricted model still kills `R`.

   Hence, for every vertex `i`, `log2 ord(a) = k - J <= w_0(3, 3^(m_b(i)), 3^(m_c(i)), 3^(m_d(i)))`, where the
   `m`'s are powers of two at most `2^J`.
2. **2-adic exponents.** The level-`k` single-cycle models of `H(n_1,...,n_4)` depend on the `n_i` only through
   their residues mod `2^(k+1)`.
3. **The cap.** In any group, if `x^y = x^3` and `y^(2^m) = 1`, then `x^(2^(m+2)) = 1` when `x` has 2-power
   order. So, in a finite 2-quotient of `H4(3)`:
   - `ord(a) <= 4 ord(d) <= 16 ord(c) <= 64 ord(b)`;
   - `c^4 = 1` forces `ord(a) <= 64`, and `ord(a) > 64` needs `ord(c) >= 8` and `ord(d) >= 32`.
4. **Single-cycle walls of the twisted groups** (the inputs to item 1), all without `R`:
   - exact, by SAT on all canonical level-3 classes: `w_0(3,3,3,9) = 6` and `w_0(3,3,9,3) = 6`;
   - lower bounds: `w_0(3,9,3,3) >= 7`. A random existence probe gives the lower bounds `w_0 >= deepest` in
     the table below. Each entry is the deepest level at which the probe found a model.

   | `(m_b,m_c,m_d)` | deepest | `(m_b,m_c,m_d)` | deepest | `(m_b,m_c,m_d)` | deepest |
   |---|---|---|---|---|---|
   | (1,1,1) | 5 | (2,1,1) | 7 | (4,1,1) | 8 |
   | (1,1,2) | 6 | (2,1,2) | 7 | (4,1,2) | 8 |
   | (1,1,4) | 7 | (2,1,4) | 8 | (4,1,4) | 8 |
   | (1,2,1) | 6 | (2,2,1) | 7 | (4,2,1) | 8 |
   | (1,2,2) | 7 | (2,2,2) | 8 | (4,2,2) | 8 |
   | (1,2,4) | 8 | (2,2,4) | 9 | (4,2,4) | 9 |
   | (1,4,1) | 7 | (2,4,1) | 8 | (4,4,1) | 8 |
   | (1,4,2) | 8 | (2,4,2) | 9 | (4,4,2) | >= 10 (probe limit) |
   | (1,4,4) | 9 | | | (4,4,4) | 9 |

   For `m_b = 1` the table reads `5 + log2 m_c + log2 m_d`. This is consistent with item 2: `3^(2^s) -> 1`
   2-adically, so these groups approach degenerate ones in which a pair of generators commutes.
5. **`J = 2` reaches level 8.** There is a transitive `2`-odometer model of `H4(3)/<<R>>` of level 8, so
   `w_2 >= 8`. GAP checks it: degree 256, order `2^41`, 2-class 20, `ord(a,b,c,d) = (64,4,4,16)`. The model
   is `model-j2-level8.g`.
   - Of the 80 level-2 classes, 37 are transitive. The first three of these all extend to level 8.
   - A random lifting probe finds 3968 level-8 classes and none at level 9. This is not exhaustive, so
     `w_2 = 8` is not proved, and neither is the guessed `w_2 = 9` (the `5 + 2J` fit).
   - Every tree model found so far, over `J = 0, 1, 2`, has `ord(a) <= 64`.
6. **Finite 2-quotients go further.** GAP's 2-quotient algorithm computes the largest 2-quotient `P_cl` of
   2-class `cl` of `H4(3)/<<R>>`:

   | `cl` | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 |
   |---|---|---|---|---|---|---|---|---|---|---|---|
   | `log2` of the order | 4 | 10 | 19 | 32 | 52 | 84 | 141 | 231 | 395 | 672 | 1172 |
   | `ord(a)` | 2 | 4 | 8 | 16 | 16 | 16 | 32 | 32 | 64 | 64 | 128 |
   | `ord(b)` | 2 | 4 | 8 | 16 | 32 | 64 | 64 | 64 | 64 | 128 | 128 |

   `ord(c) = ord(a)` and `ord(d) = ord(b)` at every class. So some finite 2-quotient of `H4(3)/<<R>>` has
   `ord(a) = 128`. That is twice the largest `ord(a)` of any tree model found for `J <= 2`.

   Adding relators caps the growth, as item 3 predicts:
   - with `b^4 = c^4 = 1`, `ord(a)` reaches the cap 64 at class 9 and stays there through class 12, with
     `ord(b,c,d) = (4,4,16)`;
   - with `b^4 = c^8 = 1`, `ord(a)` reaches 64 at class 9 and the cap 128 at class 12, with
     `ord(b,c,d) = (4,8,32)`.

   In both runs `ord(a) = 4 ord(d) = 16 ord(c)`, so the first two steps of the cap are attained.

**What it kills and what it leaves.**
- The odometer walls found so far say nothing about `ord(a)` in general finite 2-quotients.
  - Both GAP-checked models with `ord(a) = 64` (w18's at `J = 1` and item 5's at `J = 2`) have
    `ord(b,c,d) = (4,4,16)`. So they sit exactly on the cap of item 3.
  - The 2-quotients of item 6 grow the four orders together. No odometer model found does this; whether
    one can is open. The next tree models to search are those with `ord(c) >= 8`, which item 3 requires for
    `ord(a) > 64`, or non-uniform ones.
- Item 1 turns every `J` into single-cycle problems one exponent-twist away. It is lossy as an upper
  bound: already for `J = 1` the reduction bound exceeds `w_1 = 7` on three of the level-1 patterns.
- **The gap.** `a` has infinite order in the pro-2 completion of `H4(3)/<<R>>` exactly when `ord(a)` in `P_cl`
  is unbounded. The class at which `ord(a)` first doubles runs `1, 2, 3, 4, 7, 9, 11`. A proof that it keeps
  doubling would give a quotient of `H4(3)/<<R>>` with `a` of infinite order, namely the residually-2 image.
  It would not settle question (a), since amenability of the edge image `<a,c>` in that image is open.
