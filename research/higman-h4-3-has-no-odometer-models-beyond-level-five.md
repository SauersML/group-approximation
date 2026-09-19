---
rg: 2
id: higman-h4-3-has-no-odometer-models-beyond-level-five
kind: claim
title: For k >= 6 no homomorphism from the base-3 Higman group H4(3) to the Sylow 2-subgroup W_k of S_(2^k) sends a generator to a 2^k-cycle, so no action of H4(3) on the binary rooted tree has a level-transitive generator and every odometer-type self-similar model of H4(3)/<<[a,c]^2>> stops at level 5
distinct_from:
  higman-power-pair-collapse-is-base-uniform-up-to-torsion: that leaves open whether H4(3)/<<[a,c]^2>> has generators of infinite order; this does not settle that, and only excludes the tree models in which a generator acts level-transitively.
  higman-order-2e-models-need-exponential-rank: that bounds the linear degree and order of any quotient in which a has order 2^e and computes monolithic models whose a is semiregular; this excludes every 2-group action on 2^k points (k >= 6) in which a is one cycle, so those semiregular models cannot be straightened into odometer models.
  higman-torsion-generator-quotients-factor-through-tree-lattices: that excludes cyclically symmetric wreath recursions on T_2 with sections of length at most 2; this excludes level-transitive generators on T_2 for recursions of every length, and for non-self-similar tree actions too.
artifacts:
  - experiments/higman-odometer-lifting-2026-09-18/lift.py
  - experiments/higman-odometer-lifting-2026-09-18/bfs.py
  - experiments/higman-odometer-lifting-2026-09-18/run-withR-output.txt
  - experiments/higman-odometer-lifting-2026-09-18/run-noR-output.txt
  - experiments/higman-odometer-lifting-2026-09-18/rawcount.py
  - experiments/higman-odometer-lifting-2026-09-18/rawcount-withR-output.txt
  - experiments/higman-odometer-lifting-2026-09-18/rawcount-noR-output.txt
  - experiments/higman-odometer-lifting-2026-09-18/xcheck.g
  - experiments/higman-odometer-lifting-2026-09-18/xcheck-output.txt
  - experiments/higman-odometer-lifting-2026-09-18/analyze5.py
  - experiments/higman-odometer-lifting-2026-09-18/analyze5-output.txt
  - experiments/higman-odometer-lifting-2026-09-18/bfs2.py
  - experiments/higman-odometer-lifting-2026-09-18/bfs2-j1-output.txt
---

**ESTABLISHED** (proposed, computed) by `higman-h4-3-has-no-odometer-models-beyond-level-five-proof`.

**Setting.** `H4(3) = < a, b, c, d | b^a = b^3, c^b = c^3, d^c = d^3, a^d = a^3 >`, with
`x^y = y^-1 x y`, `[x,y] = x^-1 y^-1 x y`, and `R = [a,c]^2`. `W_k` is the Sylow 2-subgroup of
`S_(2^k)`, that is, the automorphism group of the binary rooted tree truncated at level `k`. Label
the level-`k` vertices by `Z/2^k`, with `x mod 2^r` as the ancestor at level `r`. The odometer is
`x -> x + 1`. An *odometer model of level `k`* is a homomorphism `H4(3) -> W_k` that sends `a` to
the odometer.

**Statement.**
1. **No odometer model beyond level 5.** For `k >= 6` there is no homomorphism
   `phi : H4(3) -> S_(2^k)` with 2-group image in which `phi(x)` is a `2^k`-cycle for some
   generator `x` in `{a, b, c, d}`. This holds without `R`, so it holds for `H4(3)/<<R>>` too.
   Equivalently, no finite 2-group quotient `Q` of `H4(3)` has a subgroup `H` with `Q = <x> H`,
   `<x> ∩ H = 1` and `ord(x) >= 64`.
2. **Tree corollary.** No action of `H4(3)` by automorphisms of the binary rooted tree `T_2` has a
   generator that acts level-transitively. This covers self-similar actions with sections of any
   length and actions that are not self-similar. In particular the adding machine `a = (1, a) sigma`
   and every other level-transitive choice of `a` are excluded as seeds of a recursion
   `Q_(e+1) -> Q_e wr C_2`.
3. **Counts** (exhaustive, computed). Raw counts are homomorphisms to `W_k` with `a` = odometer.
   Classes are counted up to conjugation by `<a>`, which is the centralizer of `a` in `W_k`.

   | k | with R: raw | with R: classes | without R: raw | without R: classes |
   |---|---|---|---|---|
   | 1 | 8 | 8 | 8 | 8 |
   | 2 | 32 | 16 | 32 | 16 |
   | 3 | 192 | 48 | 288 | 72 |
   | 4 | 1536 | 192 | 4352 | 544 |
   | 5 | 11776 | 736 | not computed | 9728 |
   | 6 | 0 | 0 | 0 | 0 |

   An independent GAP enumeration over centralizer cosets in `W_k` (`xcheck.g`) gives the same
   raw counts for `k <= 4`.
4. **Shape at level 5** (computed; the affine form is proved). In every odometer model `d` is affine,
   `d(x) = 3x + t`. At level 5, `t` is even in every model, `ord(d) = 8 = 2^(k-2)`, and `b` and `c`
   have order at most 4. The log2 order profiles of `(a, b, c, d)` at level 5 are `(5, 0, 1, 3)`,
   `(5, 1, 1, 3)`, `(5, 2, 1, 3)` (without `R` only) and `(5, 2, 2, 3)`. So level 5 is reached only
   by very unbalanced models, of degree 32. The monolithic models of
   `higman-order-2e-models-need-exponential-rank` are balanced. Their core-free degrees found there
   are 32 and 256 for `e = 3, 4`, and `a` acts semiregularly with `2^e`-cycles.

**What it kills and what it leaves.**
- Dead: every self-similar or other tree model of `H4(3)` or `H4(3)/<<R>>` in which a generator is
  level-transitive on `T_2`, whatever the section length. So the step "embed the `e = 3, 4` models in
  `W_5, W_8` and find a recursion with `a` as odometer" is blocked in its natural form. In those
  embeddings `a` has `2^(k-e)` cycles of length `2^e`. By item 1, for `e >= 6` no model of level `e`
  has a subgroup of index `2^e` that meets `<a>` trivially. So no other action of such a model
  makes `a` a single cycle either.
- Left: tree models in which `a` has infinite order but is not level-transitive. The first family is
  the `j`-odometer `a : x -> x + 2^j` on `Z_2`, trivial on the top `j` levels. For `j = 1`,
  `bfs2.py` finds 96, 752, 9152 and 229376 classes (with `R`, up to translation) at levels 2 to 5.
  At level 5 the maximal log2 orders of `(a, b, c, d)` are `(4, 3, 4, 4)`, so `ord(a) = 16` is
  reached. This family grows fast and does not die by level 5, unlike the odometer family. Level
  6 is out of reach of the pure-Python search. By the order ladder of
  `higman-order-2e-models-need-exponential-rank`, any tree model with `ord(a) = infinity` also has
  `ord(d)`, `ord(c)` and `ord(b)` infinite as well. So in such a model all four generators have
  orbits of unbounded length on the levels, but by item 2 none of them is level-transitive.
