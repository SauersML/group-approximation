---
rg: 2
id: higman-h4-3-two-orbit-odometer-models-stop-at-level-seven-proof
kind: route
title: Proof by exact F_2-linear lifting in W_k with orderly generation up to the full centralizer of the J-odometer, an exhaustive C search that dies at level 8 for J = 1, cross-checks against the J = 0 counts and bfs2.py, and a GAP check of a level-7 model
target: higman-h4-3-two-orbit-odometer-models-stop-at-level-seven
requires:
  - higman-h4-3-has-no-odometer-models-beyond-level-five
artifacts:
  - experiments/higman-jodometer-lifting-2026-09-19/jlift.c
  - experiments/higman-jodometer-lifting-2026-09-19/j1-output.txt
  - experiments/higman-jodometer-lifting-2026-09-19/xcheck-output.txt
  - experiments/higman-jodometer-lifting-2026-09-19/model-j1-level7.g
  - experiments/higman-jodometer-lifting-2026-09-19/verify.g
  - experiments/higman-jodometer-lifting-2026-09-19/verify-j1-level7-output.txt
---

The notation is that of the target. Item 4 and Lemmas 1 and 2 are proved in full here. Items 1 and
3 rest on one exhaustive computation, so their tier is **computed**. Item 2 is a certificate that
GAP checks independently. The route uses the lifting lemma (Lemma 2) of
`higman-h4-3-has-no-odometer-models-beyond-level-five-proof` and its `J = 0` counts as a
cross-check.

**Conventions.** Permutations act on the right. `W_k` acts on `Z/2^k`, and `g` is a tree
automorphism exactly when `x = y mod 2^m` implies `xg = yg mod 2^m`. The level-`k` element `a_k`
is `x -> x + 2^J`.

**Lemma 1 (the centralizer).** For `k >= J`, the centralizer `C_k` of `a_k` in `W_k` is the set of
maps `x -> x + r(x mod 2^J)`, where `r : Z/2^J -> Z/2^k` and `i -> i + r(i) mod 2^J` lies in `W_J`.
Its order is `|W_J| 2^((k-J) 2^J)`, which is `2^(2k-1)` for `J = 1`. Restriction `C_(k+1) -> C_k`
is onto, and its kernel is the `2^(2^J)` maps `r -> r + 2^k e` with `e in {0,1}^(2^J)`.

*Proof.* The `a_k`-orbits are the residue classes mod `2^J`, and `a_k` is a `2^(k-J)`-cycle on each
of them. If `g` commutes with `a_k`, then `g` maps the class of `i` to the class of some `iσ`, with
`(i + n 2^J)g = ig + n 2^J`. So `g` has the stated form with `r(i) = ig - i`. Being a tree
automorphism asks for congruences mod `2^m`. For `m <= J` these say `σ in W_J`. For `m > J` they
hold automatically, because two points congruent mod `2^m` lie in one class, where `g` is a
translation. Conversely every such map commutes with `a_k`. The condition on `r` only sees
`r mod 2^J`, so every `r` mod `2^k` lifts in exactly `2^(2^J)` ways. ∎

**Lemma 2 (orderly generation is exact).** Encode a level-`k` tuple `(b, c, d)` by blocks for
levels `1, ..., k`. The level-`m` block lists the bits `(y p >> (m-1)) & 1` for `y < 2^(m-1)`, for
`p = b, c, d` in turn. A tree automorphism is determined by these bits, and its level-`(m-1)`
restriction is determined by the blocks below `m`. Order tuples lexicographically by these blocks,
and call a model *canonical* when it is minimal in its `C_k`-orbit. Then:
1. The restriction of a canonical level-`(k+1)` model is canonical.
2. A lift `L` of a canonical `T` is canonical if and only if `L^g >= L` for every `g in C_(k+1)`
   that restricts into `Stab_(C_k)(T)`.

*Proof.* Conjugation by `g in C_(k+1)` fixes `a_(k+1)` and preserves the relators. It commutes
with restriction, because `g` restricts to an element of `C_k`. For (1), if `T^h < T` with
`h in C_k`, lift `h` to `g` (Lemma 1). Then `L^g` restricts to `T^h`, and the lex order compares
levels `<= k` first, so `L^g < L`. For (2), if `g` restricts outside the stabilizer, then
`T^(g|k) > T`, so `L^g > L`. Otherwise `L^g` and `L` agree below level `k+1`, and only the top
block decides. ∎

`jlift.c` does exactly this. `base` lists all tuples at level `J` (where `a` is trivial) that are
minimal under `W_J = C_J`. For each canonical `T`, `dfs` builds the lifting system of Lemma 2 of
the predecessor route (inhomogeneous, in the `3 * 2^k` switch bits of `b, c, d`, with `a`'s lift
fixed) and row-reduces it over `F_2`. It then enumerates the affine solution space by Gray code.
`try_lift` runs `cmp_conj` over the stabilizer list of `T` times the kernel of Lemma 1, rejects
`L` if some conjugate is smaller, and records the elements that fix the top block as
`Stab(L)`. By Lemma 2 each class is visited exactly once. Every level-`(k+1)` model restricts to a
level-`k` model, so if no canonical `T` at level `k` has a consistent system, there is no model at
any level above `k`.

**Computation (items 1 and 3).** `./jlift 1 9` (with `R`) finished in 198 s (`j1-output.txt`).
- The class counts at levels 1 to 8 are `8, 80, 332, 1908, 24336, 318432, 11776, 0`.
- At level 7 the line is `lifts tried 0` for level 8. Every one of the 11776 canonical level-7
  models has an inconsistent lifting system, so no level-8 model exists. By restriction, no
  model exists at any level `k >= 8`.
- The swap-pattern and order-profile lines give item 3.

**Cross-checks (`xcheck-output.txt`).**
1. `./jlift 0 7` gives `8, 16, 48, 192, 736` and then 0 at level 6. Here `C_k = <a>`, so these are
   exactly the `<a>`-classes of `bfs.py` in the predecessor.
2. `./jlift 0 6 noR` gives `8, 16, 72, 544, 9728` and then 0. This is the predecessor's result
   without `R`.
3. `./jlift 1 5 trans` restricts the symmetry to the translations `x -> x + r` and gives
   `8, 96, 752, 9152, 229376`. These are the counts of the independent Python `bfs2.py`.
4. Pattern `0000` at level 6 accounts for 271216 classes, and this can be predicted with no search:
   - If no generator moves level 1, a `1`-odometer model of level 6 is a pair `(M_0, M_1)` of
     `0`-odometer models of level 5, one on the even vertices and one on the odd ones. Any pair
     works.
   - `C_6` translates each half independently and swaps the halves.
   - So the classes are unordered pairs of the 736 translation classes, and there are
     `736 * 737 / 2 = 271216` of them. This is the count the program reports.
   - For the same reason pattern `0000` is absent at level 7, since there is no `0`-odometer
     model at level 6.

**Item 2.** `jlift 1 7 first` writes `model-j1-level7.g` (images on `1..128`, point `x+1` for
residue `x`). `verify.g` reads it in GAP, with no code shared with `jlift.c`
(`verify-j1-level7-output.txt`). It reports:
- all five relators are trivial;
- the orders are `[64, 4, 4, 16]`;
- the images are tree automorphisms of degree 128;
- the `a`-orbits are two 64-cycles;
- `|G| = 2^29`, and `G` is a transitive 2-group.

**Item 4.** From `a^d = a^3`, `d^-n a d^n = a^(3^n)`. In a 2-group, `ord(d) = 2^s`. If `s = 0`, then
`a = a^3`, so `ord(a) <= 2`. If `s >= 1`, then `ord(a)` divides `3^(2^s) - 1`, and this has 2-adic
valuation `s + 2` by lifting the exponent. So `ord(a) <= 2^(s+2) = 4 ord(d)`. ∎

**Remark (the wall).** A conceptual proof of either wall (level 6 for `J = 0`, level 8 for `J = 1`)
is still open.
- In both families the survivors at the top level are ladder-tight: `ord(d) = ord(a)/4`, which is
  8 at level 5 for `J = 0` and 16 at level 7 for `J = 1`.
- Every one of them has an inconsistent lifting system. This suggests, but does not prove, that
  the obstruction is that `ord(d)` cannot double along with `ord(a)`.
- The ladder alone is uniform in `k` and does not prove this.
- By the pattern-`0000` reduction above, a proof of the `J = 0` wall at level 6 gives the
  `φ = 0` part of the `J = 1` family from level 7 on. The models that move level 1 would still
  need a separate argument.
