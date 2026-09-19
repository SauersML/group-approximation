---
rg: 2
id: higman-h4-3-has-no-odometer-models-beyond-level-five-proof
kind: route
title: Proof by reduction to the odometer, exact level-by-level F_2-linear lifting in W_k = F_2^(2^(k-1)) x| W_(k-1) up to conjugation by <a>, and an exhaustive search that dies at level 6, cross-checked in GAP
target: higman-h4-3-has-no-odometer-models-beyond-level-five
requires:
  - higman-order-2e-models-need-exponential-rank
artifacts:
  - experiments/higman-odometer-lifting-2026-09-18/lift.py
  - experiments/higman-odometer-lifting-2026-09-18/bfs.py
  - experiments/higman-odometer-lifting-2026-09-18/run-withR-output.txt
  - experiments/higman-odometer-lifting-2026-09-18/run-noR-output.txt
  - experiments/higman-odometer-lifting-2026-09-18/xcheck.g
  - experiments/higman-odometer-lifting-2026-09-18/xcheck-output.txt
---

The notation is that of the target. Items 2 and the affine form in item 4 are proved in full here.
Item 1 is proved from the reductions below plus one exhaustive computation, so its tier is
**computed**. Items 3 and 4 are computed. The route requires
`higman-order-2e-models-need-exponential-rank` only for its order ladder and for the monolithic
models it is compared with.

**Conventions.** Permutations act on the right: `gh` means first `g`, then `h`. A vertex at level
`r` of the binary tree is a residue `x mod 2^r`, and the children of `x` at level `r + 1` are `x`
and `x + 2^r`. `W_k` is the group of permutations of `Z/2^k` that preserve every congruence
mod `2^r`, `r <= k`, which is the automorphism group of the tree truncated at level `k`.
`a_k : x -> x + 1` is the odometer.

**Lemma 1 (reduction to the odometer).** Let `phi : H4(3) -> S_(2^k)` have 2-group image `P`,
and suppose `phi(x)` is a `2^k`-cycle for a generator `x`. Then there is a relabelling of the
points after which `P <= W_k` and `phi(a)`, `phi(b)`, `phi(c)` or `phi(d)` (whichever is `x`) is
`a_k`. Moreover the map `a -> b -> c -> d -> a` extends to an automorphism of `H4(3)`, because it
permutes the four defining relators cyclically. So we may take `x = a`.

*Proof.* `P` lies in a Sylow 2-subgroup of `S_(2^k)`, and all of these are conjugate to `W_k`. A
`2^k`-cycle `g` in `W_k` acts transitively on each level, and any two such elements are conjugate
in `W_k`. The proof is by induction on `k`. Write `g = (g_0, g_1) s`, where `s` swaps the two
subtrees of the root, so that `s (h_0, h_1) = (h_1, h_0) s`. Conjugating by `(1, g_0^-1)` turns `g`
into `(1, g_0 g_1) s`. Its square is `(g_0 g_1, g_0 g_1)`, so `g_0 g_1` is a `2^(k-1)`-cycle of the
subtree. By induction `u^-1 g_0 g_1 u = a_(k-1)` for some `u` in `W_(k-1)`. Since `(u, u)` commutes
with `s`, conjugating by `(u, u)` gives `(1, a_(k-1)) s`. This is `a_k`: it maps `2y` to `2y + 1` with
trivial section and `2y + 1` to `2(y + 1)` with section `a_(k-1)`. ∎

**Equivalent form.** If `Q` is a finite 2-group quotient with `Q = <x> H` and `<x> ∩ H = 1`, then `Q` acts on
`Q/H`, `<x>` acts regularly there, and so `x` is a cycle of length `ord(x)`. Conversely the
stabilizer of a point in an action as in Lemma 1 is such an `H`, and `ord(x) = 2^k`.

**Lemma 2 (exact lifting).** Every element of `W_k` restricts to `W_(k-1)`, and the elements over
`g in W_(k-1)` are the pairs `(g, v)`, `v in F_2^(2^(k-1))`: the point `x + e 2^(k-1)` goes to
`g(x) + (e + v(x)) 2^(k-1)`. The product is `(g, v)(h, w) = (gh, v + w∘g)`. Fix a solution
`(a_(k-1), b, c, d)` at level `k - 1` and the lift of `a_(k-1)` to `a_k`, which has switch vector
`e_(2^(k-1) - 1)`. A relator word evaluated on lifts is trivial if and only if, for each `x`, the
switch bits collected along the path of `x` sum to 0. These are inhomogeneous `F_2`-linear
equations in the `3 * 2^(k-1)` unknown switch bits of `b, c, d`. `lift.system` writes exactly these
equations: for an inverse letter it reads the switch at the preimage, and it reads the switch of
`a` from the fixed vector. `lift.solve` does Gauss–Jordan elimination, and `bfs.lifts` lists the
whole affine solution space. Every level-`k` odometer model restricts to a level-`(k - 1)`
odometer model, so the lifts of all level-`(k - 1)` models are all level-`k` models. Every
solution is re-checked by evaluating the relators (`lift.check`, asserted in `bfs.py`). ∎

**Lemma 3 (symmetry).** The centralizer of `a_k` in `S_(2^k)` is `<a_k>`, which lies in `W_k`.
If `t' = t^(a_(k-1)^j)` at level `k - 1`, then the lifts of `t'` are the conjugates of the lifts
of `t` by `a_k^j`. This holds because `a_k^j` restricts to `a_(k-1)^j`, preserves relators and
fixes `a_k`. So `bfs.py` keeps one representative per `<a>`-class (`canon`, the minimum over the
`2^k` conjugates) and loses nothing. ∎

**Computation.** `bfs.py 7` and `bfs.py 7 noR` run the search from level 0. The class counts are
`8, 16, 48, 192, 736` with `R` and `8, 16, 72, 544, 9728` without `R` at levels 1 to 5. Every one
of the 736 and 9728 level-5 classes has an empty affine lift space ("lift-count histogram of
parents {0: 736}" and "{0: 9728}"). So level 6 is empty, and by restriction so is every level
`k >= 6`. Together with Lemma 1 this proves item 1. The version without `R` already implies the
version with `R`, and it is the one that transfers to `b, c, d` through the automorphism, since
that automorphism sends `[a,c]^2` to `[b,d]^2`.

**Independent check.** `xcheck.g` counts all homomorphisms `H4(3) -> W_k` with `a = a_k` directly in GAP,
without the linear algebra. It builds `W_k` from its level generators. It then runs `d` over the
coset `C_W(a) g` of solutions of `a^d = a^3`, `c` over `C_W(d) h`, and `b` over `C_W(c) y`, and
filters by `b^a = b^3` and, optionally, `[a,c]^2 = 1`. Its counts `8, 32, 192, 1536` (with `R`,
`k <= 4`) and `8, 32, 288, 4352` (without `R`) agree with `rawcount.py`
(`rawcount-withR-output.txt`, `rawcount-noR-output.txt`), which also gives 11776 at `k = 5` with `R`.

**Item 2.** An action of `H4(3)` on `T_2` in which a generator `x` is level-transitive induces on
level 6 a homomorphism to `W_6` in which `x` is a 64-cycle. This contradicts item 1. ∎

**Item 4, affine form.** `d^-1 a d = a^3` with right actions reads `(y + 1) d = y d + 3` for all
`y`, so `d(y) = 3y + t` with `t = d(0)`. Every such map preserves each congruence mod `2^r`, so it
lies in `W_k`. For `k >= 3`, `d^N(y) = 3^N y + t (3^N - 1)/2`. The multiplicative order of 3
mod `2^k` is `2^(k-2)`. By the valuation lemma of `higman-order-2e-models-need-exponential-rank`,
`v_2((3^(2^(k-2)) - 1)/2) = k - 1`. So `ord(d) = 2^(k-2)` if `t` is even and `2^(k-1)` if `t` is
odd. `analyze5.py` finds `t` even and `ord(d) = 8` in all 736 level-5 classes with `R`, and
`ord(b), ord(c) <= 4`. ∎

**Remark (why no hand proof yet).** The order ladder alone is consistent at every level. It asks
only `2^(k-2) | ord(d)`, `2^(k-4) | ord(c)` and `2^(k-6) | ord(b)`, and the affine `d` meets the first
condition. The obstruction at level 6 comes from how `c` must conjugate the affine `d` to `d^3`
inside `W_k` while `b` conjugates `c` to `c^3` and is itself cubed by `a`. At level 5 this already
forces `ord(b), ord(c) <= 4`, which is the edge of the ladder (`2^(5-4) = 2 | ord(c)`). A
conceptual proof that the normalizer chain `d -> c -> b -> a` in `W_k` breaks at `k = 6` is open.
