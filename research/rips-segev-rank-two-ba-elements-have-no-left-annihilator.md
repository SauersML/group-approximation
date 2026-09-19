---
rg: 2
id: rips-segev-rank-two-ba-elements-have-no-left-annihilator
kind: claim
title: In Steenbock's Rips--Segev group every element sum_j b^j v_j(a) whose coefficients span a k-space of dimension at most 2 has no left annihilator, for every b-degree and every field, so rank-two elements of <a><b> and <b><a> are two-sided non-zero-divisors; in general pure lines with nonzero port polynomials occupy at most dim span(v_j) - 1 rows
distinct_from:
  rips-segev-ab-layered-elements-have-no-left-annihilator: that is the other side (left annihilators of elements of <a><b>, all coefficient ranks) and the degree-one two-sided case.  This is left annihilators of elements of <b><a>, where the rank-one lemma fails, for coefficient rank at most 2 and every b-degree.
  rips-segev-steenbock-few-line-a-supports-are-regular: that needs a-span below 10^51; this has no bound on the a-supports.
  rips-segev-steenbock-eleven-point-a-supports-are-regular: that needs at most 11 distinct a-exponents; this has no bound on them.
  rips-segev-groups-satisfy-kaplansky-zero-divisor: that is the open question.  This settles <a>/<b>-layered elements of coefficient rank at most 2 on both sides; coefficient rank >= 3 on the <b><a> left side and mixed-layer elements stay open.
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: `rips-segev-rank-two-ba-no-left-annihilator-proof`.

**Setting.**  As in `rips-segev-ab-layered-elements-have-no-left-annihilator`.
- `G` is the Rips--Segev group built from Steenbock's graph `Gamma`, with core `K = F/<<R>>`, `F = <a> * <b>`,
  `Gr'_*(1/8)`, `girth(Phi) >= 42`, and row sets `D_r = {0} ∪ {10^e : 5r-4 <= e <= 5r}`.
- `k` is any field.  Elements of `k[t^{±1}]` are evaluated at `a`.

**Theorem R (rank two).**  Let `d >= 0` and `v_0, ..., v_d in k[t^{±1}]`, not all zero, and put
`beta = sum_j b^j v_j(a)`.  If `dim_k span(v_0, ..., v_d) <= 2`, then `alpha beta = 0` forces `alpha = 0`.
- Equivalently: `beta = q_1(b) w_1(a) + q_2(b) w_2(a)`, with `q_i in k[b^{±1}]` and `w_i in k[a^{±1}]`
  arbitrary, has no left annihilator.
- The a-supports and the b-degree are unbounded.  `d = 1` is Corollary C of the node above.

**Corollary (two-sided).**  Every element of coefficient rank `<= 2` supported in `<a><b>` or in `<b><a>` is a
non-zero-divisor on both sides of `k[G]`.
- `<b><a>`: left by Theorem R, right by Theorem A of the node above and the involution.
- `<a><b>`: left by Theorem A, right by Theorem R and the involution.

**Row bound (any coefficient rank).**  Put `n = dim_k span(v_j)` and `alpha beta = 0`.  Call a coset `T` *pure
of row `r`* if all points of `T` that meet the segments `y, y b, ..., y b^d` (`y in supp alpha`) lie in one
translate of `D_r`.  Let `g_x = sum_j alpha(x b^{-j}) v_j` be the *port polynomial* at `x in T`.  Then pure
cosets in pairwise distinct rows with some `g_x != 0` number at most `n - 1`.
- *Determinant step.*  The vectors of `n` such cosets lie in the rank-`(n-1)` syzygy module of a basis of
  `span(v_j)`, so their determinant vanishes.  Distinct rows make `(x_1, ..., x_n) -> sum x_k` injective on
  the product of their supports, so the determinant of the scalar coefficient vectors vanishes for every choice
  of points.
- *Rado.*  So the coefficient spaces `U_k` have no independent transversal, and some `J` has
  `dim sum_J U_k < |J|`.  Induction on the dimension closes it.  For `n = 2` this is the rank-one lemma.

**Mechanism of Theorem R.**
- *Segments and the port graph.*  Each `y in supp alpha` gives the segment `y, ..., y b^d`.  Its `b`-edges form
  a port graph `S` of minimum degree 2: an interior level gives two edges, and a coset with only levels `0` and
  `d` has both, since `p_0 v_0 + p_d v_d = 0` in `k[t^{±1}]`.
- *Flow cycle, purity.*  The leaf-block flow cycle and the copy splitting apply unchanged.  A good untouched
  cycle line is pure.  Its `I` positions carry only level `d`, its `O` positions only level `0`, and its middles
  `0, C` carry any level.
- *Two kinds.*  A *middle line* has all its segment points at `0` and `C`.  By Fact M two middle lines are never
  consecutive.  A *bad line* has a point at `I_1, I_2, O_1` or `O_2`, where the port polynomial is a nonzero
  multiple of `v_d` or `v_0`.
- *One bad line per copy.*  For `n <= 2` the row bound leaves at most one bad row.  Lines of one copy have
  distinct rows.
- *Windows of 6.*  Among 6 consecutive untouched cycle lines at most 2 are not middle lines (the bridge end and
  one bad line), so visits have 3 to 8 edges.  The 13-edge Greendlinger arc closes it as before.

**Calibration.**  In `H_{m,n} = <a, b | (a^m b)^n>` (`n >= 3`), `alpha = sum_j (b a^m)^j` kills
`1 - b a^m` on the left, with coefficient rank 2.  All lines of its relator loop carry the position set
`{0, m}`, so the determinant step has no distinct rows and is silent.  This is the only step that fails there.

**Open.**
- Coefficient rank `n >= 3` on the `<b><a>` left side.  Everything above holds except the count.  A copy can
  have up to `n - 1` bad lines, all images of the same `<= n - 1` lines of `Gamma`.  The 13-edge arc allows
  visits of at most 8 edges, so a 6-window must not hold two bad lines and the bridge end.
  - For `n = 3` only the copy containing the bridge end, untouched, can fail the 6-window.  Its visits have at
    most 10 edges.  Every other copy's visits have at most 8.
- General (mixed-layer) supports.
