---
rg: 2
id: excised-square-kills-cone-local-slit-pair-repair-proof
kind: route
target: excised-square-kills-cone-local-slit-pair-repair
requires:
  - near-exact-tuples-saturate-linear-conversion-defect
  - two-torus-cross-slit-forces-sqrt-d-loss-in-thin-closing
title: Excising a square keeps distance 1 but leaves a genus-2 component of area n^2 - 1, and surviving n-cycles force any commuting pair on it to have area dividing n^2
---

Notation as in the claim. Points of `(Z/n)^2` are `(i, j)`, with `b0(i, j) = (i+1, j)` and `c0(i, j) = (i, j+1)`.
Write `l = (-1, 0)`, `r = (1, 0)`, `u = (0, -1)`, `t = (0, 1)` for the neighbours of `x = (0, 0)`. For permutations
`f, g`, `rank(P_f - P_g) = rank(P_(g^-1 f) - I)`, and for a permutation `w`,
`|supp w|/2 <= rank(P_w - I) = d - #cycles(w) <= |supp w|`.

## 1. Distance and profile

`b = b0 tau`, where `tau` is the transposition of `l` and `x`: indeed `b(l) = b0(x)` and `b(x) = x = b0(l)`. So
`rank(b - b0) = 1`, and likewise `rank(c - c0) = 1`. Since `(b0, c0)` commutes, `dist(b, c) <= 1`. By Lemma B of
`near-exact-tuples-saturate-linear-conversion-defect-proof`, `rho(b, c) <= 2`. The point `x` is fixed by `b` and `c`,
so the pair is the direct sum of its restriction to `Omega' = (Z/n)^2 \ {x}` and the trivial pair on `{x}`. Ranks add
over direct sums and the trivial block commutes, so `rho` of the restriction `(b', c')` to `Omega'` is also at most 2.

## 2. The surface

Corners of a square `y` are `BL(y), BR(y), TR(y), TL(y)`. Vertices are the classes under
`BR(y) ~ BL(by)`, `TR(y) ~ TL(by)`, `TL(y) ~ BL(cy)` and `TR(y) ~ BR(cy)`. A vertex with `4k` corners has angle
`2 pi k` and excess `k - 1`. The total excess is `rank([b, c] - I)`.

*The flat point.* `b(x) = c(x) = x` identifies the four corners of `x` with each other: a regular vertex. So `{x}` is
a `1 x 1` flat torus.

*Other vertices.* The relations that differ from those of the torus are the four that involve `b(l)` or `c(u)`. Take
`n >= 3`, so that the nine squares `(i, j)` with `|i|, |j| <= 1` are distinct. Every vertex of the torus away from the
four corners of `x` then keeps its four corners, so it is regular. At the four corners of `x`, the unchanged relations
give four groups of three corners:
- `{BR(l), TR(l_d), TL(u)}` at `BL(x)`, with `l_d = (-1, -1)`;
- `{BL(r), TL(r_d), TR(u)}` at `BR(x)`, with `r_d = (1, -1)`;
- `{TL(r), BL(r_u), BR(t)}` at `TR(x)`, with `r_u = (1, 1)`;
- `{TR(l), BR(l_u), BL(t)}` at `TL(x)`, with `l_u = (-1, 1)`.

For example, `c(l_d) = l` gives `TR(l_d) ~ BR(l)`, and `b(l_d) = u` gives `TR(l_d) ~ TL(u)`. Neither uses a changed
value, because `l_d` is neither `l` nor `u`. The changed relations are:
- `BR(l) ~ BL(r)` and `TR(l) ~ TL(r)`, from `b(l) = r`;
- `TL(u) ~ BL(t)` and `TR(u) ~ BR(t)`, from `c(u) = t`.

They join the groups in the cycle `BL(x) - BR(x) - TR(x) - TL(x) - BL(x)`. So the twelve corners form one vertex of
angle `6 pi`.

*Totals.* `S'` has `F = n^2 - 1` squares and `V = n^2 - 3` vertices, so its excess is `F - V = 2`.

*Connected.* The rows `j != 0` are `b`-cycles of length `n`, the columns `i != 0` are `c`-cycles of length `n`, and
every point of `Omega'` lies on one of them. Row `j` meets column `i` at `(i, j)`, which is in `Omega'` for
`i, j != 0`. So `S'` is connected. Its Euler characteristic is `V - 2F + F = -2`, so its genus is 2.

`certify.py` (part B) checks the vertex structure for `n = 5, ..., 40`, as a cross-check.

## 3. Commuting pairs on the cone component

Let `(b'', c'')` be a commuting pair of permutations of `Omega'`, with `delta_b = rank(b'' - b')` and
`delta_c = rank(c'' - c')`. A *changed site* of `b` is a point `y` with `b''(y) != b'(y)`. There are at most
`2 delta_b` of them, and at most `2 delta_c` for `c`.

*Intact rows and columns.* Call a row `j != 0` intact when it contains no changed site of `b`. Then `b'' = b'` on it,
so it is a `b''`-cycle of length `n`. At most `2 delta_b` of the `n - 1` rows `j != 0` fail to be intact. In the same
way, a column `i != 0` without changed sites of `c` is a `c''`-cycle of length `n`, and at most `2 delta_c` columns
fail.

Suppose `2 delta_b < n - 1` and `2 delta_c < n - 1`, so that there are intact rows and intact columns.

*The component K.* An intact row `j` and an intact column `i` share the point `(i, j)`. So all intact rows and
columns lie in one orbit `K` of `<b'', c''>`. Since `b''` and `c''` commute, `Z^2` acts on `K` transitively and
abelianly, so all points of `K` have the same stabilizer `Lambda`. A `b''`-cycle in `K` has length
`min{k > 0 : (k, 0) in Lambda}`. An intact row has length `n`, so `(n, 0) in Lambda`. An intact column gives
`(0, n) in Lambda`. Hence `n Z^2 <= Lambda`, and `|K| = [Z^2 : Lambda]` divides `n^2`.

*The contradiction.* `|K| <= |Omega'| = n^2 - 1 < n^2`, so `|K| <= n^2/p`, where `p` is the least prime factor of `n`.
On the other hand `K` contains at least `n - 1 - 2 delta_b` rows of `n` points each. So
`n (n - 1 - 2 delta_b) <= n^2/p`, which gives `delta_b >= (n - 1 - n/p)/2`.

If there are no intact rows or no intact columns, then `max(delta_b, delta_c) >= (n - 1)/2`, which is larger. In all
cases `max(delta_b, delta_c) >= (n - 1 - n/p)/2 >= (n - 2)/4`. For prime `n` this is `(n - 2)/2`. QED (3).

**No padding.** The bound concerns commuting permutation pairs on the same point set `Omega'`. With one extra point
`x` and `beta = gamma = 1` there, the pair `(b0, c0)` is at distance 1 from `(b' ⊕ 1, c' ⊕ 1)`.

## 4. Slit-pair swaps and cone-local repairs

*Cost.* A swap exchanges the values `b(y1), b(y2)` across each pair of corresponding vertical edges, and does the
same for `c` across horizontal edges. So the new `b` is `b` times a product of `V` transpositions, and
`rank(b_new - b) <= V`. Likewise `rank(c_new - c) <= H`.

*Locality.* Edge paths are connected. Two paths that start at the cone point `A` lie in the component `S'`, so a swap
from `A` changes only values at points of `Omega'`, and keeps `b` and `c` on `{x}`.

*Parity.* The excess `rank([b, c] - I) = |Omega'| - #cycles([b, c])` has the parity of the permutation `[b, c]`,
which is even. So on `Omega'` the excess is even and nonnegative.

*Conclusion.* A swap from `A` that lowers the excess below 2 therefore makes it 0, that is, `[b_new, c_new] = I` on
`Omega'`. By Section 3, `max(V, H) >= (n - 1 - n/p)/2`, so the swap has at least that many edges.

For a chain of swaps, or any repair `(b'', c'')` that equals `(b, c)` on `{x}`, the final pair preserves `Omega'` and
commutes there. Its cost is at least the Section 3 bound, by the triangle inequality for rank. QED (4).

`certify.py` (part C) enumerates every pair of equal-direction sectors at `A` and every word of at most 10 moves, for
`4 <= n <= 7`. The shortest lowering swap has exactly `n - 1` edges and costs `(0, n - 1)`, so the linear bound is
attained up to the constant.

## 5. The Lipschitz bound used for the next step

For permutation pairs, `b'^s - b^s` has rank at most `s rank(b' - b)`, by telescoping. The same holds for inverses
and for `c`. A commutator `[b^s, c^t]` is a product of four factors, so

`rank([b'^s, c'^t] - [b^s, c^t]) <= 2 s rank(b' - b) + 2 t rank(c' - c)`.

Hence `rho(b', c') <= rho(b, c) + 2 max(rank(b' - b), rank(c' - c))`.

Suppose some move of cost at most `P(rho)` always lowers the excess, even using a padded donor torus (padding
leaves `rho` unchanged). The excess starts at most `2 rho`, and each move raises `rho` by at most `2 P`. So after at
most `2 rho` moves the pair commutes, at total cost at most the iterate `sum_i P(rho_i)`, where
`rho_(i+1) = rho_i + 2 P(rho_i)`. This is why the donor slit-pair lemma of the claim would settle the permutation
case.
