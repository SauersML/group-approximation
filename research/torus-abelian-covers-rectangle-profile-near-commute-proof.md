---
rg: 2
id: torus-abelian-covers-rectangle-profile-near-commute-proof
kind: route
title: Discrete Stokes, a GL2(Z) change of generators along the shortest lattice direction with band surgery, and hierarchical charge clustering bound the rank distance of abelian torus covers by their rectangle profile
target: torus-abelian-covers-rectangle-profile-near-commute
requires: []
---

Notation as in the claim. `G = Z^2/Lambda`, `pi : Z^2 -> G`, `Omega = G x A`,
`b(x,a) = (x+e1, a+beta(x))`, `c(x,a) = (x+e2, a+gamma(x))`, and
`kappa(x) = beta(x) + gamma(x+e1) - gamma(x) - beta(x+e2)`. `S = supp kappa` and `n = |S|`.
For permutations `p, q` of a set of size `M`, `rank(p - q) = M - #cycles(p q^-1)`. This is at most the
number of points where `p` and `q` differ. All ranks are invariant under left and right
multiplication by permutations, and `rank(p^m - q^m) <= |m| rank(p - q)` (telescoping).

## 1. Holonomy

Read a word `W` in `b^(+-1), c^(+-1)` as a sequence of moves. From `(x,a)`, the letter `b` goes to
`(x+e1, a+beta(x))`, and `b^-1` undoes it. The same holds for `c` with `e2`. Fix one reading
convention (moves left to right) throughout. The composition-order convention only reverses paths
and changes no rank below.

The base point traces a lattice path `P_W(x)` in `Z^2`. The fibre coordinate adds the `A`-valued
1-cochain `omega` along it, with `omega = beta` on horizontal edges and `gamma` on vertical edges.
The coboundary of `omega` on the unit plaquette with lower-left corner `x` is exactly `kappa(x)`.

**Lemma 1 (Stokes).** Let the exponent sums of `W` in `b` and `c` both be 0. Then `W(x,a) = (x, a + m_W(x))`
with `m_W(x) = sum_(z in Z^2) w_W(z) kappa(pi(x~ + z))`. Here `x~` is any lift of `x`, and
`w_W(z)` is the winding number of the closed path `P_W(0)` around the plaquette `z + [0,1]^2`.

*Proof.* The path `P_W(x~)` is closed in `Z^2`, and `Z^2` (as a square complex) is simply
connected. So `P_W(x~)` is the boundary of the 2-chain `sum_z w_W(z) [x~ + z + [0,1]^2]`. Pull the
cochain `omega` back to `Z^2`. Since `A` is abelian, the sum of `omega` along a boundary is the sum of
`d omega` over the chain. Now `d omega` on the plaquette at `y` is `kappa(pi(y))`. QED.

**Lemma 2 (rank of a monodromy word).** For `W` as in Lemma 1, let `Z_W = #{x in G : m_W(x) != 0}`. Then
`(|A|/2) Z_W <= rank(W - I) <= |A| Z_W`.

*Proof.* `W` preserves every fibre `{x} x A` and acts on it by the translation `a -> a + m_W(x)`.
A translation by `m` has `|A|/ord(m)` cycles. So the fibre contributes `|A|(1 - 1/ord(m))`, which is 0
if `m = 0` and lies in `[|A|/2, |A|]` otherwise. QED.

**Lemma 3 (support).** Let `W` be as in Lemma 1 with word length `P`. Then
`Z_W <= n |supp w_W| <= n P^2/16`.

*Proof.* `m_W(x) != 0` forces `pi(x~ + z)` into `S` for some `z` in `supp w_W`. This gives at most
`n |supp w_W|` points `x`. Plaquettes with nonzero winding lie in the bounding box of `P_W(0)`. That
box has width `w` and height `h` with `2(w+h) <= P`, so its area is at most `P^2/16`. QED.

**Lemma 4 (rectangles).** For `s,t >= 1`, the word `[b^s,c^t]` (moves: `s` times `b`, `t` times `c`,
`s` times `b^-1`, `t` times `c^-1`) has `m(x) = sum_(0<=i<s, 0<=j<t) kappa(x + (i,j))`. Its path is
the boundary of the `s x t` box at `x`, with winding 1 on the box plaquettes and 0 elsewhere.

In particular, `rank([b,c] - I) >= |A| n/2`. Since `rho >= rank([b,c]-I)/2`, this gives
**`|A| n <= 4 rho`** (charge count).

## 2. Moves and transport

**Lemma 5 (moves).**
- Replace `beta(x_0)` by `beta(x_0) + delta`. This adds `delta` to `kappa(x_0)` and subtracts `delta`
  from `kappa(x_0 - e2)`.
- Replace `gamma(x_0)` by `gamma(x_0) + delta`. This adds `delta` to `kappa(x_0 - e1)` and subtracts
  `delta` from `kappa(x_0)`.
- Each move changes `b` (respectively `c`) only on the fibre over `x_0`. So it costs rank at most
  `|A|` in that generator, and exactly 1 when `A = Z/2`.

*Proof.* `beta(x_0)` occurs in `kappa(x)` only for `x = x_0` (term `+beta(x)`) and
`x = x_0 - e2` (term `-beta(x+e2)`). Similarly `gamma(x_0)` occurs only for `x = x_0 - e1` (term
`+gamma(x+e1)`) and `x = x_0` (term `-gamma(x)`). QED.

So a charge `delta` moves one step vertically at a cost of one `beta`-move, and one step horizontally
at a cost of one `gamma`-move. Along a lattice path, the intermediate contributions cancel in pairs.

**Lemma 6 (tree cancellation).** Let `Q` be a subset of `S` with `sum_Q kappa = 0`. Let `T` be a
spanning tree on `Q` whose edges are realized by lattice paths in `G` of total length `Sigma`. Then
changing `beta, gamma` at `<= Sigma` sites makes `kappa` vanish on `Q` and leaves it unchanged
elsewhere. The cost is `max(rank(b'-b), rank(c'-c)) <= |A| Sigma`.

*Proof.* Root `T`. Repeatedly take a leaf `p` with parent `p'` and transport the current charge at
`p` to `p'` along the edge path. Lemma 5 shows this changes `kappa` only at `p` (to 0) and at `p'`.
Each site of each edge path is used once. When only the root is left, its charge equals the total,
which is 0. QED.

## 3. Change of generators

Let `(v, u)` be a basis of `Z^2` with `det(v, u) = v1 u2 - v2 u1 = 1`. Put `B = b^(v1) c^(v2)` and
`C = b^(u1) c^(u2)`, as words. Then:
- `B(x,a) = (x + v, a + beta_B(x))` and `C(x,a) = (x + u, a + gamma_C(x))`, where `beta_B, gamma_C`
  are sums of `omega` along the staircase paths.
- The pair `(B,C)` has the same structure over `G` in the basis `(v,u)`, with charge
  `kappa'(x) = beta_B(x) + gamma_C(x+v) - gamma_C(x) - beta_B(x+u)`.
- `kappa'(x)` is the holonomy of the closed move sequence `B, C, B^-1, C^-1` from `x`, a word of
  length `2(|v|_1 + |u|_1)`.

**Lemma 7.**
- (a) `|supp kappa'| <= n (|v|_1 + |u|_1)^2/4`.
- (b) Lemma 5 holds for `(B, C)` with `e1, e2` replaced by `v, u`. In particular, changing `gamma_C(x_0)`
  by `delta` moves charge between `x_0 - v` and `x_0`.
- (c) `b^-1 B^(u2) C^(-v2)` and `c^-1 B^(-u1) C^(v1)` have zero exponent sums in `b` and in `c`.
  Their lengths are at most `1 + |u2||v|_1 + |v2||u|_1` and `1 + |u1||v|_1 + |v1||u|_1`.

*Proof.* (a) follows from Lemmas 1 and 3 with `P = 2(|v|_1+|u|_1)`. (b) is the proof of Lemma 5
verbatim. (c): the `b`-exponent of `B^(u2) C^(-v2)` is `v1 u2 - u1 v2 = 1` and its `c`-exponent is
`v2 u2 - u2 v2 = 0`. The `c` case is symmetric. QED.

**Back-substitution.** Suppose `C''` commutes with `B`. Then `b'' = B^(u2) C''^(-v2)` and
`c'' = B^(-u1) C''^(v1)` commute, being words in `B` and `C''`. Moreover:
- `rank(b'' - b) <= |v2| rank(C'' - C) + rank(b^-1 B^(u2) C^(-v2) - I)`;
- `rank(c'' - c) <= |v1| rank(C'' - C) + rank(c^-1 B^(-u1) C^(v1) - I)`.

The second terms are bounded by Lemmas 2, 3 and 7(c).

## 4. The thin case: band surgery along the shortest direction

**Proposition 8.** For every abelian torus cover,
`dist <= 6 |A| n lambda_1^4 <= 24 rho lambda_1^4`.

*Proof.*

*The new basis.* Let `w` be a nonzero vector of `Lambda` with `|w|_1 = lambda_1`. Write `w = k v` with `v`
primitive and `k >= 1`, and put `l = |v|_inf`. The vector `u` with `det(v,u) = 1` is unique modulo
`Z v`. We choose it with `|u|_inf <= l`:
- If `v = (+-1, 0)` or `(0, +-1)`, take `u` to be the other unit vector with the right sign.
- Otherwise `v1, v2 != 0`, say `|v1| >= |v2|` (the other case is symmetric). Shift `u` by multiples
  of `v` until `0 <= u1 < |v1|`. Then `|u2| = |1 + v2 u1|/|v1| <= (1 + |v2|(|v1|-1))/|v1| <= |v1| = l`.

So `|v|_1, |u|_1 <= 2l`. Also `l <= |v|_1 = lambda_1/k`, hence `k l <= lambda_1` and `l <= lambda_1`.
The order of `v` in `G` is exactly `k`, since a smaller multiple in `Lambda` would be shorter than `w`.

*Rows.* `G/<v> = Z^2/(Lambda + Z v)` is cyclic, generated by the image of `u`. Let its order be
`L = N/k`. The `<v>`-orbits (**rows**) `R_0, ..., R_(L-1)` have `k` points each, with
`R_j + u = R_(j+1)` and indices mod `L`.

Let `eps(x) = sum_(0<=i<k) beta_B(x + i v)`, the fibre translation by which `B^k` acts over `x`.
- `eps` is constant on rows: shifting `x` by `v` cyclically permutes the summands. Write `eps_j`.
- Sum `kappa'` over a row. The `gamma_C` terms telescope around the row, because `x + k v = x`. So
  (row identity) `sum_(x in R_j) kappa'(x) = eps_j - eps_(j+1)`.
- In particular `eps_(j+1) = eps_j` unless `R_j` carries charge of `kappa'`. Let `n' = |supp kappa'|`.
  By Lemma 7(a), `n' <= n (4l)^2/4 = 4 n l^2`, so at most `n'` rows carry charge.

*Band surgery.* If `eps` is constant, set `sigma(x) = x + u` for all `x`. Otherwise:
- Call `R_j` a **band end** if `eps_j != eps_(j+1)`. Every band end carries charge.
- The band ends cut the cycle `Z/L` of row indices into maximal cyclic intervals (**bands**)
  `j_0, j_0+1, ..., j_1` on which `eps` is constant, with `R_(j_1)` a band end. Let `L_b` be the
  band's length.
- Define `sigma(x) = x + u` if the row of `x` is not a band end, and `sigma(x) = x + (1 - L_b) u`
  if `x` lies in the band end `R_(j_1)`.

`sigma` is a translation of `G` on each row. It maps each band's rows cyclically onto themselves, so it
is a bijection of `G`. It satisfies `sigma(x + v) = sigma(x) + v`.

Define `C''(x,a) = (sigma(x), a + gamma''(x))`. The values `gamma''` are chosen below. Start with
`gamma'' = gamma_C`. `B` and `C''` commute iff the base maps commute (true) and the charge
`kappa''(x) = beta_B(x) + gamma''(x+v) - gamma''(x) - beta_B(sigma(x))` vanishes identically.

`kappa''(x)` involves only the row of `x` (through `gamma''`) and `beta_B` at `x` and `sigma(x)`.
So `kappa'' = kappa'` on every row that is not a band end.

The row identity now reads `sum_(x in R_j) kappa''(x) = eps_j - eps(sigma(R_j))`. This is 0 for every
`j`: for a row that is not a band end, `eps_(j+1) = eps_j`; for a band end, `sigma` maps it to the
first row of its own band, where `eps` takes the same value. So every row has total charge 0, and
`kappa''` is supported on the rows carrying charge of `kappa'`.

*Row cancellation.* On a row `R = {x, x+v, ..., x+(k-1)v}` with total charge 0, go around the row.
For `i = 0, ..., k-2`, add the current charge at `x + i v` to `gamma''(x + (i+1) v)`. By Lemma 7(b)
this moves that charge to `x + (i+1) v`. The last point is left with the total, which is 0. The
argument is the same with the non-translation `sigma` on a band end, since `gamma''` enters
`kappa''` only through the row. After this, `kappa'' = 0`, so `B` and `C''` commute.

*Cost.* `C''` differs from `C` only on fibres over rows that carry charge of `kappa'`:
at most `n'` rows, each of `k` points. So
`rank(C'' - C) <= |A| k n' <= 4 |A| n k l^2 <= 4 |A| n lambda_1^3`.

The words in Lemma 7(c) have length at most `1 + l*2l + l*2l = 1 + 4l^2`. By Lemmas 2 and 3,
`rank(b^-1 B^(u2) C^(-v2) - I) <= |A| n (1+4l^2)^2/16 <= (25/16) |A| n l^4` (using `l >= 1`), and the
same bound holds for the `c`-word. Back-substitution (Section 3) and `|v1|, |v2| <= l <= lambda_1` give
`max(rank(b''-b), rank(c''-c)) <= |A| n (4 lambda_1^4 + (25/16) lambda_1^4) <= 6 |A| n lambda_1^4`.
The last inequality of the Proposition is the charge count `|A| n <= 4 rho`. QED.

*Why this closes the diagonal gap.* The recorded obstruction was a cone point whose short saddle
connections are all diagonal. Cutting along such a connection changes both `b` and `c` by its
combinatorial length in the other generator. Here the short direction `v` becomes the generator `B`,
and the cut runs along rows of `B`. It is paid for in `C''`, then converted back at the cost of a
factor `|v|_inf <= lambda_1` and the Stokes error of Lemma 7(c). The profile enters only through
`|A| n <= 4 rho` and, in Section 5, through `lambda_1`.

## 5. Theorem A (dipoles)

Let `kappa = a delta_(x_0) - a delta_(x_0+g)` with `a != 0`. Write `|g|_1` for the least `l^1` norm of
a lift of `g`, and put `m_0 = min(|g|_1, lambda_1)` and `r = ceil(m_0/2)`, so that `2r - 1 <= m_0`.

*Lower bound.* Consider the `r x r` box `D = [0,r)^2`.
- Two points of `D` differ by a vector of `l^1` norm `<= 2r - 2 < lambda_1`. So `D` maps injectively
  to `G`.
- A translate `pi(y + D)` cannot contain both `x_0` and `x_0 + g`. Otherwise `g` would have a lift of
  `l^1` norm `<= 2r - 2 < |g|_1`.
- Hence exactly `2 r^2` points `y` in `G` have a translate `pi(y + D)` containing exactly one of the two
  charges, each once.
- By Lemma 4 each such point has `m(y) = +-a != 0`. By Lemma 2,
  `rank([b^r, c^r] - I) >= |A| r^2`, so `rho >= |A| r^2/(2r) = |A| ceil(m_0/2)/2`.

*Path cut.* Suppose `|g|_1 <= lambda_1`. Transport the charge `a` from `x_0` to `x_0 + g` along a monotone
lattice path of length `|g|_1` (Lemma 6 with a single edge). This gives
`dist <= |A| |g|_1 = |A| m_0 <= 4 rho`.

*Thin cut.* Suppose `lambda_1 < |g|_1`. Then `m_0 = lambda_1` and `n = 2`, and Proposition 8 gives
`dist <= 12 |A| lambda_1^4`. The lower bound gives `lambda_1 <= 4 rho/|A|`. So
`dist <= 12 * 256 rho^4/|A|^3 <= 3072 rho^4`.

*Calibration.* The slit origami of `slit-origami-z2-pair-has-rank-distance-half-l` is the `Z/2` dipole
with `g = (L, 0)` on a torus with `lambda_1 >= L`. There `rho >= ceil(L/2)`, and the path cut gives
distance `<= L` (each `Z/2` move costs 1). This is consistent with the exact value `floor(L/2)`.
The pairs of `z2-commuting-pairs-are-not-bounded-rank-stable`, which have bounded `[b,c]` rank and
unbounded distance, have `rho` growing with `m_0`, as the theorem requires.

## 6. Theorem B (all abelian torus covers)

Assume `kappa != 0`, so `|A| >= 2`, `n >= 2` and `n <= 4 rho/|A| <= 2 rho`. Let `d_inf` be the torus
`l^inf` distance on `G` (minimum over lifts). Put `r_0 = floor(8 rho) + 1` and `r_j = r_0 (2n+2)^j`.

**Case 1: `lambda_1 <= 4 n r_(n-1)`.** Proposition 8 gives `dist <= 24 rho (4 n r_(n-1))^4`.

**Case 2: `lambda_1 > 4 n r_(n-1)`.**

*Stable level.* For a scale `r`, let `P(r)` be the partition of `S` into the connected components of
the graph that joins `p` and `q` when `d_inf(p,q) <= r`.
- The partitions `P(r_0), ..., P(r_n)` get coarser, with block counts decreasing from at most `n`
  to at least 1.
- So among the `n` steps `j -> j+1`, at most `n - 1` are strict. Hence some `j <= n-1` has
  `P(r_j) = P(r_(j+1))`: same count, and coarser.

*Every cluster is neutral.* Let `Q` be a block of `P(r_j)`. Suppose `q = sum_Q kappa != 0`.
- Lifting a spanning tree of `Q`, whose edges have `d_inf <= r_j`, gives a lift `Q~` of `l^inf`
  diameter `<= (n-1) r_j`.
- Let `R = 2 n r_j`. Since `lambda_1 > 4 n r_(n-1) >= 2R`, every `R x R` box maps injectively to `G`.
- There are at least `(R - (n-1) r_j)^2 = (n+1)^2 r_j^2` points `y` with `Q~` inside `y + [0,R)^2`, and
  they are distinct in `G`.
- For each such `y`, a charge `p` in `pi(y + [0,R)^2)` has a lift within `l^inf` distance
  `R - 1 < r_(j+1)` of `Q~`. So `p` lies in the `P(r_(j+1))`-block of `Q`, which is `Q`.
- By injectivity each point of `Q` is counted once. So Lemma 4 gives `m(y) = q != 0`.
- By Lemma 2, `rank([b^R, c^R] - I) >= (|A|/2)(n+1)^2 r_j^2`. The profile bounds the same rank by
  `2 R rho = 4 n r_j rho`.
- So `r_j <= 8 n rho/(|A| (n+1)^2) <= rho < r_0`, a contradiction.

*Cancellation.* Each block `Q` is neutral. Apply Lemma 6 to a spanning tree of `Q` whose edges have
`d_inf <= r_j`, realized by lattice paths of length `<= 2 r_j`. Over all blocks there are at most
`n - 1` edges, so `dist <= 2 |A| n r_j <= 2 |A| n r_(n-1)`.

**Bound.** Use `|A| n <= 4 rho`, `n <= 4 rho` and `r_0 <= 8 rho + 1`:
- `4 n r_(n-1) <= Lambda_0 := 16 rho r_0 (8 rho + 2)^(4 rho)`;
- `dist <= max(24 rho Lambda_0^4, 8 rho r_0 (8 rho + 2)^(4 rho)) = exp(O(rho log rho))`.

This is the bound stated in the claim. QED.

## 7. What the computation adds, and what is left

**Computation** (`experiments/rectangle-profile-dipoles-2026-09-17/`, `summary.txt`).
- `dc.c` computes `rho` exactly for `Z/2` dipoles: every HNF lattice `<(N1,0),(C,N2)>` with
  `N <= 40` and every `g`, 35205 cases. It uses `s <= 2 ord(e1)` and `t <= 2 ord(e2)`. Over `Z/2`,
  the box sum is periodic in `s` with period `2 ord(e1)` (and in `t` likewise), so larger `s, t` only
  lower the ratio.
- `lam.py` checks `m_0/rho` against Theorem A. It lies in `[0.525, 1.714]` (the theorem forces
  `<= 2`).
- `anneal.c` and `sweep.sh`, for `N <= 26`, search over boundary loops of arbitrary regions `U` for the
  largest `rank(W-I)/(|W|/2)`. The search never exceeds `1.25 rho`. So for these pairs, a bounded rectangle profile is
  equivalent, up to a factor `1.25`, to a bounded profile over all such loops.
- `surgery.py`, for `N <= 22` (5749 cases), builds the path-cut and thin-cut commuting pairs as
  explicit permutations and asserts commutation, the row identity and band closure. In every case
  the better one has `rank(b''-b) + rank(c''-c) <= 2.5 rho`.
- So within this range the dipole distance is linear in `rho`. The `rho^4` of Theorem A comes from
  worst-case bookkeeping (Lemma 3 applied to long staircase words), not from the pairs.

**What is left for permutation pairs.** A general permutation pair is a cover of the one-square
torus with fibre `Omega` and `Sym(Omega)`-valued cochain.
- Lemmas 1, 5 and 6 and the clustering of Section 6 should go through, with `kappa(x)` replaced by
  the local monodromy (up to conjugacy) and costs measured by supports. This is not checked here.
- The thin surgery of Section 4 fails. The row monodromies `eps_j` become permutations, adjacent
  rows give conjugate rather than equal ones, and regluing a band needs a fibre bijection conjugating
  `eps_(j_1)` to `eps_(j_0)`. Its rank cost is not controlled by `n` here, because the fibre is not
  bounded by `rho`.
- The next step is therefore to bound, in terms of `rho`, the rank of a conjugator between the
  `B^k`-monodromies of the two ends of a band.
