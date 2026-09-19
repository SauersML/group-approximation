---
rg: 2
id: seam-surface-forces-neutral-relocation-in-self-bound-lemma-proof
kind: route
target: seam-surface-forces-neutral-relocation-in-self-bound-lemma
title: Proof that the (1,2,3) seam surfaces have no short lowering slit pair or handle, that one relocation repairs them, and that tall one-cylinder surfaces are within rank 4 rho of a torus
requires:
  - cone-excess-transfer-reduces-donor-lemma-to-self-bound
artifacts:
  - experiments/self-bound-2026-09-18/swap.py
  - experiments/self-bound-2026-09-18/h2.py
  - experiments/self-bound-2026-09-18/corner.py
  - experiments/self-bound-2026-09-18/seambfs.py
  - experiments/self-bound-2026-09-18/bandcheck.py
  - experiments/self-bound-2026-09-18/chain2.c
  - experiments/self-bound-2026-09-18/run16.sh
  - experiments/self-bound-2026-09-18/chain123.py
  - experiments/self-bound-2026-09-18/rescue2.py
  - experiments/self-bound-2026-09-18/seamrepair.py
  - experiments/self-bound-2026-09-18/scanchain.py
  - experiments/self-bound-2026-09-18/summary.txt
---

**Status: ESTABLISHED (unreviewed).** Elementary cut-and-paste on square-tiled surfaces, plus one exhaustive
finite enumeration (`bandcheck.py`, §4). The conventions are those of `swap.py`, copied unchanged from
`experiments/cone-transfer-2026-09-17`, and "Lemma 1" and "Proposition 7" refer to
`cone-excess-transfer-reduces-donor-lemma-to-self-bound-proof`.

**Conventions.**
- Squares carry corners `4x + j`, with `j = 0, 1, 2, 3` for BL, BR, TR, TL.
- A path state `(x, k)` is a directed edge with square `x` on its left. The direction is `k` (0 right, 1 up, 2 left,
  3 down), the start vertex is corner `4x + k` and the end vertex is corner `4x + k + 1`.
- Moves are straight, left or right; there are no U-turns.
- A swap of two paths with the same word exchanges the gluings across corresponding edges. It is defined when the
  `2L` edges are distinct.
- `nu` is the counterclockwise successor of a corner around its vertex (`nu_map` in `corner.py`). A vertex with
  `N` corners has angle `2 pi N/4`, and `E = sum_v (N_v/4 - 1)`.

**The family.** `S(H, tw)` (`onecyl(1, 2, 3, H, tw)`) has squares `(i, r)` for `i` in `Z/6` and `0 <= r < H`, with:
- `b(i, r) = (i + 1, r)`;
- `c(i, r) = (i, r + 1)` for `r < H - 1`;
- `c(i, H - 1) = (sigma(i), 0)`.

Here `sigma` reverses the three blocks `[0, 1)`, `[1, 3)`, `[3, 6)` of the top row: they land on `[5, 6)`,
`[3, 5)`, `[0, 3)`, followed by the shift `tw`. The seam is level 0: the top edge of row `H - 1`, glued to the
bottom edge of row 0. In *lower coordinates* (along the top of row `H - 1`) its six vertices are at positions
`0, ..., 5`:
- positions `0, 1, 3`, the block ends, are the cone point `A`;
- positions `2, 4, 5` are three regular vertices.

In *upper coordinates* (along the bottom of row 0), `A` sits at `tw + {0, 3, 5}` and the regular vertices at
`tw + {1, 2, 4}`. Off the seam every vertex is regular. So `A` has 12 corners, angle `6 pi`, and `E = 2`. Each
regular seam vertex has one edge in each of the four directions.

## 1. Profile, self-bound point, handles (Theorem 1(a), (b))

`sigma` is a permutation of the 6 top squares and `S(H, tw)` has a single `6 pi` point. So Proposition 7 applies
with `C = 6`:
- (a) `Lambda_rect <= 6` for every `H`;
- `A` is the only cone point, and a lone cone point is self-bound (§3 of the w14 proof);
- the row index mod `H` changes by `+-1` along vertical edges, so every closed edge path has vertical holonomy in
  `H Z`.

If two loops at `A` have `det(u, w) != 0`, at least one of them has nonzero vertical holonomy and hence length at
least `H`. This is (b). Once `H > 8 rho + 4`, the short self-bound loop `u` itself is horizontal, and every partner
`w` of alternative (ii) has length at least `H`.

## 2. Common ends, and the corner rule for loop pairs

Fix two paths `P, Q` with the same word, of length `L`, from distinct states `s_P != s_Q` at `A` with the same
direction. Call the pair *admissible* when:
- the `2L` edges are distinct;
- the `2(L - 1)` interior vertices are pairwise distinct and differ from `A`;
- the two ends coincide.

**Lemma 2.1 (the common end is `A`).** The ends of an admissible pair cannot be a regular vertex.

*Proof.* Same word and same initial direction give the same direction at every step, so the last edges of `P` and
`Q` arrive at the common end `B` from the same direction. A regular vertex has exactly one edge arriving from each
direction, so the two last edges would coincide, which contradicts edge-distinctness. `A` is the only cone
point. □

(The same argument shows in general that Lemma 1(d) needs `B` to be a cone point.) So an admissible pair at `A` is a
*loop pair*: both paths return to `A`. Lemma 1 does not cover this case, because its hypothesis (ii) fails. The
next lemma replaces it.

**Lemma 2.2 (corner rule).** Let `(P, Q)` be an admissible loop pair at a vertex `A` with `N_A` corners. Write:
- `a_P`, `a_Q` for the start corners (`4x + k` of the first states);
- `g_P`, `g_Q` for the end corners (`4x + k + 1` of the last states).

Let `t = (a_P a_Q)` and `u = (g_P g_Q)`. After the swap:
- the corners of `A` form the vertices given by the cycles of `nu' = t o nu o u` on the corners of `A`;
- each pair of interior vertices `u_i, u'_i` is replaced by two vertices with `N(u'_i)` and `N(u_i)` corners;
- all other vertices are unchanged.

Hence `Delta E = 1 - c` when `N_A = 12`, where `c` is the number of cycles. Moreover `c` is 1 or 3, so the swap
lowers `E` if and only if `c = 3`.

*Proof.* Each corner `z` has a unique *next edge* `e(z)`, the edge crossed when turning counterclockwise from `z`
to `nu(z)` about their vertex. After the swap, `nu` changes exactly at the corners whose next edge is a swapped
edge. The interior vertices are not `A`, so the only swapped edges at `A` are the first and last edges of `P` and
`Q`. These four edges are distinct.
- **First edges.** Turning counterclockwise at the tail of an outgoing edge crosses it from its right side to its
  left side, and the corner on the left at the tail is `a_P`. So the corner `z` with `e(z) = ` (first edge of `P`)
  satisfies `nu(z) = a_P`. The swap glues the right side of `P`'s first edge to the left side of `Q`'s first edge,
  so `nu'(z) = a_Q`, and symmetrically for `Q`.
- **Last edges.** At the head of an incoming edge, the counterclockwise turn crosses from the left side to the
  right side, and the corner on the left at the head is `g_P`. So `e(g_P) = ` (last edge of `P`). After the swap,
  crossing that edge from `g_P` enters the square on the right of `Q`'s last edge, at the corner `nu(g_Q)`. So
  `nu'(g_P) = nu(g_Q)`, and symmetrically.
- **The formula.** `nu(g_Q)` is not `a_P` or `a_Q`: that would make `Q`'s last edge equal to `P`'s or `Q`'s first
  edge. A corner `z` with `nu(z) = a_P` is not `g_P` or `g_Q`, for the same reason. Hence `nu' = t o nu o u` on
  every corner of `A`, and `nu'` maps the corners of `A` to themselves.

The interior vertices behave exactly as in Lemma 1(b), whose proof uses only the interior hypotheses. So they swap
their corner counts, and every vertex off the paths is unchanged.

**Count.** The excess of `A` was `N_A/4 - 1 = 2`, and the `c` new vertices carry `N_A/4 - c = 3 - c`. `nu` is a
single 12-cycle on the corners of `A`, so `t o nu o u` is odd and `c` is odd. Every vertex has a multiple of 4
corners, so `c <= 3`. □

**Check** (`corner.py 8`). On all admissible loop pairs of length at most 8 at the cone point of five surfaces, the
predicted partition matched the recomputed one in 1720 of 1720 cases (132, 28, 1032, 432 and 96), with 0
mismatches. The five surfaces were `onecyl(1,2,3,8,1)`, `onecyl(1,1,4,5,0)`, `onecyl(2,3,5,4,2)`,
`twocyl(4,2,1,2,3,1)` and `twocyl(5,1,0,3,2,2)`. The matches include 840 lowering pairs.

So `Delta E` of an admissible loop pair depends only on its *end data* `(a_P, a_Q, g_P, g_Q)` and on `nu`
restricted to the corners of `A`. On `S(H, tw)` that restriction is determined by the rows `H - 1` and `0`, and it
is the same for every `H`.

## 3. Short loop pairs live in a three-level band (Theorem 1(c), reduction)

Let `(P, Q)` be an admissible loop pair at `A` on `S(H, tw)` of length `L < H`.

**Heights.** Let `h(t)` be the sum of the vertical steps (`+1` up, `-1` down) of the first `t` edges. `P` and `Q`
have the same word and the same initial direction, so they have the same direction at every step and the same
function `h`. The vertex level (row index of the vertex, mod `H`) of `P(t)` and of `Q(t)` is `h(t) mod H`.

`P` is closed, so `h(L)` is its vertical holonomy. It lies in `H Z` (§1), and `|h(L)| <= L < H`, so `h(L) = 0`.
Hence `|h(t)| <= min(t, L - t) <= L/2 < H/2` for all `t`. In particular `P(t)` lies on the seam if and only if
`h(t) = 0`.

**Lemma 3.1 (one seam visit).** There is at most one time `0 < t < L` with `h(t) = 0`.

*Proof.* At such a time `P(t)` and `Q(t)` are interior vertices on the seam. So they are distinct, and neither is
`A`: they are two of the three regular seam vertices. Interior vertices at different times are distinct too. Two
such times would need four distinct regular seam vertices. □

So `[0, L]` splits at the zeros of `h` into at most two *segments*. A segment of length 1 with a horizontal step is
a seam edge. Every other segment starts and ends with a vertical edge, and `h` has a constant sign strictly inside
it: it is an *upper* or a *lower excursion*.

**Unrolling.** Take an upper excursion on `[t_a, t_b]`. Its interior vertices lie at heights `1, ..., floor(L/2)`,
which is below `H`. So it stays in the flat part of the cylinder above the seam and never reaches the seam from
below. Unroll that part to the half-plane `Z x [0, infinity)` using upper coordinates. Then:
- `P`'s piece is a lattice path `gamma` from `(x_0, 0)` to `(x_0 + Delta, 0)`, with all interior points at height
  `> 0`;
- `Q`'s piece is `gamma + (D, 0)`, where `D` is the difference of the two start positions: same steps, flat
  region.

The two start vertices are distinct, so `D != 0 mod 6`. Lower excursions are the same, in lower coordinates and the
lower half-plane.

**Lemma 3.2 (width bound).** `1 <= |Delta| < dist(D, 6 Z)`. In particular `|Delta| <= 2`.

*Proof.* Let `T` range over the nonzero integers congruent to `0` or to `D` mod 6.
- **Disjoint translates.** The translate `gamma + (T, 0)` projects either to `P`'s own piece (`T` in `6 Z`) or to
  `Q`'s piece.
  - Interior vertices of `gamma` and of the translate are distinct, by admissibility.
  - Interior vertices lie at height `> 0` and endpoints at height 0, so these never meet.
  - Suppose an endpoint of `gamma` equals an endpoint of the translate. The unique vertical edge above that seam
    point would then be used twice: as the first or last edge of `P`'s piece, and as the last or first edge of the
    other piece. This contradicts edge-distinctness, for `P` alone when `T` is in `6 Z`, and for the pair
    otherwise.

  So `gamma` and `gamma + (T, 0)` are disjoint lattice paths, hence disjoint arcs.
- **Non-interleaving.** Two disjoint arcs in the closed half-plane, with endpoints on the boundary line and
  interiors in the open half-plane, have non-interleaving endpoint pairs (Jordan curve theorem). So the intervals
  `I = [x_0, x_0 + Delta]` and `I + T` are nested or disjoint. They have the same length and `T != 0`, so they are
  disjoint, which means `|T| > |Delta|`. Taking `T` in `{D, D - 6, 6}` gives `|Delta| < dist(D, 6 Z)`.
- **`Delta != 0`.** `Delta = 0` would make the first and last edges of `gamma` the same vertical edge.

Finally, `dist(D, 6 Z) <= 3`. □

**Lemma 3.3 (U-shape replacement).** Replace `gamma` by the U-shape `U` from `(x_0, 0)`:
- one step up;
- a turn towards `Delta`;
- `|Delta| - 1` straight steps;
- a turn down, and one step down to `(x_0 + Delta, 0)`.

Replace `Q`'s piece by `U + (D, 0)`, and do the same in every excursion. The new pair is again admissible, has the
same end data `(a_P, a_Q, g_P, g_Q)`, and lies in the band of vertex levels `-1, 0, 1`.

*Proof.*
- **Same moves for both paths.** `U` has no U-turn, and its first and last edges are those of `gamma`: the
  vertical edges at `x_0` and at `x_0 + Delta`. The move at each segment boundary is between the same edge
  directions as before. So the new words of `P` and `Q` agree, and the first and last states, hence the end data,
  are unchanged.
- **Disjointness.** The vertices of `U` are the interval `I` at height 1, plus its endpoints at height 0. By the
  proof of Lemma 3.2, `I` and `I + T` are disjoint for every `T` there. So `U`, `U + D` and their 6-periodic copies
  are pairwise vertex- and edge-disjoint.
- **Other pieces.** Pieces in the other half and the seam edges are unchanged. The seam vertex at the visit time is
  unchanged and regular.

So every admissible loop pair of length `< H` has the same `Delta E` as an admissible *band pair*, by Lemma 2.2. A
band pair has at most two pieces, each a seam edge or a U-shape of length at most 4, so its length is at most 8. □

**The band is the same for every `H`.** For `H >= 3` the band consists of the squares of rows `H - 1` and `0` with
their mutual gluings. It does not depend on `H`. `S(4, tw)` realises it without wrapping: the band is vertex levels
3, 0 and 1. For `H <= 2`, `L <= 1`, and a one-edge loop at `A` is a horizontal seam edge (`h(1) = +-1 != 0` for a
vertical one), which is also a band pair.

## 4. The finite check (Theorem 1(c) concluded)

`bandcheck.py` enumerates by depth-first search every admissible loop pair at `A` in `S(4, tw)`, taking the
successor states restricted to end levels `{3, 0, 1}`. The search has no length cap: admissibility bounds the
length by the number of vertices. For each pair it recomputes `E` after the swap directly, with `apply_swap` and
`excess`. The output lists the number of admissible pairs, the number that lower `E`, the maximal length, and the
lowering lengths.

| seam lengths | twists | admissible pairs | lowering | max length |
|---|---|---|---|---|
| `(1, 2, 3)` | all 6 | 40 each | **0** | 7 |
| `(1, 3, 2)` | all 6 | 40 each | **0** | 7 |
| `(2, 2, 2)` (control) | all 6 | 156 each | 84, at lengths 2, 4, 6 | 6 |
| `(1, 2, 4)` (control) | all 7 | 28 each | 4, at length 8 | 8 |
| `(1, 1, 4)` (control) | all 6 | 4 each | 4, at length 1 | 1 |

With §3, this proves Theorem 1(c) for `(1, 2, 3)`. The argument of §3 uses only circumference 6, three regular seam
vertices and a single cone point, so it applies verbatim to `(1, 3, 2)`. □

The controls show that the check is not vacuous. In the circumference-7 control `(1, 2, 4)`, §3 still bounds
`|Delta| <= 3`, and the band check (which has no width limit) finds lowering pairs of length 8. Heuristically, the
surfaces without short slit pairs are those where one seam length is the sum of the other two.

## 5. Edge-distinct swaps (computation only)

Theorem 1(c) is about admissible pairs. A swap needs only distinct edges, so `chain2.c` (mode 0, `L1 = 0`)
searches every same-word pair of paths from two sectors of a cone point with distinct edges, any interior vertices,
and ending anywhere. It asks whether the swap lowers the recomputed excess.
- `run16.sh 15` ran this on `S(20, tw)` for `tw = 0, ..., 5` at every length `<= 15`. No lowering swap exists (the
  output is reproduced in `summary.txt`).

So the obstruction does not come from the vertex-distinctness convention.

**Conclusion of Theorem 1.** Take any polynomial `P` and any `H > P(6)`, and let `A` be the cone point of
`S(H, tw)`:
- `rho <= 6`, so `P(rho) <= P(6) < H`;
- every admissible same-vertex slit pair of length `< H` keeps `E`, by §§2-4;
- every sign-matched handle has a loop of length `>= H`, by §1.

So the self-bound step without relocation moves, "(i) or (ii) at length `poly(rho)`", fails on this family.

## 6. One neutral relocation suffices (Theorem 2)

**The excess depends only on the seam.** For a one-cylinder surface with seam permutation `sigma`,
`[b, c] = b c b^-1 c^-1` fixes every square whose downward neighbour lies in the same cylinder copy of the row
structure. So it acts only on row 0, and there it acts as a commutator of `R` (the rotation `i -> i + 1`) with
`sigma`. Hence `E = rank([R, sigma] - I)` on `Z/6`, independent of `H`.

**The chain.** In block form, `sigma = rho_(tw + 3) o (0 2 1)`, where `rho_j` is the rotation by `j` and `(0 2 1)`
is the 3-cycle `0 -> 2 -> 1 -> 0` of top squares. Also `(0 2 1) (0 2) (0 1) = id`. Transposing the `c`-values of
two top-row squares `x, y` is the swap of two one-edge horizontal seam paths, the top edges of `x` and `y`, of cost
`(0, 1)`. So:
- **swap 1** replaces `sigma` by `sigma o (0 2) = rho_(tw + 3) o (0 1)`, whose excess is again 2, so it is
  excess-neutral: a relocation;
- **swap 2** replaces it by `rho_(tw + 3)`, a torus with `E = 0`.

The total cost is `(0, 2)`.

**Checks.**
- `rescue2.py 3 5 7` enumerates every chain of the form in `chain123.py` on `S(H, tw)` for `H = 3, 5, 7` and all
  twists. Swap 1 is a one-edge path from a sector of `A` against any one-edge path of the same direction, keeping
  `E`; swap 2 is `best_swap` at length 1, a one-edge same-vertex slit pair from two sectors of one cone point with a
  common end, reaching `E = 0`.
  - It finds 8 chains for each `(H, tw)`.
  - All of them fix `b` and change `c` only on the top row.
  - Their intermediate seams are the three `rho_(tw + 3) o tau` with `tau` a transposition in `{0, 1, 2}`, and every
    final seam is `rho_(tw + 3)`.
- `chain123.py 9` finds 8 chains for every `3 <= H <= 9`, and 12 or 8 at `H = 2`. After swap 1 the cone structure
  is two `4 pi` points or one `6 pi` point.
- Every step is a statement about the seam alone: the seam vertices and their corner cycles are formed by the
  corners of rows `H - 1` and `0`. So the chain works for every `H >= 2`.

Hence the self-bound step *with* neutral relocation holds on this family, at cost 2.

## 7. Tall one-cylinder surfaces (Proposition 3)

Let `S` have squares `(i, r)`, `i` in `Z/n`, `0 <= r < H`, with `b` and `c` as in the family above but with an
arbitrary seam permutation `sigma` in `Sym(n)`. Assume `H >= n`. For each residue `j`:
- let `C_j = {x : sigma(x) - x = j}`;
- note that `rank(rho_j^-1 sigma - I) <= n - |C_j|`.

Set `d(sigma) = min_j rank(rho_j^-1 sigma - I)`.

**Repair.** Regluing the top row by `c'(i, H - 1) = (i + j, 0)` gives a torus, so `[b, c'] = I`. Also
`rank(c' - c) = rank(rho_j^-1 sigma - I)`. So `S` is within rank `d(sigma)` of a commuting pair, with `b`
unchanged.

**Lower bound for `rho`.**
- A column crosses the seam once in `H` steps up, so `c^H (i, r) = (sigma(i), r)`. Hence
  `[b^s, c^H] = [R^s, sigma] (x) id_rows`, and `rank([b^s, c^H] - I) = H r_s`, with `r_s = rank([R^s, sigma] - I)`.
- So `rho >= H r_s/(s + H) > r_s/2` for `1 <= s <= n - 1 < H`.
- Let `m_s` be the number of points moved by `[R^s, sigma]`. A point `x` is fixed exactly when `x` and `x + s` lie
  in the same class `C_j`. Summing over `s`,

  `sum_(s=1)^(n-1) m_s = n^2 - sum_j |C_j|^2 >= n (n - max_j |C_j|) >= n d(sigma)`.

  So some `s` has `m_s >= d(sigma)`.
- A permutation moving `m` points has rank at least `m/2`, so `r_s >= d(sigma)/2`, and therefore
  `rho > d(sigma)/4`. □

**Check** (`seamrepair.py`, exhaustive over `Sym(n)` for `2 <= n <= 7`, `H = n`, on the actual surface
permutations).
- It asserts every step: `c^H = sigma` rowwise, `[b, c'] = I`, `rank(c' c^-1 - I) = d(sigma)`, the averaging chain,
  and `d(sigma) < 4 H r_s/(s + H)`.
- The largest ratio of `d(sigma)` to the computed profile lower bound is 1.14, at `n = 7`.

On the family of §§1-6, `d(sigma) = 2`: the 3-cycle. Theorem 2's chain is exactly this repair, split into two
transpositions.

## 8. What this leaves

- **Relocation is necessary.** The self-bound lemma of Corollary C must allow neutral moves before the lowering
  swap. The form "(i) a same-vertex slit pair or (ii) a sign-matched handle, at length `poly(rho)`" is false on
  `S(H, tw)` for large `H`, even at `rho <= 6` with a single cone point. With one relocation it holds, at cost 2.
- **One-cylinder surfaces are settled when tall.** The one-cylinder family of Proposition 7, and this one, are
  within rank `4 rho` of a torus whenever `H >= n`. Short one-cylinder surfaces (`H < n`) are not covered by this
  argument.
- **Next step: a cylinder form of Proposition 3.** Every rational direction on a square-tiled surface is
  completely periodic, so the self-bound loop `u` at `A` (length at most `8 rho + 4`) gives a cylinder
  decomposition in direction `u`. The target lemma: each cylinder is either
  - tall (height at least circumference), and then repairable by rotation matching of its seam at cost `O(rho)`,
    since the `c^H` argument above localises to the cylinder; or
  - short, and then crossed by a transverse loop of length at most circumference plus height, which is the candidate
    partner `w` for alternative (ii).

  Several cylinders sharing one seam need a common rotation, and that is the open part.
- **Not addressed.** A transfer that never raises the profile (to make `F` polynomial).
