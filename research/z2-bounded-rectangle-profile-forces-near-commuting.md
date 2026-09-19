---
rg: 2
id: z2-bounded-rectangle-profile-forces-near-commuting
kind: claim
root: true
title: Unitary pairs whose rectangle commutators satisfy rank([b^s,c^t]-I) <= K(s+t) for all s,t are within rank F(K) of a commuting pair
distinct_from:
  z2-commuting-pairs-are-not-bounded-rank-stable: that refutes stability under a bounded commutator rank; this assumes a bounded linear profile over all rectangle words, which both the dislocation dipole and the slit origami violate.
  slit-origami-z2-pair-has-rank-distance-half-l: that computes the rank distance of one pair with quadratic profile; this asks whether a linear profile forces bounded distance.
  near-exact-tuples-saturate-linear-conversion-defect: that proves the converse direction (distance delta gives profile constant 2 delta) and that linear order is the near-exact noise floor; this is the forward direction.
  deligne-cover-bounded-rank-sector-tuples-have-bounded-dimension: that is the rung; this is the commuting-rounding input its long-root route needs for g >= 5, not the rung itself.
---

**OPEN.**

**Statement.** Define the rectangle profile of unitaries `b, c` in `U(d)` as
`Lambda_rect(b,c) = sup_(s,t >= 1) rank([b^s, c^t] - I) / (s + t)`. There is a function `F` such that
`Lambda_rect(b,c) <= K` implies that some commuting pair `b', c'` (after padding by `U(m)`) has
`max(rank(b' - b (+) beta), rank(c' - c (+) gamma)) <= F(K)`. The bound must not depend on `d`.

**Converse (proved).** Rank distance `delta` gives `Lambda_rect <= 2 delta`: this is Lemma B of
`near-exact-tuples-saturate-linear-conversion-defect-proof`. So, if the statement holds, the rectangle
profile is a coarse (bounded-rank-invariant) measure of the distance to commuting pairs.

**Why this is the right target.**
- Every word-growth invariant has its near-exact noise floor at linear order
  (`near-exact-tuples-saturate-linear-conversion-defect`). So sublinear forms such as "conversion
  defect `o(L)`" are false, and linear order is the finest scale at which an invariant of this kind can see.
- `sln-relators-force-linear-commutator-growth` gives `Lambda_rect(rho(u), rho(v)) <= C_n k` for
  every commuting root pair of a rank-`k` tuple of `SL_n(Z)`, `n >= 5`. The extension to `s != t` is the
  same proof: `Area([u^s, v^t]) <= C_2 (s + t) + O(log^4 (s + t))` via `W_s(u)`, `W_t(v)`. This covers
  Deligne sector tuples with `g >= 5` through the `SL_g(Z)` Levi.
- Both known far-from-commuting families with bounded commutator rank have quadratic profile up to
  their defect scale: the dislocation dipole and the slit origami, `phi(m) = 2 m^2`. No pair is known
  that has bounded `Lambda_rect` and is far from commuting.

**Reduction (one direction).** Suppose the statement holds. Then for `g >= 5` the commuting root pair
`(rho(e_13), rho(e_23))` of the `SL_g(Z)` Levi of every rank-`k` sector tuple lies within rank `F(C_g k)` of a commuting
pair. This is the rounding input that the joint-spectrum route of the rung needed and that
`z2-commuting-pairs-are-not-bounded-rank-stable` showed cannot come from `Z^2` alone. It does **not**
by itself give the rung. The atom-level `SL_2(Z)` rigidity step recorded in the rung's Attempts
(interlacing) is still needed after rounding.

**Easiest nontrivial case and first falsifiable step.** Take permutation pairs, that is, square-tiled
surfaces. Here `rank([b,c] - I)` bounds the total cone excess. A rectangle loop based at `x` fails to
close only if the rectangle at `x` meets the singular set with nontrivial monodromy. `Lambda_rect <= K`
forces every cone point to have flat injectivity radius `O(K)`, because an embedded `R x R` cone disk
gives `~R^2/4` non-closing loops at scale `R/2`. The step to check is whether each cone point then
lies on a saddle connection or cylinder boundary of length `O(K)` whose regluing removes it at rank
cost `O(K)`, so that `F(K) = O(K^2)` for permutations. The examples fit this picture:
- slit of length `s`: `Lambda ~ s`, distance `s/2`;
- L-shaped origamis: distance `<= 2`;
- tall thin cylinders of circumference `c_0`: `Lambda ~ c_0`, regluing cost `c_0`.

A counterexample would need cone points whose short loops are all diagonal, or a genuinely
non-permutation unitary construction.

## Attempts

- **Cone-radius regluing for permutation pairs (2026-09-18, w6-124, transplanter). Where it stops.**
  - **Proved.** An embedded flat `R x R` disk around a cone point gives about `R^2/4` non-closing
    rectangle loops at scale `R/2`. So `Lambda_rect <= K` bounds every flat injectivity radius by
    `O(K)`.
  - **Where it stops.** A short injectivity radius yields a short closed curve through the cone point,
    but not one along the `b` or `c` direction. The regluing step needs a horizontal or vertical saddle
    connection of length `O(K)`. If every short connection is diagonal, cutting along it changes the
    rank of both `b - b'` and `c - c'` by its combinatorial length in the other generator. No bound in
    `K` for that length is known yet.
  - **General unitaries.** Beyond permutations there is no singular set. The profile controls
    `rank([b^s,c^t] - I)` only, which gives interlacing and not atoms: the same barrier as the rung's
    D2 attempt. The permutation case is the first step to settle.
- **GL2(Z) change of generators plus band surgery (2026-09-18, w7-124, transplanter). Settles the abelian
  class; the non-abelian thin case is open.**
  - **Proved** (`torus-abelian-covers-rectangle-profile-near-commute`). Take any regular abelian cover
    of a square-tiled torus, with any number of squares. Rectangle profile `K` gives distance
    `exp(O(K log K))`. For dipole covers (for example the slit origami) the bound is `3072 K^4`.
  - **How the diagonal gap closes.**
    - Rewrite the pair in the basis `(v, u)`, where `v` is the primitive shortest lattice direction:
      `B = b^(v1) c^(v2)` and `C = b^(u1) c^(u2)`.
    - The short diagonal becomes the generator `B`. Cut and reglue `C` along the rows of `B`
      (the band surgery).
    - Back-substitute `b'' = B^(u2) C''^(-v2)` and `c'' = B^(-u1) C''^(v1)`. The cost is
      `6 |A| n lambda_1^4`, where the charge count `|A| n <= 4K` comes from Stokes.
    - When `lambda_1` is large, hierarchical clustering of the charges shows that the profile forbids
      non-neutral clusters.
  - **Computation.**
    - Exhaustive for Z/2 dipole covers with `N <= 40` (exact profile).
    - For `N <= 22`, the explicit commuting pairs are within `2.5 K` in every case.
    - General loops beat rectangles by at most `1.25x`.
    - Result: no counterexample. In range, the distance is linear.
  - **Where it stops.** General origamis are covers with non-abelian fibre. In the thin case, the row
    monodromies of `B^k` at the two ends of a band are conjugate rather than equal. Regluing needs a
    conjugating fibre bijection, whose rank cost is not yet bounded by `K`. Bounding that cost is
    the next step.
- **Conjugating fibre bijections for the non-abelian thin case (2026-09-18, w8-124, transplanter).
  Dead: the step is false.**
  - **Proved** (`centralizer-rounding-cannot-bound-rank-distance-by-profile`). The example is a
    cross-slit pair on `(Z/p)^2 x Z/2`, with one swap on `b` and one swap on `c`. It has profile at most
    2 and distance 1. Yet every commuting pair that keeps a word `b^v1 c^v2` with `|v|_1 < p`, and
    changes only the other generator inside its centralizer, costs at least `2p`.
  - **Why this settles the step.** Over the one-square torus every permutation pair is thin, and
    band surgery there means "keep `b`, conjugate `c`". So the conjugator cost of the proposed step is
    not bounded by any function of `K`.
  - **Why it fails.** The 2p-cycles of the kept word lie over a proper set of base orbits. The other
    generator translates that set, so every conjugator must move it.
  - **Computation** (exact: all frames for `p = 11, 13, 17`, and cylinder variants). On random
    `S_3`, `Q_8` and `A_4` slit covers, one-sided rounding stays within `3.4 K`. Those covers have long
    slits, whereas the obstruction lives in short cross slits.
  - **What it leaves.** Any proof of the forward statement has to be two-sided and local near the
    defects: it must change both generators, as the abelian path cuts do. For general permutation
    pairs, the open step is a local two-sided surgery around non-commuting cone points whose cost
    is bounded by the profile.
- **w8-124, 2026-09-18 — two-sided strip cut for abelian dipoles. Landed: F(K) <= 24 K on dipole covers.**
  See `torus-dipole-covers-rank-distance-linear-in-profile`.
  - **Method.** Cut the row circle of the shortest lattice direction at the two charged rows, and reglue each
    arc into its own torus. This redirects `2 lambda_1` moves. Then cancel the seam charges along a
    digital line of `lambda_1` squares. In total `6 lambda_1` sites change, so `dist <= 6|A| lambda_1 <= 24 K`.
  - **Result.** This replaces the `3072 K^4` of the dipole case. It is linear, as the data had
    suggested.
  - **Computation.** Checked assertion by assertion on 4342 exhaustive cases (`N <= 20`). The construction
    has `dist/K <= 4.5`, and the best of all two-cuts has `dist/K <= 1.67` (`N <= 16`).
  - **Open.** Two steps remain:
    - several charges, where the merged clusters are not neutral; a cost of `O(|A|(n lambda_1 + n^2))` looks
      plausible for the thin case;
    - non-abelian fibres, where band cancellation needs the ordered product of the charges to be trivial.
- **w9-124, 2026-09-18 — non-abelian band cancellation, settled both ways. Landed: F(K) <= 36 K on regular
  two-charge covers with any finite fibre group.**
  - **Obstruction** (`nonabelian-band-rungs-absorb-ordered-charge-product`, Theorem 2). The ordered product of
    the charges in a band piece is a commutator of the piece's holonomies. No change supported in a disk can make
    it trivial: a flat connection that agrees off `S` has trivial boundary holonomy on the filled lift of every
    inessential component of `S`. So fewer than `lambda_1` changes can cancel charges only in disk clusters
    whose product is 1, and a single charge costs at least `lambda_1`.
  - **Theorem** (same node, Theorem 1, the rung lemma). If every charge lies in an essential band of `m`
    faces, changing only its `m` rungs makes the connection flat, for every fibre group.
    - *Proof idea.* The complement of the band is a flat annulus. A flat model with the same core holonomy exists
      on the whole torus, and a gauge on the annulus matches the two.
    - *Cost.* Compared with the abelian tree it costs one extra edge per band. With `m = lambda_1` it is optimal.
  - **Two-charge theorem** (`nonabelian-two-charge-torus-covers-rank-distance-linear`). `dist <= 36 rho` for regular
    `F`-covers with at most two charged faces and arbitrary charges. The ingredients:
    - box counting on free fibres gives `rho >= |F| ceil(m_0/2)/2`, plus a separate bound for short
      dipoles that are not neutral;
    - a push along a shortest path;
    - the abelian strip cut, with rung-closed bands.
  - **Computation.** `rungs.py` ran on 6900 covers with fibres `S_3`, `Q_8` and `A_4`. Tree-only closing fails on
    3641 of the 5056 bands, and the rung lemma closes all of them. The worst ratio is `dist/rho_lower = 7.10`.
  - **Open.** Two steps remain:
    - *several charges*: neutrality is no longer needed inside a piece, but a lower bound
      `rho >~ |F| n lambda_1` for `n` non-neutral clusters is still missing;
    - *non-free fibres and general permutation pairs*: a charge may move only a few points, so the box count
      `|F|/2` per box fails. This is the step that separates the regular-cover results from the full statement.
- **w10-124, 2026-09-18 — any number of charges, and non-free fibres. Landed: F(K) = O(K^4) on all regular torus
  covers; dist <= 608 rho^4 (rho + |Y|) on all covers with fibre Y.**
  - **Multi-charge lower bound** (`regular-torus-covers-rank-distance-polynomial-in-profile`). Cluster the lifted
    charges at a threshold `theta`, merging when translated bounding boxes come within `l^inf` distance `theta`.
    - When `lambda_1 >= 2(n+1) theta`, a cluster that is not neutral is isolated by `(theta+1)^2` boxes with
      distinct corners, each with holonomy conjugate to the cluster's. This gives
      `rho > theta sigma / (4(n+1))`, where `sigma` is the support size of the cluster holonomy.
    - So `theta ~ 4(n+1) rho/|F|` forces every cluster to be neutral.
    - The bound is not of the form `|F| n lambda_1` asked for. Instead it picks a scale at which every cluster is
      neutral.
  - **Theorem A.** Every regular `F`-cover has `dist <= 10^4 rho^4/|F|^3`. There are two cases.
    - Thick tori: pushes inside disjoint cluster boxes.
    - Thin tori (`lambda_1 < 2(n+1) theta`): the strip cut at every charged-row gap of more than `2l`, walks of at
      most `2n` steps into a digital band, and rungs. This costs `3 n lambda_1 + 2 n^2` sites.
  - **Non-free fibres (Theorem B).** The replacement for `|F|/2` is `|supp hol|/2`. It weighs the lower bounds
    (`sum supp <= 4 rho`, so `n <= 2 rho`) and the push costs (supports are subadditive). This gives
    `dist <= 384 rho^5` on tori with `lambda_1 >= 96 rho^3`, for every fibre, and `dist <= 608 rho^4 (rho + |Y|)` in
    general.
  - **Computation.** `multicharge.py` ran on 600 covers with fibres `S_3`, `Q_8`, `A_4`, `S_3` on 3 points and `S_4`
    on 4 points, and up to 13 charges. All steps and bounds were checked, including 171 box-count lemmas.
  - **Open.**
    - *Thin tori with large fibres.* There, strip redirects and rungs cost `|Y|` each. Every pair on `d` points is a
      cover of the one-square torus, so removing this factor, or finding thick equivariant quotients with small
      fibres, is the remaining step to the full statement.
    - *Linearity.* A heuristic multi-scale `Z/2` example suggests that single-scale box counting cannot give
      `O(K)`.
- **w11-124, 2026-09-18 — removing the `|Y|` factor on thin tori. Obstruction: neither proposed route works. Landed
  `two-torus-cross-slit-forces-sqrt-d-loss-in-thin-closing`.**
  - **The family.** Take `(Z/p)^2 ⊔ (Z/(p+1))^2` with the unit translations. Swap the images of `(0,0)` and `(0,0)`
    under `b`, and do the same under `c`. This gives `rho <= 2` and `dist = 1`.
  - **No thick quotient.** The coprime row lengths `p` and `p+1` force the period lattice to be `Z^2`. So the
    one-square torus is the only grid torus the pair covers, and route (ii), in the form of an exact equivariant map
    to a thick torus, has nothing to map to.
  - **One-sided thin closing.** There Theorem B's thin construction makes no push and changes one rung, so it keeps
    one generator. The merged `b`-cycle of length `2p+1` is unique, so every `c'` in `C(b)` disagrees with `c` at
    `4p+2` points, and the cost is at least `2p+1 > sqrt(2d) - 1`. Route (i), weighting the rungs by support, cannot
    help: it is still one-sided. The count `4p+2` is exact for `p <= 15` (`twotorus.py`).
  - **What it leaves.** A proof for all pairs must include a two-sided surgery that is not equivariant, done on the
    square-tiled surface itself (here, undoing the slit). The next target is a *slit-pair lemma*. At a cone point
    with excess, find two parallel saddle connections of `l^1` length `poly(rho)` whose swap lowers the total excess.
    There are at most `2 rho` excess units, so iterating the lemma would finish the proof.
- **w12-124, 2026-09-18 — the slit-pair lemma, tested both ways. Two-sided swaps close the cross slit, but the
  lemma is false. Landed: `excised-square-kills-cone-local-slit-pair-repair`.**
  - **Calibration.** A slit-pair swap exchanges the gluings along two grid paths with the same move word. On the
    coprime two-torus cross slit, the shortest excess-lowering swap has 2 edges (the two L-slits) and costs `(1, 1)`.
    It closes that family at distance 1 (`certify.py`, part A).
  - **Obstruction.** Excise one square of the `n x n` torus into its own `1 x 1` torus. The pair has
    `rho <= 2` and `dist = 1`. Its other component `S'` has genus 2 and one `6 pi` cone point.
    - Every commuting permutation pair on `S'` costs at least `(n - 1 - n/p)/2 >= n/4 - 1/2`, where `p` is the least
      prime factor of `n`. The intact `n`-cycles force the big torus to have area dividing `n^2`, and `S'` has area
      `n^2 - 1`.
    - So every excess-lowering swap at the cone point is that long. The exact minimum is `n - 1` for
      `4 <= n <= 7`.
    - Every cone-local chain costs at least as much, and so does every padding-free rounding of the permutation pair
      `S'`, which has `rho(S') <= 2`.
  - **Where it fails.** The cheap repair uses a flat donor (the stranded square, or a padded point), and its first
    step leaves the excess unchanged. So excess is not a monotone potential for local moves. Greedy lowering swaps
    strand small flat tori the same way in 5 of 178 random clustered perturbations.
  - **Next step: a donor slit-pair lemma.** Pad by a flat torus of area `poly(rho)`. Then some chain of at most two
    swaps of total length `poly(rho)` should lower the excess, with the first swap allowed to be excess-neutral and
    to use the donor. With `rho(b', c') <= rho + 2 * cost` and `excess <= 2 rho`, this would settle the permutation
    case with an iterated `F`.
- **w13-124, 2026-09-18 — the donor slit-pair lemma. One mechanism proved, and every stall resolved. The lemma is
  still open. Landed `lattice-donor-excises-sign-matched-cone-handles`.**
  - **Context.** w12-124 (landing pending) showed that the plain slit-pair lemma fails. On the excised-square torus
    (`rho <= 2`, `dist 1`), every cone-local slit-pair repair costs at least `n/4`. So the step is: pad with a flat
    donor torus, allow a first swap that keeps the excess unchanged, then lower the excess.
  - **Proved (handle excision).** Take two edge loops `alpha, beta` at a cone point, with holonomies `u, w` and
    `det(u, w) != 0`. Suppose `beta` crosses `alpha` with the sign of `det`, and the copies of the loops in
    `Z^2/<u,w>` are simple. Then two swaps with that donor, of area at most `|alpha||beta|`, excise them:
    - the first swap is excess-neutral and splits the cone point;
    - the second swap lowers the excess by exactly 2;
    - `rho` grows by at most `2(|alpha| + |beta|)`.
    This closes w12-124's excised square at total length 2, and excised `k x l` blocks at length `k + l`, which is
    linear in the measured profile.
  - **Computation.**
    - The sign condition is sharp: 600 lowering pairs out of 8298, and all of them satisfy (H1).
    - The donor two-swap search resolves all 13 greedy stalls of w12-124, at total length at most 8 (at most 5 with a
      donor).
    - Iterated greedily on 737 random clustered perturbations, it never stalls.
    - The 8 uninvestigated stalls are not arithmetic: each has a full-area excess-2 component. They are artifacts of
      a greedy that allows only lowering first moves. The chains that resolve them first move or merge cone points
      with a neutral transposition, then slit.
  - **Open (the next step).** The dichotomy at length `poly(rho)`: every cone point carries one of the following.
    - a same-vertex slit pair;
    - a sign-matched handle satisfying (H1) and (H2);
    - a neutral cone move that produces one of the first two.
    The cone-radius bound gives a short loop or saddle connection at each cone point. Two things are missing: the
    partner loop with the right crossing sign, and the simplicity of the donor copies.
- **w14-124, 2026-09-18 — the donor slit-pair lemma. Reduced to self-bound cone points; both alternatives shown
  necessary. The lemma is still open. Landed `cone-excess-transfer-reduces-donor-lemma-to-self-bound`.**
  - **Proved (transfer).** Swapping `k + 1` same-word paths that leave a `2 pi (k + 1)` cone point one turn apart,
    in the sequential order `P_(j-1) <-> P_j`, empties that point. The total excess stays the same, or drops by 2
    when two current ends coincide, and the cost is at most `k |P_0|` per generator.
  - **Proved (cone-ball dichotomy).** Develop the cone ball at a cone point `A` into the surface. Rectangle counting
    closes it at radius `r* <= 2 rho + 1`. Then one of two cases holds.
    - *Free:* the first collision is another cone point, and the rotated staircases to it satisfy the transfer
      hypotheses. So the transfer lowers `E`, or keeps `E` and lowers the number of cone points.
    - *Self-bound:* `A` carries an edge loop of nonzero holonomy and length at most `8 rho + 4`.
  - **Consequence.** Only the self-bound case of the donor lemma remains. If a self-bound lemma holds at polynomial
    length `P(rho)`, the permutation case follows with an explicit `F(K)`. This `F` is not polynomial
    (`exp(O(K^2 log K))` even for linear `P`), because each transfer raises the profile.
  - **Both alternatives are needed (proved).** One-cylinder surfaces with a single `6 pi` point have
    `Lambda_rect <= C` for every height `H`. Every sign-matched handle there has length at least `H`, yet a one-edge
    same-vertex slit pair lowers `E` to 0. The excised square is the reverse case.
  - **Computation.**
    - The transfer prediction matched in 60 422 of 60 422 cases.
    - The sequential chain behaved as predicted in all 41 451 swaps.
    - Pairing `P_0` with `P_j` instead fails in 347 steps.
    - Loop copies were neutral in all 767 cases.
  - **Open (the next step).** The self-bound lemma: at a cone point whose developed ball closes on itself, find one
    of the following at length `poly(rho)`.
    - a same-vertex slit pair;
    - a partner loop crossing the short loop with the sign of `det`, whose donor copies are simple;
    - a counterexample family of self-bound points where neither exists.
    A polynomial `F` would also need a transfer that does not raise the profile at every step.
- **w15-124, 2026-09-18 — the self-bound lemma. Obstruction: without relocation moves it is false. Landed
  `seam-surface-forces-neutral-relocation-in-self-bound-lemma`.**
  - **The family.** `S(H, tw)` is one horizontal cylinder of circumference 6 and height `H`, with its top glued to
    its bottom by the interval exchange that reverses lengths `(1, 2, 3)` (then twist `tw`). It has a single `6 pi`
    cone point `A`, so `E = 2`, and `rho <= 6` for every `H`. So `A` is self-bound.
  - **Theorem 1.** Every loop at `A` with nonzero vertical holonomy has length `>= H`, so every sign-matched handle is
    long. No admissible same-vertex slit pair of length `< H` lowers `E`. The proof uses a corner rule for loop-pair
    swaps and the fact that both paths keep equal heights. It then reduces every pair to a three-level band at the
    seam, and one exhaustive band check finds 40 pairs, none lowering. So neither (i) nor (ii) exists at length
    `poly(rho)` once `H > poly(6)`.
  - **Theorem 2.** One neutral relocation (two one-edge swaps of top-row `c`-values) reaches a torus, at cost 2. So
    the self-bound lemma must allow neutral relocation moves before the slit pair or handle.
  - **Proposition 3.** Every one-cylinder surface of height `H >= n` is within rank `4 rho` of a torus, by regluing
    the seam with the best rotation (`b` unchanged).
  - **Open.** The cylinder form of Proposition 3. The short loop `u` at a self-bound point gives a periodic
    decomposition in direction `u`. Tall cylinders should be seam-repairable at cost `O(rho)`, and short ones crossed
    by a partner loop of length `poly(rho)`. A seam shared by several cylinders is the missing case. A transfer that
    never raises the profile was not found.
- **w16-124, 2026-09-18 — the cylinder form of Proposition 3, with shared seams. Landed
  `tall-cylinder-seams-reglue-within-quadratic-profile`: F(K) = 176 K^2 on the locally tall class.**
  - **Theorem 1.** Take the horizontal cylinders `C_j` that are not torus components (at most `4 rho` of them), with
    widths `w_j`, heights `h_j`, and `tau_j` the least height among `C_j` and its seam neighbours. Some `c'`
    commuting with `b` differs from `c` only on top rows, at at most `96 rho^2 + 20 rho sum_j w_j/tau_j` points. So if
    `w_j <= tau_j` for every `j`, the pair is within `176 rho^2` of commuting, with `b` unchanged.
  - **Proof idea.** With `t = tau_j`, every orbit of `c^t` counted crosses exactly one seam.
    - *Width lemma.* With `s = w_j`, `b^s` fixes `C_j`, so seam points into cylinders of non-dividing width are
      few (`u_j <= 2 rho (1 + w_j/tau_j)`); the same holds from below.
    - *Offset lemma.* Averaging over `s < w_j` bounds the defect of the best rotation class.
    - *Regluing.* Majority classes pick distinct targets, and a width-preserving completion exists.
  - **Theorem 2 (sharpness).** On the excised square `T_n` (`rho <= 2`, distance 1) every regluing that keeps `b`
    costs at least `2(n-1)`, while `w_B/tau_B = n - 1`. The ratio term is needed, and short wide cylinders need
    two-sided moves.
  - **Theorem 3 (height gap).** If the seam joins `a` top points of `C_j` to `C_beta`, with `w_beta != w_j`, then
    `a min(h_j, h_beta) <= 2 rho (max w + min h)`. So a mismatch of mass `a >= max w/2 >= 4 rho` forces a cylinder of
    height `<= 8 rho`: short means `O(rho)`, not just shorter than wide.
  - **Computation.** `seams.py` ran on 450 random multi-cylinder surfaces. It checked every inequality and compared
    with the exact one-sided optimum (an assignment). Tall cases have `alg <= 1.57 rho_hat^2`.
  - **Open.** Pairs with a locally wide cylinder in both directions. The next step is a two-sided width adjustment:
    padding or deleting a column of a height-`h` cylinder costs `O(h)`. The profile should bound
    `sum_j h_j |w_j - w'_j|` for some matchable width vector `w'`.
- **w17-124, 2026-09-18 — the doubly-wide case. Width matching plus one-sided regluing is killed. Landed
  `excised-thick-torus-kills-width-matched-one-sided-repair`.**
  - **Family.** The thick torus `Z/(a^2+1)` with `b = +1` and `c = +a` is one row, wide in both directions. Excise
    the `k` squares `0, ..., k-1` (with `a >= 2k+1`) to get `E(a, k)`.
    - It is within rank `k` of the torus in each generator, so `Lambda_rect <= 2k` by Lemma B.
    - Both decompositions are a single self-glued cylinder of width `n = a^2 + 1 - k` and height 1.
  - **One-sided costs.** In `b`-order, `c` is a 3-interval exchange, so keeping `b` costs exactly `a`. In `c`-order,
    `b` is translation by `-a+1` on an arc of `k(a-1)` points and by `-a` elsewhere, so keeping `c` costs exactly
    `k(a-1)+1`. The computation matches for `a <= 13`.
  - **What this kills.** On `E` the width defect `sum_j h_j |w_j - w'_j|` is 0 and Theorem 3 is vacuous. So the
    brief's step holds trivially, but combining it with Theorem 1 of
    `tall-cylinder-seams-reglue-within-quadratic-profile` costs `~ sqrt(d)` at profile `2k`. The repair that works
    is `k` column insertions at the holes, which are the break points of the seam. So a certificate must locate
    columns, not only count them.
  - **Next.** The one-row case: `b` an `n`-cycle and `c` a `b`-interval exchange with `<= 4 rho` breaks. Show that
    profile `K` gives a rotation after `O_K(1)` column insertions and deletions at the breaks. This is Theorem 1 with
    an interval transversal, in the style of zippered rectangles and Rauzy–Veech induction.
- **w18-124, 2026-09-19. The one-row step (a rotation after column insertions) is false; the corrected target is the
  arc-torus. Landed `one-row-profile-pairs-need-arc-tori-not-rotations`.**
  - **Break lemma.** For `b = +1`, `Lambda_rect <= sup_t |B_t|`, where `B_t` is the set of breaks of `c^t`.
  - **Obstruction.** Take `c` fixing `A = [0, alpha)` and swapping `B` and `C`. Then `|B_t| <= 3`, so the profile is at
    most 3.
    - Every single-row repair costs at least `min(alpha, beta + gamma) / 2`. The reason is that the centraliser of a
      full cycle consists of its powers, and a power is either the identity or fixed-point-free.
    - Cutting the row into `A` and `B u C` costs 1.
    - So any argument that outputs a single row fails, including Rauzy–Veech induction with one interval as
      transversal. A repair must cut the row.
  - **Exact reformulation.** Permutation distance is equivalent, up to a factor of 2, to the least `max(m, e)` over
    `(m, e)`-arc-tori. These are commuting pairs whose rows are concatenations of at most `m` old arcs and padding
    runs, with `c` changed at `e` old points.
  - **E(a, k) is the twist theta = beta + gamma.** It is repaired with `m = 2` and `e = beta` by column insertion.
  - **Data.**
    - Resonant twists `n/q` have profile about `2q`.
    - Generic twists with `beta = 1` have profile about `sqrt(n)/2`.
    - `(400, 157, 229, 75, 96)` is two thin diagonal arc-tori (`c^3 = b^-4` and `c^2 = b^10`) at profile about 10.
  - **Next.** Show that profile `K` gives an `(F(K), F(K))`-arc-torus with its cuts in `U_{|j| <= O(K)} c^j(B_1)`.
