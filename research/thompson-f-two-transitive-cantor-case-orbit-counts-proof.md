---
rg: 2
id: thompson-f-two-transitive-cantor-case-orbit-counts-proof
kind: route
title: The triangle inequality for disagreement sets gives one-sided support at irrational points, products over good cuts follow by induction, and counting orbits on pairs times a good orbit in two ways gives the stabilizer counts
target: thompson-f-two-transitive-cantor-case-orbit-counts
requires:
  - thompson-f-two-transitive-disagreement-sets-are-self-similar
  - thompson-f-two-transitive-irrational-orbit-colorings
---

Notation as in the target. Imported statements, verbatim.

From `thompson-f-two-transitive-disagreement-sets-are-self-similar`:

- (SS1) "`D(ω,ω')` is closed, `D(ω,ω') = D(ω',ω)`,
  `D(gω,gω') = g D(ω,ω')` for `g ∈ F`, and `D(ω,ω') = ∅` iff `ω = ω'`.
  For any `ω_1, ω_2, ω_3`, every point of
  `D(ω_1,ω_2) ∪ D(ω_2,ω_3) ∪ D(ω_1,ω_3)` lies in at least two of the three
  sets."
- (SS2) "All disagreement sets of distinct pairs form one `F`-orbit of closed
  sets. Call a representative `D_0`. It is a compact subset of `(0,1)`."

From `thompson-f-two-transitive-irrational-orbit-colorings`:

- (C1) "If `y` is irrational, then `F_y = G_y`, and `G_y·aH ↦ H·a^{-1}y` is a
  bijection from the `G_y`-orbits on `Ω` onto the `H`-orbits on `F·y`."
- (C5A) "(A) `D_0` is a Cantor set. The good points form an `F`-invariant
  comeager subset of `(0,1)`. There is an irrational orbit on which `H` is
  transitive, and `H` is transitive on `F·y` for every good irrational `y`."
- (C6) "Let `y` be a good irrational point. [...] Then `G_y = A_y × B_y`, the
  map `ω_1 ↦ (B_y ω_1, A_y ω_1)` is a bijection from `Ω` onto
  `Ω/B_y × Ω/A_y`, `A_y` acts on the first factor and trivially on the second,
  `B_y` acts the other way round, and `H ∩ G_y = (H ∩ A_y) × (H ∩ B_y)`."
  Step 6 of its proof shows `G_y = A_y × B_y` for every irrational `y`
  (goodness is used only for surjectivity).

Two elementary facts are used without further comment.

- (T) Triangle inequality: `D(ω_1,ω_3) ⊆ D(ω_1,ω_2) ∪ D(ω_2,ω_3)`. This follows
  from the last sentence of (SS1): a point of `D(ω_1,ω_3)` lies in a second
  one of the three sets.
- (DI) For dyadic `p < q` and dyadic `p' < q'` there is a PL homeomorphism
  `[p,q] → [p',q']` with dyadic breakpoints and slopes powers of `2`. Proof:
  split `[p,q]` into standard dyadic intervals `[k2^{-j},(k+1)2^{-j}]`.
  Halving one piece raises the number of pieces by one, so both intervals
  can be split into the same number `N` of standard pieces. Map the `i`-th
  piece affinely onto the `i`-th piece. Gluing such maps with the identity or
  with affine dyadic maps gives elements of `F`.

Orbit-counting principle (OC): if a group `Q` acts transitively on a set `Y`
with stabilizer `Q_y`, then `Q·(x,y) ↦ Q_y·x` is a bijection from the
`Q`-orbits on `X × Y` onto the `Q_y`-orbits on `X`. It also restricts to any
`Q`-invariant subset of `X × Y`.

**Step 0 (good points avoid every disagreement set).** If `y` is good, then
`G_y ω_1 = Ω`, so `y ∉ D(ω_1,ω_2)` for all `ω_1, ω_2`. This is the definition
of `D`.

**Step 1 (item 1).** Let `y` be irrational.

- If `ω_2 = aω_1` with `a` supported in `[0,c]`, `c < y`, then `a ∈ G_x` for
  every `x ∈ (c,1]`, so `D(ω_1,ω_2) ⊆ [0,c] ⊆ [0,y)`.
- Conversely, let `D(ω_1,ω_2) ⊆ [0,y)`. Then `y ∉ D(ω_1,ω_2)`, so
  `ω_2 ∈ G_y ω_1`. Since `G_y = A_y B_y`, write `ω_2 = abω_1` with `a ∈ A_y`
  and `b ∈ B_y`, and put `ω_3 = bω_1`, so `ω_2 = aω_3`.
- By the first bullet and its mirror, `D(ω_3,ω_2) ⊆ [0,y)` and
  `D(ω_1,ω_3) ⊆ (y,1]`. By (T),
  `D(ω_1,ω_3) ⊆ D(ω_1,ω_2) ∪ D(ω_2,ω_3) ⊆ [0,y)`.
- So `D(ω_1,ω_3) = ∅`, hence `ω_3 = ω_1` by (SS1), and `ω_2 = aω_1 ∈ A_yω_1`.

The statement for `B_y` is the mirror image. Goodness is not used, so item 1
holds in both cases of the dichotomy.

**Step 2 (item 2).** First take `n = 2`, with good irrational `y < z`.

- By (C6) at `y`, `Φ_y : Ω → L_y × R_y` is a bijection. `B_z ≤ B_y` acts
  through the second factor.
- Hence `L_z = Ω/B_z ≅ L_y × (R_y/B_z)`. Since `A_y` and `B_z` commute,
  `R_y/B_z = (Ω/A_y)/B_z = Ω/(A_yB_z) = M_{y,z}`. Under this identification
  `B_zω_1` corresponds to `(B_yω_1, A_yB_zω_1)`.
- Composing with the bijection `Φ_z : Ω → L_z × R_z` of (C6) at `z` gives the
  bijection `Ω → L_y × M_{y,z} × R_z` of item 2.

Induction on `n`: suppose the bijection holds for `y_1 < … < y_{n-1}`.

- `B_{y_{n-1}}` acts trivially on `L_{y_1}` (as `B_{y_{n-1}} ≤ B_{y_1}`) and
  on each `M_{y_i,y_{i+1}}` with `i ≤ n-2` (as `B_{y_{n-1}} ≤ B_{y_{i+1}}`).
  It is transitive on `R_{y_{n-1}}`: `G_{y_{n-1}} = A B` is transitive on
  `Ω ≅ L × R` and `A` acts trivially on `R`.
- So `L_{y_{n-1}} = Ω/B_{y_{n-1}} ≅ L_{y_1} × M_{y_1,y_2} × … × M_{y_{n-2},y_{n-1}}`.
- Combining this with the case `n = 2` at `(y_{n-1}, y_n)`, which gives
  `Ω ≅ L_{y_{n-1}} × M_{y_{n-1},y_n} × R_{y_n}`, proves the bijection for `n`
  points. The coordinates are those displayed in item 2.

Stabilizer. Each `y_i` is irrational, so `F_{y_i} = G_{y_i}` by (C1). Let `k`
be the identity on `(y_i − ε, y_i + ε)` for every `i`. Choose dyadic
`c_i < y_i < d_i` in these neighbourhoods. Cutting `k` at all the `c_i` and
`d_i`, as in Step 6 of the colourings proof, writes `k` uniquely as a product
of commuting pieces:

- one piece supported in `[0,c_1]`;
- one piece supported in `[d_i, c_{i+1}]` for each `i`;
- one piece supported in `[d_n,1]`.

So `∩_i G_{y_i} = A_{y_1} × C_{y_1,y_2} × … × B_{y_n}`, an internal direct
product. Each factor acts only on its own coordinate:

- `A_{y_1}` acts trivially on `M_{y_i,y_{i+1}}` because `A_{y_1} ≤ A_{y_i}`,
  and on `R_{y_n}` because `A_{y_1} ≤ A_{y_n}`;
- `C_{y_i,y_{i+1}}` lies in `B_{y_j}` for `j ≤ i` and in `A_{y_j}` for
  `j ≥ i+1`. If `c` lies in a group `X`, then `X cω_1 = Xω_1`. So `c` fixes
  every coordinate other than the `M_{y_i,y_{i+1}}` coordinate. It permutes
  the classes `A_{y_i}B_{y_{i+1}}ω_1`, because it commutes with `A_{y_i}` and
  with `B_{y_{i+1}}` (the supports are disjoint);
- `B_{y_n}` is the mirror of `A_{y_1}`.

`A_{y_1}` is transitive on `L_{y_1}`, since `G_{y_1}` is transitive on
`Ω ≅ L_{y_1} × R_{y_1}` and `B_{y_1}` acts trivially on `L_{y_1}`. By the
mirror argument `B_{y_n}` is transitive on `R_{y_n}`.

**Step 3 (item 3).** Keep `y_1 < … < y_n` good and irrational. Put
`I_0 = [0,y_1)`, `I_i = (y_i,y_{i+1})` for `1 ≤ i ≤ n-1`, and `I_n = (y_n,1]`.
These intervals are pairwise disjoint. By Step 0, every disagreement set lies
in their union. Index the coordinates of item 2 by `0, …, n` in order.

- *One coordinate.* Let `β, β'` differ only in coordinate `i`. Then
  `D(β,β') ⊆ I_i`.
  - For `i ≥ 1`, `β` and `β'` have the same `L_{y_i}` coordinate, because by
    Step 2 `L_{y_i} ≅ L_{y_1} × M_{y_1,y_2} × … × M_{y_{i-1},y_i}`. So
    `β' ∈ B_{y_i}β`, and `D(β,β') ⊆ (y_i,1]` by item 1.
  - For `i ≤ n-1`, the two points likewise have the same `R_{y_{i+1}}`
    coordinate, so `D(β,β') ⊆ [0,y_{i+1})`.
  - In all cases `D(β,β') ⊆ I_i`.
- *Walk.* Given `ω_1, ω_2`, let `β_{-1} = ω_1`. For `j = 0, …, n` let `β_j`
  have coordinates `0, …, j` equal to those of `ω_2` and the remaining ones
  equal to those of `ω_1`. So `β_n = ω_2`, and `β_{j-1}, β_j` differ at most
  in coordinate `j`. Put `P_j = D(β_{j-1},β_j) ⊆ I_j`.
- *Additivity.* We show `D(ω_1,ω_2) ∩ I_j = P_j` for each `j`.
  - Applying (T) repeatedly gives `D(ω_1,ω_2) ⊆ ∪_k P_k`. Intersecting with
    `I_j` leaves `P_j`.
  - Conversely, (T) gives
    `P_j ⊆ D(β_{j-1},ω_1) ∪ D(ω_1,ω_2) ∪ D(ω_2,β_j)`.
  - The pair `β_{j-1}, ω_1` differs only in coordinates `< j`, so by the walk
    and (T) its disagreement set lies in `∪_{k<j} I_k`. Likewise
    `D(ω_2,β_j) ⊆ ∪_{k>j} I_k`. Intersecting with `I_j` gives
    `P_j ⊆ D(ω_1,ω_2)`.
  - So `D(ω_1,ω_2) = ⊔_j P_j`.
- *Locality.* Let `(β,β')` and `(γ,γ')` both differ only in coordinate `j`,
  with the same pair of `j`-th coordinates. Then `β, γ` differ only outside
  coordinate `j`, and so do `β', γ'`. Their disagreement sets therefore lie in
  `∪_{k≠j} I_k`, which is disjoint from `I_j`.
  - By (T), `D(β,β') ⊆ D(β,γ) ∪ D(γ,γ') ∪ D(γ',β')`. Intersecting with `I_j`
    gives `D(β,β') ⊆ D(γ,γ')`, and by symmetry the two sets are equal.
  - So `P_j` depends only on the two `j`-th coordinates. By (SS1) it is empty
    iff `β_{j-1} = β_j`, that is, iff those coordinates agree.

**Step 4 (item 4).** Assume case (A). Let `O` be a good irrational orbit and
`y ∈ O`. By (C5A), `H` is transitive on `O`. Write `ω = (l_0, r_0)` in the
coordinates of (C6) at `y`.

- *Stabilizers of coordinates.* Let `a' ∈ A_y`. It acts only on `L_y`, so
  `a'ω = (a'l_0, r_0)`, and by injectivity `a'` fixes `l_0` iff `a' ∈ H`. So
  `Stab_{A_y}(l_0) = H ∩ A_y`. Likewise `Stab_{B_y}(r_0) = H ∩ B_y`.
- *Orbits of `G_y` on `Ω × Ω`.* `G_y = A_y × B_y` acts on
  `Ω × Ω ≅ (L_y × L_y) × (R_y × R_y)` factor by factor, so its orbits are the
  products of `A_y`-orbits on `L_y × L_y` with `B_y`-orbits on `R_y × R_y`.
  - `A_y` is transitive on `L_y` (Step 2 with `n = 1`). By (OC) its orbits on
    `L_y × L_y` correspond to the `(H ∩ A_y)`-orbits on `L_y`: the diagonal,
    plus `a` off-diagonal orbits.
  - Likewise `B_y` has `1 + b` orbits on `R_y × R_y`.
  - So `G_y` has `(1+a)(1+b)` orbits on `Ω × Ω`. Split them by type
    (same `L` or not, same `R` or not): the type (same, same) has 1 orbit,
    (same, different) has `b`, (different, same) has `a`, and
    (different, different) has `ab`.
- *Counting the other way.* `F` is transitive on `O` with stabilizer
  `F_y = G_y` (C1). By (OC), the `F`-orbits on `Ω × Ω × O` correspond to the
  `G_y`-orbits on `Ω × Ω`. For each `z ∈ O` the type of `(ω_1,ω_2)` at `z` is
  preserved by `F`, because `f` carries `A_z`, `B_z` to `A_{fz}`, `B_{fz}`.
  So the four types give four `F`-invariant subsets `T_{**}` of
  `Ω × Ω × O`, with `1`, `b`, `a` and `ab` orbits.
  - By Step 1 at `z`, `(ω,ω',z)` has type (same `L_z`, different `R_z`) iff
    `D(ω,ω') ⊆ (z,1]`. By Step 0, `z ∉ D(ω,ω')`, so this holds iff `z < ξ`.
    Similarly the type (different, same) holds iff `z > η`, and the type
    (different, different) holds iff `ξ < z < η`.
  - `F` is transitive on the off-diagonal of `Ω × Ω`. So by (OC), applied to
    `Q = F` acting on the off-diagonal, the `F`-orbits on
    `T_{=,≠} = {(ω_1,ω_2,z) : ω_1 ≠ ω_2, same L_z}` correspond to the
    `K`-orbits on `{z ∈ O : z < ξ}`. So `K` has `b` orbits on `O ∩ (0,ξ)`,
    `a` orbits on `O ∩ (η,1)` and `ab` orbits on `O ∩ (ξ,η)`.
  - The type (same, same) is the diagonal, and it carries one `F`-orbit
    because `H` is transitive on `O`. So `F` has `(1+a)(1+b)` orbits on
    `Ω × Ω × O`.
- *Independence of `y`.* `a` is the number of `F`-orbits on the
  `F`-invariant set `T_{≠,=} ⊆ Ω × Ω × O`, which does not mention `y`. The
  same holds for `b`.
- *`O ∩ D(ω,ω') = ∅`.* This is Step 0.
- *`a, b ≥ 1`.* By (DI) some `g ∈ F` maps `[0, η]` into `[0, y)`: take dyadic
  `d ∈ (η,1)` and `d' ∈ (0,y)`, and glue a PL map `[0,d] → [0,d']` to one
  from `[d,1]` onto `[d',1]`. Then `D(gω,gω') = gD(ω,ω') ⊆ [0,y)`. By Step 1,
  `gω'` and `gω` are distinct points with the same `R_y` coordinate, so
  `|L_y| ≥ 2` and `a ≥ 1`. The mirror argument gives `b ≥ 1`.

**Step 5 (item 5).** Assume case (A), with `O` as in Step 4. Write `O^{<n}`
for the set of increasing `n`-tuples of `O`. Every point of `O` is good and
irrational (by (C5A) the good points are `F`-invariant).

- *`F` is transitive on `O^{<n}`.* Induct on `n`. The case `n = 1` holds
  because `O` is an orbit. Let `ȳ, ȳ' ∈ O^{<n}`. By induction we may assume
  `y_i = y'_i` for `i < n`.
  - Since `y_n, y'_n ∈ O`, some `g ∈ F` has `gy_n = y'_n`. The point `y_n` is
    irrational, so it is not a breakpoint of `g`, and `g` agrees near `y_n`
    with an affine map `φ(x) = 2^s x + δ`, `δ` dyadic.
  - Choose a dyadic `d` with `y_{n-1} < d < min(y_n, y'_n)`, and dyadic
    `d < p < y_n < q` close enough to `y_n` that `φ` maps `[p,q]` into `(d,1)`.
  - By (DI) there is `k ∈ F` that is the identity on `[0,d]` and equals `φ`
    on `[p,q]`, with PL pieces `[d,p] → [d,φ(p)]` and `[q,1] → [φ(q),1]`.
  - Then `k` fixes `y_1, …, y_{n-1}` and `ky_n = y'_n`.
- *Count.* By (OC), the `H`-orbits on `O^{<n}` correspond to the
  `F_ȳ`-orbits on `Ω`, where `F_ȳ = ∩_i F_{y_i}`. (Both correspond to the
  `F`-orbits on `Ω × O^{<n}`.) By item 2, `F_ȳ` acts factor by factor and is
  transitive on the two end factors. So the number of `F_ȳ`-orbits on `Ω`
  is `∏_i m(y_i,y_{i+1})`, where `m(y,z)` is the number of
  `C_{y,z}`-orbits on `M_{y,z}`. For `n = 2` the same count gives
  `m(y,z) = #H\O^{<2} = m`, for every `y < z` in `O`. So `H` has `m^{n-1}`
  orbits on `O^{<n}`.
- *`m` via `B_y`.* `H` is transitive on `O`. So by (OC) the `H`-orbits on
  `O^{<2}` correspond to the `(H ∩ F_y)`-orbits on `O ∩ (y,1)`, for any
  `y ∈ O`. By (C6), `H ∩ F_y = (H ∩ A_y) × (H ∩ B_y)`, and `H ∩ A_y` fixes
  `(y,1)` pointwise. So `m` is the number of `(H ∩ B_y)`-orbits on
  `O ∩ (y,1)`. The mirror argument gives the same `m` for `(H ∩ A_z)` on
  `O ∩ (0,z)`.
- *`m = 1`.* By the count, `m = 1` iff `F_y ∩ F_z = G_y ∩ G_z` is transitive
  on `Ω`, for any `y < z` in `O`.

**Step 6 (item 6).**

- Let `y > η` be irrational. Then `D(ω,ω') ⊆ [0,y)`, so `ω' = a'ω` with
  `a' ∈ A_y` by Step 1. Every `h ∈ H ∩ B_y` commutes with `a'`, so
  `hω' = a'hω = a'ω = ω'`. Hence `H ∩ B_y ≤ K`. The case `y < ξ` is the
  mirror image.
- Let `y < z` be good irrational points in one gap of `D(ω,ω')`. Then
  `D(ω,ω') ∩ (y,z) = ∅`, so by item 3 (with cuts `y < z`) `ω` and `ω'` have
  the same `M_{y,z}` coordinate `m_0`.
  - An element `h ∈ H ∩ C_{y,z}` acts only on that coordinate (item 2) and
    fixes `ω`, so it fixes `m_0`.
  - Hence `h` fixes `ω'`, and `H ∩ C_{y,z} ≤ K`.
  - In case (A) the good points are comeager, so every gap contains such
    points.

**Step 7 (item 7).** Assume case (A) and `m = 1`.

- Let `z_1, z_2 ∈ O ∩ (η,1)`. Since `O` is dense, pick `y ∈ O` with
  `η < y < min(z_1,z_2)`.
- By Step 5 (with `m = 1`), `H ∩ B_y` is transitive on `O ∩ (y,1)`. By
  Step 6 it lies in `K`, so `z_1, z_2` lie in one `K`-orbit. Hence `a = 1`.
- The mirror argument gives `b = 1`, so `ab = 1`, and item 4 gives exactly
  three `K`-orbits on `O`.
- `K` preserves `D(ω,ω')`, so it permutes its gaps. Each gap is open and
  meets the dense set `O`, so transitivity on `O ∩ (ξ,η)` makes `K`
  transitive on the gaps.
- `m^{n-1} = 1` gives transitivity of `H` on `O^{<n}`.

If `m ≥ 2`, then `m^{n-1} ≥ 2^{n-1}` (with cardinal arithmetic if `m` is
infinite). The two cases are exclusive and cover case (A).

**Step 8 (item 8, calibration).** Write `C = {Σ_{k≥1} d_k 4^{-k} : d_k ∈ {0,1}}`.
These are exactly the points whose binary digits in odd places are `0`. Put
`E = 1/2 + C/4`.

- *Cylinders.* For a word `w ∈ {0,1}^j` put `t_w = 1/2 + Σ_k w_k 4^{-k-1}`, a
  dyadic number, and `E_w = t_w + 4^{-j}(E − 1/2)`. Its hull is
  `[t_w, t_w + 4^{-j-1}/3]`. Then `E_w = E_{w0} ⊔ E_{w1}`, and the hull of
  `E_{w0}` ends at `t_w + 4^{-j-2}/3 < t_w + 4^{-j-2} = t_{w1}`. So between
  consecutive cylinders there is an open gap.
- *Shape.* `E` is compact, perfect and totally disconnected, with infinitely
  many components (all points) and extreme points `1/2` and
  `1/2 + 1/12 = 7/12`. So it is a Cantor set.
- *Self-similarity.* Let `U ⊆ E` be nonempty and relatively clopen. By
  compactness `U` is a finite disjoint union of cylinders
  `U_1 < … < U_N`. Splitting the last cylinder repeatedly writes `E` as
  `V_1 < … < V_N`, also a disjoint union of cylinders.
  - Let `α_i` be the affine map carrying `V_i` onto `U_i`. Its slope is a
    power of `4` and its constants are dyadic.
  - Choose dyadic `p_i < min V_i` and `q_i > max V_i` so close to the hull of
    `V_i` that the intervals `[p_i,q_i]` lie in `(0,1)`, are disjoint and
    increasing, and so are their images `α_i[p_i,q_i]`. This is possible
    because the hulls of the `U_i` (and of the `V_i`) are disjoint closed
    intervals in `(0,1)`.
  - Let `g` be `α_i` on `[p_i,q_i]`. Fill `[0,p_1]`, `[q_i,p_{i+1}]` and
    `[q_N,1]` with PL maps from (DI) onto the corresponding image intervals.
  - Then `g ∈ F` and `gE = ⊔ α_i(V_i) = U`.
- *The element `s`.* Map `E_{00} → E_0` by `x ↦ 4x − 3/2`, `E_{01} → E_{10}`
  by a dyadic translation, and `E_1 → E_{11}` by `x ↦ x/4 + 7/16`. Extend as
  in the previous bullet; the first map may be used on `[7/16, q_1]`, a
  neighbourhood of `1/2`.
  - The resulting `s ∈ F` has `sE = E`.
  - It fixes `1/2` and is affine there with slope `4`.
  - It fixes `7/12` (since `7/12 = 7/48 + 7/16`) and is affine there with
    slope `1/4`.
- These are exactly the properties listed in item 8, and none of them
  refers to `Ω`.

**Consequence for the class kill.** Suppose an argument derives "not Cantor"
using only the following as input:

- the set-level conclusions of items 2 and 4–7 of the self-similar claim;
- items 1–3 of the hull-endpoints claim for one element preserving `D_0`.

Then the argument would also show that `E` is not a Cantor set, which is
false. So any proof of the not-Cantor claim must use the action on `Ω`, for
example through items 1–7 here, or through the two-of-three rule for three
distinct points. This completes the proof of the target.
