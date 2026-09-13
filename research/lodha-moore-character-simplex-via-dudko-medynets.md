---
rg: 2
id: lodha-moore-character-simplex-via-dudko-medynets
kind: route
title: Transport the dyadic compressibility lemma to G_0' on the real line, then apply both Dudko--Medynets character theorems
target: lodha-moore-group-character-simplex
requires:
  - thompson-f-is-a-subgroup-of-lodha-moore-group
  - lodha-moore-commutator-simple-abelianization-z3
  - dudko-medynets-compressible-action-character-theorems
---

Notation: `G_0 = <a, b, c>` acts on `R` (Lodha--Moore, arXiv:1308.4250,
`vN_fp.tex` l.106--127).  `F = <x_s> <= G_0`
(`thompson-f-is-a-subgroup-of-lodha-moore-group`).  DM refers to
`dudko-medynets-compressible-action-character-theorems`, BLR to
`lodha-moore-commutator-simple-abelianization-z3`.

## Step 0. A topological conjugacy `h : (0,1) -> R` for the action of `F`

**0a. Binary coordinates.**  Let `beta : 2^N -> [0,1]`, `beta(xi) = sum_i xi_i 2^-i`.
- An element `f` of `F` acts on `2^N` by finitely many prefix replacements
  `s_i xi -> t_i xi`, where `{s_i}` and `{t_i}` are maximal antichains
  (Lodha--Moore l.205--213).
- On the standard dyadic interval `[beta(s_i 0^∞), beta(s_i 0^∞) + 2^-|s_i|]`, the
  map `beta f beta^-1` is affine, with slope `2^(|s_i| - |t_i|)`, onto the
  standard dyadic interval of `t_i`.
- So `f_beta := beta f beta^-1` is a well-defined homeomorphism of `[0,1]`.  It is
  piecewise linear, with dyadic breakpoints and slopes powers of 2, so it lies in
  `F_(2,1)`.
- **Converse.** Take `g in F_(2,1)` with breakpoints `0 = x_0 < ... < x_k = 1`.
  Subdivide each `[x_(j-1), x_j]` into standard dyadic intervals.  `g` is affine
  on each piece, with slope a power of 2 and dyadic endpoints.  Halving a piece
  `r` times halves its image `r` times.  For `r` large, every image piece has
  length `2^-m` and a left endpoint of denominator at most `2^m`, so it is a
  standard dyadic interval.  The resulting pairs of standard dyadic intervals
  define a prefix replacement `f` with `f_beta = g`.
- Hence `f -> f_beta` is an isomorphism `F -> F_(2,1)`, and it maps `F'` onto
  `F_(2,1)'`.

**0b. The continued fraction map.**  Lodha--Moore l.248--264 define
`Phi : 2^N -> R ∪ {∞}` from
`phi(0 xi) = 1/(1 + 1/phi(xi))` and `phi(1 xi) = 1 + phi(xi)`.
- In projective coordinates, `phi(s xi) = M_s . phi(xi)`, with `M_s` a product of
  `[[1,0],[1,1]]` and `[[1,1],[0,1]]`.
- **Continuity.** `phi([s])` lies in the interval `M_s([0,∞])` between two
  consecutive Farey fractions `p/q` and `p'/q'`.
  - If `xi` is not eventually constant, both denominators of `M_s` along its
    prefixes tend to infinity, so these intervals shrink to a point.
  - If `xi` is eventually constant, the intervals shrink to the rational point
    `phi(xi)`, or to `∞` in the chordal metric.
  So `phi`, and with it `Phi`, is continuous.
- **Surjectivity.** The image is compact and contains every `M_s(0)` and `M_s(∞)`,
  a dense set, so `Phi` is onto `R ∪ {∞}`.
- **Identifications** (l.261--264, verbatim): "This function is one-to-one except
  at $\xi$ which are eventually constant ... On sequences which are eventually
  constant, the map is two-to-one: $\Phi(s \seq{0 \bar 1}) = \Phi(s \seq{1 \bar 0})$
  and $\Phi(\seq{\bar 0}) = \Phi(\seq{\bar 1}) = \infty$."

**0c. The conjugacy.**  Set `h := Phi beta^-1` on `(0,1)`.
- `beta` identifies exactly the pairs `s01̄ ~ s10̄`, which `Phi` also identifies,
  so `h` is well defined.
- `h` is continuous: `[0,1]` carries the quotient topology of the compact map
  `beta`.
- `h` is injective on `(0,1)`: the only extra identification of `Phi` is
  `0̄ ~ 1̄`, lying over the endpoints `0` and `1`.
- `h` is onto `R`, since `Phi` is onto and `Phi^-1(∞) = {0̄, 1̄}`.
- A continuous bijection from `(0,1)` onto `R` is strictly monotone, hence a
  homeomorphism.
- **Conjugation.** Lodha--Moore l.268--271 say that conjugation by `Phi` carries
  `a, b` to the standard generators of `F` on `2^N`.  Composing, the action of
  each `f in F` on `R` equals `h f_beta h^-1`.

## Step 1. `G_0'` acts compressibly on `R`, so it has no proper characters

Take the base `U = { h((p,q)) : 0 < p < q < 1 dyadic }` of the topology of `R`.
- **(i)** By BLR item 4, each `g in G_0'` has compact support `K ⊂ R`.  Since
  `h^-1(K)` is compact in `(0,1)`, it lies in some dyadic `(p,q)`, and
  `K ⊂ h((p,q))`.
- **(iv)** holds for intervals.
- **(ii) and (iii).** DM item 4 supplies witnesses in `F_(2,1)' = (F^0_(2,1))'`
  for the dyadic base on `(0,1)`.  Their conjugates by `h` lie in
  `F' <= [G_0, G_0] = G_0'` (Step 0).  A homeomorphism carries images, supports,
  closures and disjointness across, so they witness (ii) and (iii) for `U`.
- `R` is an infinite regular Hausdorff space.  `G_0'` is countable and simple
  (BLR item 1).  So by DM item 2, `G_0'` has no proper characters.  This is item 1
  of the claim.

## Step 2. The extension theorem with `R = G_0'`

**ICC.**  `G_0'` contains `F'`, so it is infinite.  If `e != u in G_0'` had finite
conjugacy class, its centralizer would have finite index, and the normal core of
that centralizer would be a finite-index normal subgroup of the simple group
`G_0'`, hence all of `G_0'`.  So `u` would be central, and the centre of a
nonabelian simple group is trivial.  So `G_0'` is ICC.

**Condition (ii).**  Let `g in G_0 \ {e}`.
1. Pick `x in R` with `g(x) != x`, and a basic interval `J = h((p,q)) ∋ x` with
   `g(J) ∩ J = ∅`.
2. `G_0'` has infinitely many distinct elements supported in `J`.
   - Take `e != k in F_(2,1)'` and `U_1` in the dyadic base containing
     `supp(k)` (DM (i)).
   - By DM (ii), some `u` in `F_(2,1)'` has `u(U_1) ⊆ (p,q)`.  The powers of the
     conjugate `u k u^-1` are supported in `(p,q)` and pairwise distinct, since
     `F` is torsion-free.
   - Conjugate these by `h`.
3. Let `r_1, r_2, ...` be distinct elements of `G_0'` supported in `J`, and set
   `g_n = r_n g r_n^-1 in C_R(g)`.
4. **Distinct.** If `g_n = g_m` with `n != m`, then `k = r_m^-1 r_n != e`
   commutes with `g`.  But `k` is supported in `J`, and `g k g^-1` is supported in
   `g(J)`, which is disjoint from `J`.  So `k = e`, a contradiction.
5. **In `R`.** Put `v = r_n^-1 r_m`.  Then `g_n^-1 g_m = r_n (g^-1 v g v^-1) r_n^-1`,
   a conjugate of a commutator, so it lies in `G_0'`.

**Conclusion.**  By DM item 3, every finite type factor representation of `G_0` is
regular, or factors through `G_0/N(G_0') = G_0/G_0' ≅ Z^3` (BLR item 3).
- Finite factor representations of abelian groups are scalar (DM, l.317).
- Indecomposable characters correspond to finite type factor representations
  (DM, l.114--115).
- So the indecomposable characters of `G_0` are the regular character and the
  characters `rho o pi`.  This is item 2.
- Every character is a barycentre of indecomposable ones (Choquet), which gives
  `t tau_reg + (1-t) chi_ab`.  On `G_0' \ {e}`, `tau_reg = 0` and `chi_ab = 1`,
  so the value is `1 - t`.  This is item 3. ∎
