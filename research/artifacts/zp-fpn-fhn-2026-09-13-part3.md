# FP_n versus FH_n (Zaremsky Problem 1.4), part 3: isolated singular vertices and Leary's cofinite family

Lane z1-04-fp-fh, 2026-09-13. Conventions and Lemma S: part 1. Status: unreviewed.

## 9. Proposition V: isolated vertex stabilizers of type F_n

**Proposition V.** Let `n ≥ 2`. Suppose `G` acts cellularly, with finitely
many orbits of cells, on an `(n−1)`-acyclic CW complex `X`. Suppose `V` is a
`G`-invariant set of vertices such that:

1. every cell not in `V` has trivial stabilizer;
2. the vertices `v ∈ V` have pairwise disjoint closed subcomplex
   neighbourhoods `N_v` with `gN_v = N_{gv}`;
3. `N_v` is `G_v`-equivariantly and cellularly the cone (cone point `v`) on a
   free `G_v`-CW complex `Lk_v` with finitely many orbits of cells;
4. every `G_v` is finitely presented and of type `FP_n`.

Then `G` acts freely, with finitely many orbits of cells, on an
`(n−1)`-acyclic CW complex.

*Step 1: an `(n−1)`-connected free cocompact `H`-complex `E ⊇ Lk_v`*, where
`H = G_v`.
- (a) Connect. `Lk_v` has finitely many `H`-orbits of cells, hence finitely
  many orbits of components. Choose a base vertex `x_0`, a finite generating
  set `s_1, …, s_r` of `H`, and vertices `y_1, …, y_q` representing the orbits
  of components. Attach the `H`-orbits of 1-cells `x_0 — s_i x_0` and
  `x_0 — y_j`. The result `Z_1` is connected: `h y_j` is joined to `h x_0`,
  and `h x_0` is joined to `x_0` along a word in the `s_i`. The action stays
  free.
- (b) Simply connect. `Z_1 → Z_1/H` is a regular covering with deck group
  `H`, and `Z_1/H` is finite. So `1 → π_1(Z_1) → π_1(Z_1/H) → H → 1` with
  `π_1(Z_1/H)` finitely presented. A surjection from a finitely generated
  group onto a finitely presented group has finitely normally generated
  kernel. Attach the `H`-orbits of 2-cells along lifts of finitely many
  normal generators. Then `π_1(Z_2/H) → H` is an isomorphism, so `Z_2` is
  simply connected.
- (c) Kill homology. For `k = 2, …, n−1`, suppose `Z_k` is `(k−1)`-connected,
  free and cocompact. Its cellular chain complex is exact at degrees
  `1, …, k−1` and at `ℤ`, with finitely generated free terms. By Lemma S
  (using `FP_n`, and `k+1 ≤ n`), the cycles in degree `k` form a finitely
  generated module, so `H_k(Z_k)` is finitely generated. By Hurewicz
  (`k ≥ 2`, `(k−1)`-connected), every class is spherical. Attaching
  finitely many orbits of `(k+1)`-cells along representing spheres gives
  `Z_{k+1}`, which is `k`-connected.
- Put `E = Z_n`. It is `(n−1)`-connected, free, cocompact, and contains `Lk_v`.

*Step 2: replacement.* Choose representatives `v_1, …, v_p` of the orbits in
`V` (finitely many, by cocompactness) and complexes `E_{v_j}` as in Step 1.
Let `A = X ∖ ⋃_v int N_v`, a subcomplex, and

`Y = A ∪ ⊔_j G ×_{G_{v_j}} Cyl(Lk_{v_j} ↪ E_{v_j})`,

glued along `G ×_{G_{v_j}} Lk_{v_j} = ⊔_{v ∈ Gv_j} Lk_v ⊆ A`. `Y` is a
`G`-CW complex with finitely many orbits of cells, and it is free: cells of
`A` have trivial stabilizers, and `G_{v_j}` acts freely on the cylinder.

*Step 3: homology.* `X = A ∪ ⊔ N_v` and `Y = A ∪ ⊔ M_v`, both glued along
`⊔ Lk_v`. Compare the two Mayer–Vietoris sequences. On the pieces,
`H_k(N_v) = H_k(pt) → H_k(M_v) ≅ H_k(E_v)` is an isomorphism for `k ≤ n−1`,
and the identity on `A` and on `⊔ Lk_v`. The five lemma gives
`H_k(X) ≅ H_k(Y)` for `k ≤ n−1`. So `Y` is `(n−1)`-acyclic. ∎

## 10. Theorem L: Leary's groups with cofinite S are FH_n

Setting (Leary, arXiv:1512.06609; quotes in the citation node
`leary-gls-cocompact-slabs-with-isolated-stabilizers`). `L` is a finite
connected flag complex, `S ⊆ ℤ`, and `G = G_L(S)` acts cellularly on the
contractible cube complex `X = X_L^{(S)}` with a `G`-invariant Morse (height)
function `f`.
- (F2) `G` acts cocompactly on each slab `X(m) = f^{-1}([−m−1/2, m+1/2])`.
- (F3) The action is free except that each vertex of height not in `S` has
  stabilizer isomorphic to `π_1(L)`.
- (F4) The closed `1/4`-ball around such a vertex `v` is `G_v`-equivariantly
  `M(𝕊(L̃) → ∗)`, the cone on `𝕊(L̃)`, with `G_v` acting freely with quotient
  `𝕊(L)`.
- (F5) The Bestvina–Brady Morse lemma: enlarging a slab cones off descending
  links at new top vertices and ascending links at new bottom vertices.
- (F6) Vertices of height in `S` are unbranched, with ascending and
  descending links `L`.

**Theorem L.** Let `n ≥ 2`, let `L` be `(n−1)`-acyclic with `π_1(L)` of type
`FP_n`, and let `ℤ − S` be finite. Then `G_L(S)` is of type `FH_n`.

*Proof.*
1. Pick `m ≥ max{ |h| : h ∈ ℤ − S }`. For `m' > m`, all new vertices of
   `X(m')` have heights in `S`. By (F5) and (F6), `X(m')` is obtained up to
   homotopy from `X(m)` by coning off copies of `L`. Hence
   `H_i(X(m'), X(m)) ≅ ⊕ H̃_{i−1}(L) = 0` for `i ≤ n`, and
   `H_i(X(m)) ≅ H_i(X(m'))` for `i ≤ n−1`.
2. `X = ⋃_{m'} X(m')` is contractible and homology commutes with increasing
   unions. So `H̃_i(X(m)) = 0` for `i ≤ n−1`.
3. `X(m)` is cocompact by (F2). All singular vertices (heights in `ℤ − S`)
   lie in the open slab and have cone neighbourhoods as in (F4). Their
   stabilizers `≅ π_1(L)` are finitely presented, since `L` is finite, and of
   type `FP_n`. After a cubical subdivision making the balls and slab
   boundaries subcomplexes, Proposition V applies. ∎

**Consequence for Problem 1.4.** Assume `π_1(L)` is of type `FP_n`. Leary's
Corollary on type `FP_n` gives the following, and in every case `FP_n` implies
`FH_n`:
- `S` finite: `G_L(S)` is `FP_n` iff `L̃` is `(n−1)`-acyclic, and then it is
  `FH_n` (Leary's proposition for finite `S`).
- `S` and `ℤ − S` both infinite: `FP_n` for all `S` is equivalent to `FH_n`
  for all `S` (Leary's Theorem B).
- `ℤ − S` finite: `G_L(S)` is `FP_n` iff `L` is `(n−1)`-acyclic, and then it
  is `FH_n` by Theorem L.

So Leary's family, the natural candidate source, cannot answer Problem 1.4
negatively over `ℤ`.

Leary's own open remark ("we do not know whether `G_L(S)` is necessarily
`FH(R)`" for `ℤ − S` finite) concerns `FH` in all degrees, and Theorem L does
not settle it. Step 1 yields an `(n−1)`-connected `E_v`, not a finite
acyclic one; that would need `π_1(L)` of type `FH` together with an
equivariant map from `𝕊(L̃)`, as Leary notes.

## 11. Where this leaves Problem 1.4

- Yes-side evidence. Two families come with cocompact actions on
  `(n−1)`-acyclic complexes that are either free or have isolated type-`F_n`
  vertex stabilizers: Bestvina–Brady kernels (level sets) and Leary's
  `G_L(S)` (slabs, via Proposition V). So those `FP_n` groups are `FH_n`.
  Brown–Leary's small-cancellation groups `G(S)` are stated in
  arXiv:2004.04550 to be of type `FH`. This lane has not checked other
  families.
- No-side: a separating group must be of type `FP_3` with no finitely
  presented cover with superperfect kernel (Theorem D). Such a group cannot
  come from these constructions. It would need an `FP_3` group built by
  purely algebraic means, e.g. by realizing a module-theoretic invariant, with
  a proof that every finitely presented `Q ↠ G` with perfect kernel has
  `H_2(ker) ≠ 0`.
