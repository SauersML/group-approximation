# Clique complexes of level sets in CAT(0) cube complexes

Lane z4-04-fn-rips, 2026-09-13. Toward Zaremsky Problem 4.4
(`zaremsky-4-04-type-fn-groups-have-connected-rips-complex`). Unreviewed.

## Setting

- `X`: a locally finite, finite-dimensional CAT(0) cube complex; its 1-skeleton
  is a median graph and `d` is its path metric on `X^(0)`.
- `h: X → R`: affine on each cube, integer-valued on vertices, with
  `|h(u) − h(v)| <= 1` for adjacent vertices `u, v`.
- `L := h^{-1}(0)`, `V_0 := L ∩ X^(0)`.
- `Θ`: the graph on `V_0` with `u ~ v` iff `u ≠ v` lie in a common cube.
- `K`: the simplicial complex on `V_0` whose simplices are the nonempty finite
  subsets of `V_0` contained in some cube.

## Theorem A

1. `K = Flag(Θ)`.
2. `|K| ≃ L`.
3. Let a group `N` act on `X` by cubical automorphisms with `h ∘ g = h` for all
   `g ∈ N`, freely and transitively on `V_0`. Fix `v_0 ∈ V_0` and put
   `T := {g ∈ N \ {1} : v_0` and `g v_0` lie in a common cube`}`. Then `T` is
   finite and symmetric, and `Flag(Cay(N,T)) ≅ K ≃ L`. If `L` is connected,
   `T` generates `N` and `Flag(Cay(N,T)) = R_1(N,T)` is a Rips complex of `N`.
   In particular, if `L` is (n−1)-connected then `N` has an (n−1)-connected
   Rips complex.

**Credit.** The case `h ≡ 0` with `N` vertex-transitive on `X` (e.g. a RAAG
on its Salvetti universal cover, `T` = products over cliques) is known:
Chalopin–Chepoi–Genevois–Hirai–Osajda, *Helly groups*, Theorem 4.1 and Lemma
5.20, as cited in Hulbert–Zaremsky arXiv:2608.25614 §1 and Li–Sánchez Saldaña
arXiv:2608.24279 §1 (not re-read here). The Helly property of cubes is
standard median-graph theory. The level-set form with `h ≠ 0` was not found in
Zaremsky arXiv:1812.10976, Hulbert–Zaremsky arXiv:2608.25614 or Li–Sánchez
Saldaña arXiv:2608.24279. That check was bounded to these three papers.

## Standard facts used

Sageev (1995), Chepoi (2000); see e.g. Sageev's PCMI notes.

- (F1) Every hyperplane splits `X^(0)` into two halfspaces. `d(u,v)` is the
  number of hyperplanes separating `u` and `v`. A vertex is determined by the
  set of hyperplanes separating it from a fixed vertex.
- (F2) The intersection of two cubes is empty or a common face.
- (F3) Two distinct hyperplanes either cross (all four quarters meet
  `X^(0)`) or some quarter `H_1^ε ∩ H_2^δ` is empty.
- (F4) The hyperplanes separating two vertices of a cube `Q` are hyperplanes
  of `Q`, dual to edges of `Q` at either vertex, and they pairwise cross.
- (F5) Link condition: the link of a vertex is a flag simplicial complex, so
  edges `e_1, …, e_k` at a vertex that pairwise span squares span a `k`-cube.

## Lemma 1 (slices are spanned by vertices)

For every cube `C`, `C ∩ L = conv(C ∩ V_0)`. In particular `C ∩ L ≠ ∅` iff
`C ∩ V_0 ≠ ∅`.

*Proof.* Identify `C = [0,1]^k`. Then `h(x) = c + Σ_i ε_i x_i` with `c ∈ Z` and
`ε_i = h(e_i) − h(0) ∈ {−1, 0, 1}`. `P := C ∩ L` is a polytope, the intersection
of `C` with the hyperplane `{h = 0}`. Each vertex `p` of `P` is the unique point
of `F ∩ {h = 0}` for some face `F` of `C` of dimension `<= 1`. If `dim F = 0`,
`p` is a vertex of `C`. If `F` is an edge `{u + s e_j : s ∈ [0,1]}`, then
`ε_j ≠ 0` (otherwise `h` is constant on `F`, and `F` either misses
`{h = 0}` or lies in it). The zero `s = −h(u)/ε_j` is an integer in `[0,1]`,
so `p` is a vertex of `C`. So every vertex of `P` is in `C ∩ V_0`, and
`P = conv(C ∩ V_0)`. ∎

## Lemma 2 (pairwise crossing hyperplanes at a vertex span a square)

Let `e_1 = [a,b]` and `e_2 = [a,c]` be edges at `a`, dual to distinct crossing
hyperplanes `H_1, H_2`. Then `e_1, e_2` span a square.

*Proof.* Since `H_1, H_2` cross, choose a vertex `x` on the `b`-side of `H_1`
and the `c`-side of `H_2`, and let `m` be the median of `b, c, x`. The only
hyperplanes separating `b` and `c` are `H_1` and `H_2`, and a median lies on the
majority side of every hyperplane. So `m` agrees with `b` and `c` off
`{H_1, H_2}`. For `H_1`, both `b` and `x` are on the `b`-side, so `m` is too;
for `H_2`, both `c` and `x` are on the `c`-side, so `m` is too. Hence `m`
differs from `b` exactly in `H_2` and from `c` exactly in `H_1`, so `m` is
adjacent to both, and `a, b, m, c` is a 4-cycle. In the cube complex of a
median graph every 4-cycle bounds a square. ∎

## Lemma 3 (Helly property of cubes)

A finite set `A ⊆ X^(0)` whose points pairwise lie in common cubes lies in a
single cube.

*Proof.* Let `𝓗` be the set of hyperplanes separating some pair of points of
`A`, and fix `a ∈ A`.

- Every `H ∈ 𝓗` is dual to an edge at `a`. `H` separates some `c, d ∈ A`, so
  it separates `a` from `c` or from `d`, say from `b ∈ A`. Since `a, b` lie in a
  common cube `Q`, `H` is a hyperplane of `Q` dual to an edge of `Q` at `a`
  (F4).
- The hyperplanes in `𝓗` pairwise cross. Suppose `H_1 ≠ H_2 ∈ 𝓗` do not
  cross. By (F3) some quarter `H_1^ε ∩ H_2^δ` is empty, so
  `H_1^ε ⊆ H_2^{−δ}` and `H_2^δ ⊆ H_1^{−ε}`. As `H_1` separates two points of
  `A`, there is `p ∈ A ∩ H_1^ε`, and similarly `q ∈ A ∩ H_2^δ`. Then
  `p ∈ H_2^{−δ}` and `q ∈ H_1^{−ε}`, so both `H_1` and `H_2` separate `p` from
  `q`. But `p, q` lie in a common cube, so the hyperplanes separating them
  pairwise cross (F4). Contradiction.
- By Lemma 2 the edges at `a` dual to the hyperplanes of `𝓗` pairwise span
  squares, so by (F5) they span a cube `Q_A ∋ a` whose hyperplanes are exactly
  `𝓗`. For `b ∈ A`, the hyperplanes separating `a` and `b` form a subset
  `B ⊆ 𝓗`, and `Q_A` has a vertex separated from `a` by exactly `B`. By (F1)
  that vertex is `b`. So `A ⊆ Q_A`. ∎

## Proof of Theorem A

**(1)** `K ⊆ Flag(Θ)` holds because any two points of a cube lie in that cube.
Conversely a finite clique of `Θ` lies in a cube by Lemma 3.

**(2)** Let `I` be the set of cubes `C` with `C ∩ V_0 ≠ ∅`.

- `L` is a regular CW complex whose cells are the polytopes `F ∩ L` over cubes
  `F`; faces of `F ∩ L` are the sets `F' ∩ L` for faces `F' ⊆ F`. The
  subcomplexes `L_C := C ∩ L`, `C ∈ I`, cover `L`: a point of `L` lies in a
  cube `C` with `C ∩ L ≠ ∅`, and `C ∈ I` by Lemma 1.
- The full simplices `Δ_C := Δ(C ∩ V_0)`, `C ∈ I`, are subcomplexes of `K` and
  cover `K` by definition of `K`.
- For `C_1, …, C_k ∈ I`, the intersection `D = C_1 ∩ … ∩ C_k` is empty or a
  cube (F2, iterated). Then `L_{C_1} ∩ … ∩ L_{C_k} = D ∩ L`, which by Lemma 1
  is `conv(D ∩ V_0)`: convex, hence contractible, when nonempty, and nonempty
  iff `D ∩ V_0 ≠ ∅`. Likewise `Δ_{C_1} ∩ … ∩ Δ_{C_k} = Δ(D ∩ V_0)` is a simplex
  when nonempty, and nonempty iff `D ∩ V_0 ≠ ∅`.
- So both covers are indexed by `I`, have the same nerve, and all their nonempty
  finite intersections are contractible. Both are locally finite, since `X` is.
  The Nerve Theorem for covers of CW complexes by subcomplexes with contractible
  nonempty finite intersections (Borsuk; Weil; McCord; Björner, *Topological
  methods*, Handbook of Combinatorics, §10) gives `L ≃ nerve ≃ |K|`. ∎

**(3)** `N` preserves cubes and `h`, so it preserves `V_0`, `Θ` and `K`. The map
`g ↦ g v_0` is a bijection `N → V_0`, and `g v_0 ~ g' v_0` iff
`v_0 ~ g^{-1} g' v_0` iff `g^{-1} g' ∈ T`. So `Θ ≅ Cay(N,T)` and
`K = Flag(Θ) ≅ Flag(Cay(N,T))` by (1). `T` is finite because `v_0` lies in
finitely many cubes, and symmetric because `v_0, g v_0 ∈ Q` gives
`g^{-1} v_0, v_0 ∈ g^{-1}Q`. If `L` is connected then so is `K`, `T` generates
`N`, and `Flag(Cay(N,T)) = R_1(N,T)` by
`group-rips-complexes-are-cayley-graph-flag-complexes`. ∎

## Corollary B (Bestvina–Brady groups) — pending the Morse-lemma citation

Let `Γ` be a finite simplicial graph with flag complex `Δ_Γ`, `A_Γ` its
right-angled Artin group, and `X_Γ` the universal cover of the Salvetti
complex. `X_Γ` is a CAT(0) cube complex on which `A_Γ` acts freely and
transitively on vertices. Let `φ: A_Γ → Z` send every generator to `1`, let
`h` be its affine extension, and let `BB_Γ = ker φ`.

- `V_0 = BB_Γ`, and `BB_Γ` acts freely and transitively on it, so Theorem A
  applies. Explicitly,
  `T = {∏_{v∈α} v · ∏_{w∈β} w^{-1} : α, β` disjoint subsets of a clique of
  `Γ`, `|α| = |β| >= 1}`.
- `X_{[−1/2, 1/2]} := h^{-1}[−1/2, 1/2] ≃ L`, by the nerve argument of (2) with
  the same index set. A cube with all vertex heights `>= 1` or all `<= −1`
  misses `[−1/2, 1/2]`. A cube with heights on both sides of `0` has a height-0
  vertex, because heights change by at most 1 along edges. Each
  `C ∩ X_{[−1/2,1/2]}` is convex.
- Bestvina–Brady Morse theory: ascending and descending links in `X_Γ` are
  copies of `Δ_Γ`, and the level set `X_{[−1/2,1/2]}` includes into the
  contractible `X_Γ` by an `n`-connected map when `Δ_Γ` is (n−1)-connected.
  Hence `X_{[−1/2,1/2]}` is (n−1)-connected. The level-set Morse lemma needed
  is Bestvina–Brady, Invent. Math. 129 (1997), Corollary 2.6. Hulbert–Zaremsky
  arXiv:2608.25614 cite that numbering before their simplicial Lemma 3.1, a
  sublevel-set form that does not cover level sets. **The statement of BB97
  Corollary 2.6 is to be read in the source before the corollary is landed as
  established.**
- Conclusion: if `Δ_Γ` is (n−1)-connected, equivalently (Bestvina–Brady)
  `BB_Γ` is of type `F_n`, then `R_1(BB_Γ, T)` is (n−1)-connected. Taking `Δ_Γ`
  (n−1)-connected but not n-connected gives groups of type `F_n` not `F_{n+1}`
  with (n−1)-connected Rips complexes; the Bieri–Stallings groups are the case
  `A_Γ = F_2^{n+1}`.
