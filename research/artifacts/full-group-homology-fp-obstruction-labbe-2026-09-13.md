# Homology of derived full groups and finite presentation, part 2: Labbé's shift

Lane `ex-fp-simple-full-group-obstruct`, 2026-09-13. **Unreviewed.** Part 1 is
`research/artifacts/full-group-homology-fp-obstruction-2026-09-13.md`, and the numbering continues from it.

## 0. Outcome

- **Theorem 6.** Let `X ⊆ A^{Z^2}` be a subshift carrying an expansive 2-dimensional morphism
  `ω : X -> X` that is recognizable in `X` and satisfies `X = closure_σ(ω(X))`. Then for every
  finite coefficient ring `R = Z/m`:
  - `|H^2(Z^2; C(X, R))| <= m^{N_{3,3}}`;
  - `|H^1(Z^2; C(X, R))| <= m^{N_{4,3} + N_{3,4}}`.

  Here `N_{a,b}` is the number of `a × b` patterns in the language of `X`. Primitivity is not used.
- **Corollary 7 (Labbé).** Labbé's 19-tile Wang shift `Omega_U` satisfies the hypotheses. So:
  - `H_2(D([[Z^2 ~ Omega_U]]); Z) ≅ Z ⊕ T`, where `T` is a finite abelian 2-group of exponent at
    most 4;
  - `H_j(D([[Omega_U]]); Z)` is finitely generated for every `j`;
  - every conjugation-invariant additive invariant of relations has finitely generated image.
- **Consequence.** No homological or additive-invariant argument can refute
  `labbe-shift-derived-full-group-is-finitely-presented`. The remark in its Attempts, that homology gives no
  obstruction, is now a theorem. It covers all degrees, not only the sequence `H_2(A(G)) -> H_2(G)`.

## 1. Source: Labbé, arXiv:1802.03265

TeX `article1.tex`, on MSI in `/scratch.global/sauer354/fpsz2/src/1802.03265.d/`. Line numbers
refer to that file.

- **Definitions, lines 813–823.** For `X ⊆ A^{*^d}`, a map `ω : X -> B^{*^d}` is a *d-dimensional
  morphism* if `ω(u ⊙^i v) = ω(u) ⊙^i ω(v)` whenever `u ⊙^i v ∈ X`.
  - Line 884: `ω` is *expansive* if for every `a ∈ A` and `K ∈ N` there is `m` with
    `min(shape(ω^m(a))) > K`.
- **Self-similar, lines 1012–1016.** `X` is self-similar if there is an expansive `d`-dimensional
  morphism `ω` with `X = closure_σ(ω(X))`.
- **Recognizability, lines 1134–1143.** A pair `(k, x)` with `y = σ^k ω(x)` is an
  `ω`-representation of `y`. It is *centered* if `0 <= k < shape(ω(x_0))` coordinatewise. "We say
  that `ω` is *recognizable in `X`* if each `y ∈ B^{Z^d}` has at most one centered
  `ω`-representation `(k, x)` with `x ∈ X`."
- **Abstract, line 216.** "We prove the existence of an expansive, primitive and recognizable
  2-dimensional morphism `ω : Omega_U -> Omega_U` that is onto up to a shift."
- **Theorem `thm:main`, line 296.** "The Wang shift `Omega_U` is self-similar, aperiodic and
  minimal."

## 2. Preliminaries on recognizable morphisms

Let `X`, `ω` be as in Theorem 6, with `(σ^v y)(u) = y(u + v)`.

**(P1) Grid.** For `x ∈ X`, all tiles in a row of `x` have images of the same height, and all tiles
in a column have images of the same width. Indeed `ω(u ⊙^1 v)` is defined only when the heights
agree, and `ω(u ⊙^2 v)` only when the widths agree. So `ω(x)` partitions `Z^2` into rectangles
`ω(x_c)`, `c ∈ Z^2`, arranged as a grid.

**(P2) Every point has a centered representation, depending continuously on the point.**
- The set `Gr = {(y, k, x) : y = σ^k ω(x), 0 <= k < shape(ω(x_0))} ⊆ X × Z^2 × X` is closed.
  - `ω` is continuous, since it is a morphism with bounded shapes.
  - The shapes are bounded, so `k` takes finitely many values, and `Gr` is compact.
- Its projection to `y` is shift-invariant: re-center by moving to the tile of `x` whose image
  contains the origin. The projection contains `ω(X)` and is closed, so by self-similarity it
  equals `X`.
- By recognizability the projection is injective. A continuous bijection from a compact space
  to a Hausdorff space is a homeomorphism.
- So `y -> (k(y), x(y))` is continuous.

**(P3) Iterates.** `ω^n` is again an expansive morphism with `X = closure_σ(ω^n(X))`, and it is
recognizable in `X`.
- Take centered `ω^2`-representations `(k, x)` and `(k', x')` of `y`, and put `u = ω(x)`,
  `u' = ω(x')`.
- The origin lies in `ω(u_j)` for a unique tile `j` of the block `ω(x_0)`. With `s_j` the offset
  of `ω(u_j)` in `ω^2(x_0)`, the pair `(k - s_j, σ^j u)` is a centered `ω`-representation of `y`.
  Likewise `(k' - s'_{j'}, σ^{j'} u')`.
- Recognizability gives `σ^j u = σ^{j'} u'` and `k - s_j = k' - s'_{j'}`.
- Now `(j, x)` and `(j', x')` are centered `ω`-representations of that same point. So `x = x'`,
  `j = j'`, `s_j = s'_{j'}` and `k = k'`.
- Induction handles general `n`.

**Notation.**
- For `y ∈ X`, write `(k_n(y), x_n(y))` for its centered `ω^n`-representation.
- The level-`n` supertile of `y` containing a site is `ω^n` of the tile of `x_n(y)` whose image
  contains it. By (P1) the level-`n` supertiles form a grid.
- Its *collar* is the `3 × 3` block of `x_n(y)` around that tile.
- By (P2), `y -> (k_n(y), x_n(y)|_{[-r, r]^2})` is locally constant for each `r`.
- By expansiveness and finiteness of `A`, `s_n := min over a ∈ A of min(shape(ω^n(a))) -> ∞`.

## 3. Proof of Theorem 6

`M = C(X, R)`, `t_i g = g ∘ σ^{e_i}`. The Koszul cochain complex is
`M -δ^0-> M^2 -δ^1-> M`, with `δ^0 g = ((t_1 - 1) g, (t_2 - 1) g)` and
`δ^1 (a, b) = (t_1 - 1) b - (t_2 - 1) a`. Its cohomology is `H^*(Z^2; M)`.

**Geometric reading.**
- For `y ∈ X`, a 0-cochain `g` assigns `g(σ^p y)` to the vertex `p` of the unit grid.
- A 1-cochain `(a, b)` assigns `a(σ^p y)` to the edge `p -> p + e_1`, and `b(σ^p y)` to the edge
  `p -> p + e_2`.
- `δ^0` is the difference along edges, and `δ^1` the circulation around the square at `p`.

**Assignment convention.** A vertex `p` belongs to the supertile containing the unit square with
lower-left corner `p`. So the vertices of a supertile `S` with corner `c` and shape `(w, h)` form
the rectangle `V(S) = c + [0, w-1] × [0, h-1]`.

### 3.1 Degree 2

- `H^2 = M / ((t_1 - 1) M + (t_2 - 1) M)`, the coinvariants.
- Let `g ∈ M` depend only on `y|_{[-ρ, ρ]^2}`. Choose `n` with `s_n > ρ + 1`.
- Then `[-ρ, ρ]^2` lies in the union of the supertile containing the origin and its eight
  neighbours. So `g(y)` is a function of `(τ, q)`, where `τ = x_n(y)|_{[-1,1]^2}` and `q = k_n(y)`.
  Hence `g = Σ_{τ,q} g_{τ,q} 1_{[τ, q]}`.
- Moreover `1_{[τ, q]} = 1_{[τ, 0]} ∘ σ^{-q}`: the point `σ^{-q} y` has its origin at the corner
  of the same supertile. So `[1_{[τ,q]}] = [1_{[τ,0]}]` in the coinvariants.
- So the classes `[1_{[τ,0]}]`, with `τ` ranging over `3 × 3` patterns of `x_n(y)`, span the
  image of every `g` of radius `ρ`.
- Since `x_n(y) ∈ X`, there are at most `N_{3,3}` such `τ`, whatever `n` is.
- Any finite set of classes has representatives of a common radius. So `H^2` is generated by at
  most `N_{3,3}` elements, and `|H^2| <= m^{N_{3,3}}`.

### 3.2 Degree 1

Let `(a, b)` be a 1-cocycle whose values depend only on `y|_{[-ρ,ρ]^2}`, and choose `n` with
`s_n > ρ + 2`.

1. **Potential inside supertiles.**
   - For a vertex `p ∈ V(S)`, define `f(σ^p y)` as the sum of `(a, b)` along the canonical path in
     `V(S)`: from the corner `c`, first horizontally, then vertically, to `p`.
   - The edge values read `y` within distance `ρ` of `V(S)`, which lies inside the collar of `S`.
     So `f(y)` is a function of `(x_n(y)|_{[-1,1]^2}, k_n(y))`, and `f ∈ M` by (P2).
2. **The residual vanishes inside supertiles.** Let `ψ = (a, b) - δ^0 f`.
   - For an edge with both endpoints in `V(S)`, the two canonical paths and the edge bound a union
     of unit squares whose four corners all lie in `V(S)`.
   - The cocycle condition on those squares gives circulation 0. So `ψ = 0` on such edges.
3. **Crossing edges.** The remaining edges join `V(S)` to `V(S')` for grid neighbours `S`, `S'`.
   - Take a vertical boundary: `p` in the right column of `V(S)` and `p + e_1 ∈ V(S')`.
   - For `p` and `p + e_2` both in `V(S)`, (P1) gives `p + e_1` and `p + e_1 + e_2` in `V(S')`.
     The square at `p` has its left edge in `V(S)` and its right edge in `V(S')`, where `ψ = 0`.
   - The cocycle condition then gives `ψ(p -> p+e_1) = ψ(p+e_2 -> p+e_2+e_1)`.
   - So `ψ` is constant on the crossing edges of each vertical boundary between `S` and `S'`, and
     likewise on horizontal ones.
4. **Values depend on a bounded block.** The constant on the boundary `(S, S')` reads `y` only
   within the collars of `S` and `S'`, that is, on a `4 × 3` block of `x_n(y)` (or a `3 × 4` block
   for horizontal boundaries).
   - So `ψ` lies in the subgroup `W_n ⊆ M^2` of cochains that vanish off crossing edges and equal,
     on the crossing edges of each boundary, a value depending only on the adjacency block.
   - `W_n` is the image of a map from `R^{N_{4,3} + N_{3,4}}`, so `|W_n| <= m^{N_{4,3} + N_{3,4}}`.
5. **Counting.** Any finitely many classes in `H^1` have representatives of a common radius `ρ`.
   All of them lie in the image of `W_n ∩ ker δ^1` for one `n`. So every finitely generated
   subgroup of `H^1` has order at most `m^{N_{4,3} + N_{3,4}}`, and so does `H^1`. ∎

**Remark (integral coefficients).**
- The degree-2 argument shows that `H^2(Z^2; C(X, Z))` is finitely generated.
- The degree-1 argument bounds only the rank of each finitely generated subgroup. Integral `H^1`
  can be an increasing union, like `Z[1/2]`, so its finite generation is not claimed.

## 4. Corollary 7: Labbé's shift

1. **Hypotheses.** Labbé's Proposition `prop:pre-main` (lines 2269–2280) reads: "The d-dimensional
   morphism `ω : Omega_U -> Omega_U` defined as `ω = α ∘ β ∘ γ` is expansive, recognizable in
   `Omega_U` and satisfies
   `Omega_U = ω(Omega_U) ∪ σ^{e_1} ω(Omega_U) ∪ σ^{e_2} ω(Omega_U) ∪ σ^{e_1+e_2} ω(Omega_U)`."
   - The displayed equation gives `Omega_U = closure_σ(ω(Omega_U))`. Lemma
     `lem:existence-omega-representation`, line 973, gives the language form.
   - So Theorem 6 applies.
2. **Mod-2 cohomology.** `H^1(Z^2; C(Omega_U, Z/2))` and `H^2(Z^2; C(Omega_U, Z/2))` are finite.
   - `Z^2` acts freely and minimally (`minimal-aperiodic-wang-shift-exists`).
   - Part 1, Theorem 3, then gives `H_2(D) ≅ Z ⊕ T`, with `T` a finite 2-group of exponent
     at most 4.
3. **All degrees.**
   - `Y` is the universal cover of `Ω^∞_0 K`. For `j >= 2`, `π_j(Y) = π_j(K)` is filtered by
     pieces `H_p(G; π_q(S))` with `p + q = j` and `p <= 2`.
   - If `q >= 1`, `π_q(S)` is finite, so the piece is finite by Theorem 6 and duality. It is a
     finite product of groups `Z/m`, and Theorem 6 applies to each `Z/m`.
   - The only piece with `q = 0` is `(p, q) = (2, 0)`, which is `H_2(G) = Z`.
   - So every `π_j(Y)` is finitely generated. By Serre's mod-`C` Hurewicz theorem, every
     `H_j(D) = H_j(Y)` is finitely generated. The finiteness of integral `H_1(G)` is never needed.
4. **Additive invariants.** Proposition 5 of part 1 applies verbatim with `μ` the invariant
   probability of `Omega_U`.

**Consequences for the graph.**
- **Dead routes.** Refuting finite presentation of `D([[Omega_U]])` through infinitely generated
  homology, or through an additive relation invariant, is dead.
- **What remains.** A proof of non-finite presentation must be nonabelian. Two candidates:
  - LEF (`labbe-shift-derived-full-group-is-lef`, which by itself would refute finite
    presentation);
  - rigidity on defect models, or non-spatial marked approximants.
- **Scope of Theorem 6.** It covers every self-similar tiling in Labbé's sense. So the homological
  criterion of part 1 can fire only for non-self-similar minimal `Z^2`-systems, for instance
  products `X_1 × X_2` with `K^0(X_i) ⊗ Z/2` infinite, or hierarchical systems with unbounded
  collared-type counts.
