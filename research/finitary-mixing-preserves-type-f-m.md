---
rg: 2
id: finitary-mixing-preserves-type-f-m
kind: claim
title: Permutation groups containing the finitary symmetric group whose finite-set stabilizers are of type F_m stay in that class under finitary mixing, proved by Brown's criterion on the balanced slice of the infinite cube of recolorings
requires:
  - strongly-shift-similar-point-stabilizers-are-copies-of-the-group
distinct_from:
  finitary-mixing-of-fp-highly-transitive-groups-is-fp: that is the case m = 2, proved by an explicit presentation, with only point stabilizers assumed finitely generated; this proves every m (including m = infinity) by a contractible complex, and assumes all finite-set stabilizers of type F_m.
  bh-class-closed-under-finite-direct-products: that is about embedding products into fp simple groups; this is a finiteness-property statement for one explicit overgroup of a product of permutation groups.
---

**ESTABLISHED** (lane proof, below; not independently reviewed; no priority claimed). The only imports are
Geoghegan's rigid form of Brown's criterion and finite-index invariance of type `F_m`. Both were read at source on
2026-09-18. A bounded priority search (see `strongly-shift-similar-type-f-m-passes-to-houghton-like-groups`) found
no earlier proof.

**The class.** For `1 <= m <= infinity`, let `𝔐_m` be the class of pairs `(Y, A)` with `Y` infinite,
`FSym(Y) <= A <= Sym(Y)`, and `Fix_A(F)` (pointwise stabilizer) of type `F_m` for every finite `F ⊂ Y`,
including `F = ∅`.

**Statement.**
1. **Two blocks.** If `(Y, A), (Z, C) ∈ 𝔐_m` with `Y ∩ Z = ∅`, then `M = (A x C) · FSym(Y ⊔ Z)` is of type `F_m`,
   and `(Y ⊔ Z, M) ∈ 𝔐_m`.
2. **Many blocks.** If `(X_k, G_k) ∈ 𝔐_m` for `k = 1..n`, then `(G_1 x ... x G_n) · FSym(X_1 ⊔ ... ⊔ X_n)` is of type
   `F_m` and lies in `𝔐_m`.
3. **Membership.** If `G <= Sym(N)` is strongly shift-similar and of type `F_m`, then `(N, G) ∈ 𝔐_m`.

**Imports.**
**Source.** R. Geoghegan, *Topological Methods in Group Theory*, GTM 243, Springer 2008, Chapter 7. The chapter PDF
was fetched on MSI via institutional access, with SHA-256
`d878192da46df2c5d6737f66bb63332308a11be34af56124f7d40977a919e56a`. It was converted to text with ghostscript
`txtwrite` and read there. Quotes are verbatim up to extraction spacing.
- (B) **Theorem 7.3.1**: "For `n ≥ 1`, let `Y` be an `(n−1)`-connected rigid `G`-CW complex having finite
  `n`-skeleton mod `G`. If the stabilizer of each `i`-cell has type `F_(n−i)` for all `i ≤ n − 1`, then `G` is of
  type `F_n`." The book's Source Notes attribute Brown's criterion to Brown's paper (K. S. Brown, *Finiteness
  properties of groups*, JPAA 44 (1987)). That paper's Proposition 1.1 could not be read: ScienceDirect returned a
  bot wall from MSI. So the rigid form is cited from Geoghegan, and the proof below arranges rigidity by barycentric
  subdivision. For `m = infinity`, apply (B) for each finite `m` and use Proposition 7.2.2 (`F_infinity` iff `F_n`
  for all `n`).
- (F) **Corollary 7.2.4**: "Let `H ≤ G` and let `[G : H] < ∞`. For `0 ≤ n ≤ ∞`, `G` has type `F_n` iff `H` has type
  `F_n`."

**Proof of 3.** `FSym(N) <= G`, and `Fix_G(F) ≅ G` for finite `F`
(`strongly-shift-similar-point-stabilizers-are-copies-of-the-group`, items 1 and 3).

**Proof of 1.** Put `W = Y ⊔ Z`.
- *Recolorings.* A recoloring is a map `c : W -> {Y, Z}` that differs on a finite set `D(c)` from the side map
  `c_0`. `M` acts by `b · c = c ∘ b^-1`. This preserves recolorings, since `A x C` fixes `c_0` and finitary
  permutations change a coloring at finitely many points.
- *The infinite cube.* Let `𝒳` be the cube complex with vertices the recolorings and a cube
  `Q(c, F) = {c' : c' = c off F}` of dimension `|F|` for every finite `F ⊂ W`. `M` acts by cubical automorphisms,
  with `b Q(c,F) = Q(b·c, b(F))`. The cubes `Cube_F = Q(c_0, F)` are finite cubes `[0,1]^F`, and every finite
  subcomplex lies in one of them.
- *Height.* Put `h(c) = |D(c) ∩ Z| - |D(c) ∩ Y|`. It is `M`-invariant: `A x C` preserves the sides, and for a
  finitary `f` and a finite `f`-invariant `S ⊇ D(c) ∪ D(c ∘ f^-1)`, `h(c) = |c^-1(Y) ∩ S| - |Y ∩ S|` is unchanged.
  On `Cube_F` with coordinates `t ∈ [0,1]^F`, `h = Σ_(F∩Z) t_w - Σ_(F∩Y) t_w`. Extending affinely, `h` is affine on
  every cube and changes by `±1` along every edge.
- *The balanced slice.* Let `L = h^-1(0) ⊂ 𝒳`. Its cells are the level vertices and the slices `P_Q = Q ∩ L` for
  cubes `Q` whose interior meets `L`. Then `dim P_Q = dim Q - 1`, and no edge interior meets `L`, since heights are
  integers differing by 1. `L ∩ Cube_F` is a hyperplane slice of a cube through the vertex `c_0`, so it is convex and
  nonempty. Every finite subcomplex of `L` lies in some `L ∩ Cube_F`. So `L` is contractible, and its `m`-skeleton
  `L^(m)` (the slices of cubes of dimension `<= m+1`, and the level vertices) is `(m-1)`-connected.
- *Transitivity.* The level vertices are the recolorings with `|D ∩ Y| = |D ∩ Z|`. A finitary permutation swapping
  `D ∩ Y` with `D ∩ Z` carries `c_0` to any of them, so `M` is transitive on them. Their stabilizer is
  `Stab_M(c_0) = M ∩ (Sym(Y) x Sym(Z)) = A x C`. Indeed, if `b = gf` with `g ∈ A x C` and `f` finitary preserves
  the sides, then so does `f`, so `f ∈ FSym(Y) x FSym(Z) <= A x C`.
- *Cocompactness.* A cube whose interior meets `L` has a level vertex. Translating it to `c_0`, the cube becomes
  `Q(c_0, F)`, and its `(A x C)`-orbit is fixed by `(|F ∩ Y|, |F ∩ Z|)`, since `A` and `C` are highly transitive.
  So `L^(m)` has finitely many `M`-orbits of cells.
- *Stabilizers.* The stabilizer of `P_Q` equals that of `Q`, because `Q` is the unique cube whose interior contains
  the relative interior of `P_Q`. For `Q = Q(c_0, F)`, the kernel `K_Q` of the action of `Stab(Q)` on the `2^|F|`
  vertices of `Q` has finite index. We claim `K_Q = Fix_A(F ∩ Y) x Fix_C(F ∩ Z)`.
  - `K_Q <= Stab(c_0) = A x C`.
  - If `g ∈ A x C` moves `x ∈ F` to `y ≠ x`, then the vertex `c'` that flips only `x` has
    `(c' ∘ g^-1)(y) = c'(x) ≠ c_0(y) = c'(y)`. So `g` does not fix `c'`.
  - Conversely, an element of `A x C` fixing `F` pointwise fixes every `c'` that equals `c_0` off `F`.
- *Brown.* Pass to the barycentric subdivision of `L^(m)`. There the action is rigid, the complex is still
  `(m-1)`-connected and finite modulo `M`, and a simplex stabilizer is a flag stabilizer `S` with
  `K_(Q_top) <= S <= Stab(Q_top)`. `K_(Q_top)` is a product of stabilizers of finite sets, hence of type `F_m` by
  hypothesis, so `S` is of type `F_m` by (F). By (B), `M` is of type `F_m`.
- *`M ∈ 𝔐_m`.* Let `F ⊂ W` be finite and `b ∈ Fix_M(F)`, say `b ≡ g` modulo finitary with `g ∈ A x C`. Choose
  `f' ∈ FSym(Y) x FSym(Z)` with `f' g` fixing `F` pointwise. Then `b ≡ f'g ∈ Fix_A(F∩Y) x Fix_C(F∩Z)`. So restriction
  to `W \ F` identifies `Fix_M(F)` with the mixing of `(Y \ F, Fix_A(F ∩ Y))` and `(Z \ F, Fix_C(F ∩ Z))`. Both pairs
  lie in `𝔐_m`, since `Fix_A(F ∩ Y)` contains `FSym(Y \ F)` and its finite-set stabilizers are those of `A`. So the
  first part of the proof applies. ∎

**Proof of 2.** Induct on `n`. The mixing of `n` blocks is the two-block mixing of the first `n-1` blocks'
mixing with `G_n`. ∎

**Calibrations.**
- `m = 2` recovers `finitary-mixing-of-fp-highly-transitive-groups-is-fp` (under the stronger stabilizer hypothesis).
- The 1-cells of `L` are the diagonals of squares with one ascending and one descending direction. They join `c` to
  `c ∘ (y z)`, so the 1-skeleton is the transposition graph on balanced recolorings.
- **`FSym` is needed.** For trivial `A` and `C`, `M = FSym(W)` is not finitely generated. The proof breaks at
  `Stab(c_0) = A x C`, which needs `FSym(Y) <= A`.
- **Houghton check.** `(H_k-rays, H_k) ∈ 𝔐_(k-1)`, via its strongly shift-similar representation and item 3, since
  `H_k` is of type `F_(k-1)` (Brown). Item 1 then gives `(H_a x H_b) · FSym` of type `F_(min(a,b)-1)`. That group is
  the kernel of a character of `H_(a+b)`, which is of type `F_(a+b-1)`, so there is no conflict with Brown's theorem.
