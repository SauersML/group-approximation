# The Penrose cut-torus subshift is of finite type (2026-09-16)

Author: swarm agent on `penrose-derived-full-group-is-finitely-presented`.
Supports: `penrose-cut-torus-subshift-is-of-finite-type` via route
`penrose-cut-torus-subshift-finite-type-proof`.

## 0. Statement and trust surface

**Theorem.** Let `Λ = P/Lat ≅ Z^2 ⊕ Z/5` act on the Cantor set `X = C~/Lat` of
Chornyi--Juschenko--Nekrashevych (ChJN, arXiv:1602.04255, section "Penrose tiling
group"). Then:

1. the action is expansive: some finite clopen partition of `X` gives an equivariant
   embedding `X -> A^Λ`, whose image `Y` is a free minimal `Λ`-subshift;
2. `Y` is a subshift of finite type.

Since finite type is a conjugacy invariant, item 2 holds for every generating clopen
partition.

**Consequence for the Penrose problem.** By Theorem G
(`fp-alternating-full-groups-of-free-subshifts-force-sft`), "D(𝒫) finitely presented"
implies only "`Y` is of finite type", and that is true. So Theorem G and every other
finite-type obstruction give nothing here. The Penrose group sits in the same class as
Labbé's `Omega_U`: free minimal subshifts of finite type over a finitely generated
abelian group.

**Trust surface.** The proof uses exactly these imports. Line numbers refer to the TeX
source `IET_copy.tex` of arXiv:1602.04255, fetched from arXiv on 2026-09-16. Beyond line 95
they differ slightly from the copy cited in `penrose-tiling-group-amenable-orbit-citation`:
for example, "Polygons with sides belonging to lines" is at line 439 here.

- **(I1)** ChJN, `IET_copy.tex` lines 569--582. `F` is a clopen fundamental domain for
  `Lat = <w_1, w_2>` acting on `C~`. `Λ ≅ Z^2 ⊕ Z/5`, and `X = C~/Lat` is homeomorphic
  to `F`. The node `penrose-tiling-group-is-an-amenable-orbit-full-group` imports this
  already, and adds that `Λ` acts freely.
- **(I2)** ChJN lines 512--527. There are `t_1, ..., t_4 ∈ P` such that the sets
  `V_s'' = V_s' + t_s` are pairwise disjoint. Their union `V''` is equidecomposable with
  `F`: some homeomorphism `φ : F -> V''` is locally a translation by elements of `P`.
- **(I3)** ChJN lines 485--500, attributed there to de Bruijn (1981). The map
  `(s, ξ~) -> (T_ξ~, s)` is a bijection from `V' = ∪_s (s, V_s')` onto the space `𝒯`
  of pointed Penrose tilings up to translation, and it is a homeomorphism. The topology
  on `𝒯` is ChJN's vertex-patch topology (lines 346--358): basic sets `U_{A,v}` are the
  pointed tilings whose vertex set contains the translated finite set `A`.
- **(I3a)** ChJN lines 356--358: "the space `𝒯` is homeomorphic to the Cantor set, and
  ... for every Penrose tiling `T` the set of pointed tilings `(T, v)` is dense". We use
  only that `𝒯` is Hausdorff in the vertex-patch topology. That forces a Penrose tiling to
  be determined by its vertex set, which ChJN use tacitly at lines 343--344 ("We sometimes
  identify a tiling with the set of vertices of its tiles"). Lemma 0 upgrades this to
  local constancy of decorated tile patches. This is the import a referee should check
  first; see §6.
- **(I4)** ChJN lines 299--315 and 336--344. A Penrose tiling is a tiling of the plane by
  the two unit rhombi, decorated with single and double arrows, in which adjacent tiles
  carry matching arrows. `𝒯` is the set of such tilings with sides parallel to the lines
  `e^{kπi/5} R`, pointed at a vertex and taken up to translation.
- **(I5)** ChJN lines 464--467 and 491--498. For `v = Σ n_j ζ^{2j} ∈ P` and
  `v' = Σ n_j ζ^j`, `x ∈ T_ξ~` if and only if `x - v' ∈ T_{ξ~ + v}`. The vertices of
  `T_ξ~` correspond bijectively to the points of `V'` in the `P`-orbit of `ξ~`, through
  `x = Σ k_j ζ^j -> (s, ξ~ + v)` with `s = Σ k_j` and `v = Σ k_j ζ^{2j} - s`.

Beyond these, the proof uses only elementary plane topology (§4).

**Novelty.** Penrose rhombus tilings form a tiling space of finite type by definition.
Fernique--Lutfalla (arXiv:2211.08239) prove the sharper undecorated statement and call
it folklore. What is new here is only the transfer to ChJN's group-action model over
`Z^2 ⊕ Z/5`, where the group is not the translation group of the tiling. That transfer
needs the developing argument of §4, because `Λ` is not a lattice in the physical plane.

## 1. Notation

- `ζ = e^{2πi/5}`, and `P = {Σ n_j ζ^j : Σ n_j = 0} = (1 - ζ) Z[ζ] ≅ Z^4`.
- `σ` is the field automorphism of `Q(ζ)` with `σ(ζ) = ζ^2`, so `σ(P) = P`.
- `C~` is the plane with the lines of `L` doubled, and `Q : C~ -> C`.
- `Lat = <w_1, w_2>`, `Λ = P/Lat`, and `X = C~/Lat`. The class of `ξ~ ∈ C~` is written
  `[ξ~]`. `Λ` acts by `[ξ~] + (p mod Lat) = [ξ~ + p]`.
- `S ⊂ Λ` is a finite symmetric generating set, and `|μ|` is word length.
- A **Penrose tiling** is as in (I4). For a tiling `T` with `0` as a vertex, the
  **`r`-patch** `pat_r(T)` is the set of decorated tiles of `T` meeting the closed disc
  `B(0, r)`. The **star** `st(T) = pat_0(T)` is the set of tiles containing `0`.
- `𝒯` is realised as the set of Penrose tilings having `0` as a vertex. A tiling pointed
  at a vertex `v` is identified with its translate `T - v`. The topology has the basis
  `{T : pat_r(T) = π}`.

- `E = {±ζ^j : 0 <= j <= 4}` is the set of the 10 unit edge vectors.

**Edge distance.** Let `M(r) = ⌈22 (r + 2)^2⌉`. In every Penrose tiling with `0` as a
vertex, every vertex of every tile meeting `B(0, r)` is joined to `0` by an edge path of
length at most `M(r)`.

*Proof.* The tiles meeting `B(0, r)` lie in `B(0, r + 2)`, since a tile has diameter at
most `2 cos 18° < 2`. Each tile has area at least `sin 36° > 0.58`, so there are at most
`π (r + 2)^2 / 0.58 < 5.5 (r + 2)^2` of them.
- Their union contains the disc `B(0, r)`, so it is connected.
- Penrose tilings are edge to edge: the matching condition of (I4) compares whole edges,
  and the de Bruijn tilings `T_ξ~` of (I3) are duals of pentagrids. So two of these closed
  rhombi that meet share a vertex.
- Hence their 1-skeleton is a connected graph containing `0`, with fewer than
  `22 (r + 2)^2` vertices. ∎

**Finite local complexity.** Every vertex of an `r`-patch is `Σ_{i <= M(r)} e_i` with
`e_i ∈ E ∪ {0}`, a finite set. There are 20 decorated tile types. So only finitely many
`r`-patches occur.

**Lemma 0 (decorated patches are locally constant).** Let `𝒯_dec` be `𝒯` with the
tile-patch topology, whose basic sets are `{T : pat_r(T) = π}`. Then the identity
`𝒯_dec -> 𝒯` is a homeomorphism. Hence `T -> pat_r(T)` is locally constant on `𝒯` for
every `r`.

*Proof.*
1. **Compactness.** `𝒯_dec` is compact by the diagonal argument. Its basis
   `{pat_r = π}`, `r ∈ N`, is countable by finite local complexity, so sequential
   compactness suffices.
   - Given a sequence, finite local complexity lets us pass to a subsequence whose
     `r`-patches are eventually constant, say `π_r`, for `r = 1, 2, ...`.
   - The `π_r` increase, and their union is a set of decorated tiles covering the plane
     with disjoint interiors and matching arrows. It is a Penrose tiling with vertex `0`,
     and it is the limit.
2. **Continuity.** The identity is continuous. If `A ⊂ V(T) ∩ B(0, r)`, then every
   `T'` with `pat_r(T') = pat_r(T)` has `A ⊂ V(T')`, because vertices in `B(0, r)` are
   vertices of tiles meeting `B(0, r)`.
3. **Conclusion.** `𝒯` is Hausdorff by (I3a). A continuous bijection from a compact space
   onto a Hausdorff space is a homeomorphism. ∎

**Compactness and factoring.** `X` is compact. The map `Θ : X -> 𝒯` of §2 is a continuous
bijection onto a Hausdorff space, so it is a homeomorphism.
- Let `f` be a locally constant function on `X`. Its level sets are finitely many clopen
  sets.
- Each is a finite union of basic sets `Θ^{-1}{pat_r = π}`, by Lemma 0 and compactness.
- Taking the largest `r` involved, `f` factors through `pat_r ∘ Θ`, and then through
  `pat_{r'} ∘ Θ` for every `r' >= r`.

## 2. The orbit correspondence

**The map `Θ`.** Compose the homeomorphisms of (I1), (I2) and (I3).
- By (I1), identify `X` with `F`: each class `[ξ~]` has a unique representative in `F`.
- By (I2), for `f ∈ F` let `s(f) ∈ {1, 2, 3, 4}` be the index with `φ(f) ∈ V_s''`, and
  put `η(f) = φ(f) - t_{s(f)} ∈ V_{s(f)}'`.
- Write `η(f) = f + κ(f)`. Then `s` and `κ` are locally constant on `F`, and `κ` takes
  values in `P`, because `φ` is locally a translation by elements of `P`.
- Set `Θ(f) = T_{η(f)} - s(f) ∈ 𝒯`. This is the tiling of (I3) for `(s(f), η(f)) ∈ V'`,
  translated so that its marked vertex is `0`.

`Θ` is a homeomorphism `X -> 𝒯`. It is the composite of `X ≅ F`, of `φ`, of the
homeomorphism `V'' -> V'`, `ξ~ -> (s, ξ~ - t_s)` on the disjoint clopen pieces `V_s''`,
and of (I3). By Lemma 0 each `pat_r ∘ Θ` is locally constant.

**Translating tilings.** For `v ∈ P` put `v' = σ^{-1}(v)`. By (I5), `T_{ξ~ + v}` and
`T_ξ~ - v'` have the same vertex set. Both are Penrose tilings, since a translate of a
Penrose tiling is one. By (I3a) a Penrose tiling is determined by its vertex set, so
`T_{ξ~ + v} = T_ξ~ - v'` as decorated tilings.

**Lemma 1 (orbit correspondence).** For `x ∈ X` there is a bijection
`ψ_x : Λ -> V(Θ(x))` such that:
1. `ψ_x(0) = 0`, and `Θ(x + λ) = Θ(x) - ψ_x(λ)` for all `λ`;
2. `ψ_x(λ + μ) = ψ_x(λ) + ψ_{x + λ}(μ)`;
3. for each `λ`, the map `x -> ψ_x(λ)` is locally constant on `X`.

*Proof.* Let `x = [f]` with `f ∈ F`.

- **Definition.** For `λ ∈ Λ` let `f_λ ∈ F` be the representative of `x + λ`, so
  `f_λ = f + p` for the unique `p ∈ λ` with `f + p ∈ F` (I1). Then
  `η(f_λ) - η(f) = p + κ(f_λ) - κ(f) ∈ P`, and we put
  `ψ_x(λ) = s(f_λ) - s(f) + σ^{-1}(η(f_λ) - η(f))`.
- **Item 1.** Put `v = η(f_λ) - η(f)`. By the translation rule
  `T_{η(f_λ)} = T_{η(f)} - σ^{-1}(v)`, so
  `Θ(x + λ) = T_{η(f)} - σ^{-1}(v) - s(f_λ) = Θ(x) - ψ_x(λ)`. Since `0` is a vertex of
  `Θ(x + λ)`, `ψ_x(λ)` is a vertex of `Θ(x)`. Also `f_0 = f`, so `ψ_x(0) = 0`.
- **Item 2.** The representative of `(x + λ) + μ` is `f_{λ + μ}`. The formula is a
  difference of the quantities `s(f_ν) + σ^{-1}(η(f_ν) - η(f))`, which telescopes:
  `ψ_x(λ + μ) = ψ_x(λ) + ψ_{x + λ}(μ)`.
- **Injectivity.** If `ψ_x(λ) = ψ_x(μ)`, then `Θ(x + λ) = Θ(x + μ)` by item 1. `Θ` is
  injective, so `x + λ = x + μ`, and `λ = μ` because `Λ` acts freely
  (`penrose-tiling-group-is-an-amenable-orbit-full-group`, item 2).
- **Surjectivity.** Let `w` be a vertex of `Θ(x)`, so `z = w + s(f)` is a vertex of
  `T_{η(f)}`.
  - Write `z = Σ k_j ζ^j` with `s' = Σ k_j ∈ {1, ..., 4}`, and put
    `u = Σ k_j ζ^{2j} - s' ∈ P`. By (I5), `(s', η(f) + u) ∈ V'` and `σ^{-1}(u) = z - s'`.
  - By (I1)--(I3) there is `f' ∈ F` with `s(f') = s'` and `η(f') = η(f) + u`.
  - Then `f' = f + κ(f) + u - κ(f') ∈ f + P`, so `f' = f_λ` for some `λ ∈ Λ`.
  - The formula gives `ψ_x(λ) = s' - s(f) + σ^{-1}(u) = s' - s(f) + z - s' = w`.
- **Item 3.** Fix a representative `p_0 ∈ P` of `λ`. The sets `F ∩ (F - p_0 - l)`, for
  `l ∈ Lat`, are clopen and partition `F`. Only finitely many are nonempty, because `Q(F)`
  is bounded and `Lat` is discrete in `C`. On each of them `f_λ = f + p_0 + l`. Since `s`
  and `κ` are locally constant, so is `ψ_x(λ)`. ∎

**The functions `c` and `d`.**
- For `s ∈ S` put `c(s, x) = ψ_x(s)`. By Lemma 1.3 it is locally constant, so it takes
  finitely many values. Let `D = max |c(s, x)|`.
- For `e ∈ E`, the set `X_e = {x : e ∈ V(Θ(x))}` is clopen by (I3). For `x ∈ X_e` put
  `d(e, x) = ψ_x^{-1}(e) ∈ Λ`.
  - The sets `{x : ψ_x(λ) = e}`, for `λ ∈ Λ`, are clopen by Lemma 1.3 and partition `X_e`.
  - By compactness only finitely many are nonempty, so `d(e, ·)` is locally constant with
    finite range.
  - Let `D'` be the maximum word length of `d(e, x)`.

By the factoring statement of §1, fix `r_0 >= 3` such that every `c(s, ·)`, every
indicator of `X_e`, and every `d(e, ·)` factors through `pat_{r_0} ∘ Θ`. Write
`c(s, x) = ĉ_s(pat_{r_0} Θ(x))` and `d(e, x) = d̂_e(pat_{r_0} Θ(x))`.
## 3. The coding and expansiveness

**Alphabet and coding.** Let `A` be the finite set of `r_0`-patches (§1). Put
`ℓ(x) = pat_{r_0}(Θ(x))` and `y_x(μ) = ℓ(x + μ)` for `μ ∈ Λ`. Let
`Y = {y_x : x ∈ X} ⊆ A^Λ`.

**Proposition 2.** The map `x -> y_x` is a `Λ`-equivariant homeomorphism `X -> Y`. So `Y`
is a subshift, `Λ` acts freely on `Y`, and the action on `X` is expansive.

*Proof.*
- **Continuity and equivariance.** Each coordinate `x -> ℓ(x + μ)` is locally constant,
  by Lemma 0. `y_{x + λ}(μ) = y_x(μ + λ)`. Since `Λ` is abelian this is the shift action
  `(λ·y)(μ) = y(μλ)` of `fp-alternating-full-groups-of-free-subshifts-force-sft`.
- **Injectivity.** Suppose `y_x = y_{x'}`.
  - The increments `c(s, x + λ) = ĉ_s(y_x(λ))` agree for `x` and `x'`. By Lemma 1.2,
    `ψ_x(λ + s) = ψ_x(λ) + c(s, x + λ)`, so by induction on word length `ψ_x = ψ_{x'}`.
  - By Lemma 1.1, for every `λ` the tiles of `Θ(x)` meeting `B(ψ_x(λ), r_0)` are exactly
    the tiles of `y_x(λ) + ψ_x(λ)`, and likewise for `x'`.
  - Every tile of `Θ(x)` has a vertex, which is `ψ_x(λ)` for some `λ` by Lemma 1. So
    `Θ(x) = Θ(x')`, and `x = x'` because `Θ` is injective.
- **Homeomorphism.** `X` is compact and `A^Λ` is Hausdorff.
- **Freeness.** Freeness transfers from `X` (`penrose-tiling-group-is-an-amenable-orbit-full-group`,
  item 2).
- **Expansive.** This is the existence of the embedding. ∎

**Minimality.** By Lemma 1 the orbit `x + Λ` maps under `Θ` onto the pointed tilings
`(Θ(x), v)` with `v` a vertex. These are dense in `𝒯` by (I3a). So `Λ ~ X` and `Λ ~ Y`
are minimal. This is not used below.

## 4. `Y` is of finite type

**Constants.**
- `Λ = <S | ℛ>` is a finite presentation. Every abelian finitely generated group has one.
  Let `L` bound the relator lengths.
- `D` and `D'` are as in §2, and `M(r)` is as in §1.
- `m_* = 2 M(max(D, r_0 + 2)) + 2`, and `N = max(L, (m_* + 2) D')`. Since `r_0 >= 3`,
  `m_* >= 2 M(3)`.

**Setup.** Let `y ∈ A^Λ` be such that for every `λ` the pattern `y|_{λ + B(N)}` occurs in
`Y`. Choose `x_λ ∈ X` with `y(λ + μ) = ℓ(x_λ + μ)` for all `μ ∈ B(N)`. Write
`π_λ = y(λ)`. Define `c_y(s, λ) = ĉ_s(π_λ)`, and `d_y(e, λ) = d̂_e(π_λ)` whenever
`e ∈ V(π_λ)`. We show that `y ∈ Y`.

Every `r_0`-patch `π ∈ A` contains the full star of `0`, and all neighbours of `0` lie in
`V(π)`, since `r_0 >= 3 > 1`.

**Step 1 (positions).** Define `pos_y : Λ -> C` by `pos_y(0) = 0` and
`pos_y(λ + s) = pos_y(λ) + c_y(s, λ)`, along words in `S`.

*Well defined.* The Cayley complex of `<S | ℛ>` is simply connected. So it suffices that
the increments sum to zero around every relator loop based at every `λ`.
- Such a loop stays in `λ + B(L) ⊆ λ + B(N)`.
- There `c_y(s, λ + μ) = ĉ_s(ℓ(x_λ + μ)) = c(s, x_λ + μ) = ψ_{x_λ + μ}(s)`.
- By Lemma 1.2 the increments along the loop sum to
  `ψ_{x_λ}(end) - ψ_{x_λ}(start) = 0`.

*Charts.* The same computation along a geodesic word gives, for `μ ∈ B(N)`,
`pos_y(λ + μ) - pos_y(λ) = ψ_{x_λ}(μ)`.

**Step 2 (chart lemma, F3).** Let `λ ∈ Λ` and let `0 = v_0, v_1, ..., v_k` be an edge path
in `Θ(x_λ)` with `k D' <= N`. Define `λ_0 = λ` and
`λ_{i + 1} = λ_i + d_y(v_{i + 1} - v_i, λ_i)`. Then for all `i <= k`:
1. `μ_i = λ_i - λ` satisfies `ψ_{x_λ}(μ_i) = v_i` and `|μ_i| <= i D'`;
2. `π_{λ_i} = pat_{r_0}(Θ(x_λ) - v_i)`;
3. `pos_y(λ_i) = pos_y(λ) + v_i`.

*Proof.* By induction on `i`. The case `i = 0` holds since `ψ_{x_λ}(0) = 0` and
`π_λ = ℓ(x_λ)`.
- **Item 2 from item 1.** `μ_i ∈ B(N)`, so
  `π_{λ_i} = ℓ(x_λ + μ_i) = pat_{r_0}(Θ(x_λ) - ψ_{x_λ}(μ_i))` by Lemma 1.1.
- **Item 3 from item 1.** This is the chart identity of Step 1.
- **Step to `i + 1`.** Let `e = v_{i + 1} - v_i ∈ E`.
  - `e` is a neighbour of `0` in `Θ(x_λ) - v_i = Θ(x_λ + μ_i)`, so `d_y(e, λ_i)` is defined
    and equals `d(e, x_λ + μ_i) = ψ_{x_λ + μ_i}^{-1}(e)`.
  - By Lemma 1.2, `ψ_{x_λ}(μ_i + d_y(e, λ_i)) = v_i + e = v_{i + 1}`.
  - `|μ_{i + 1}| <= |μ_i| + D'`. ∎

In particular, the labels `λ_i` depend only on `v_i`, not on the path: `ψ_{x_λ}` is
injective, and item 1 gives `λ_i = λ + ψ_{x_λ}^{-1}(v_i)`.

**Step 3 (the tiles of `y`).** Let `λ ∈ Λ`, and let `τ ∈ π_λ` be a tile with vertices
`0, a, a + b, b`, where `a, b ∈ E`.
- Its **labels** are `lab(0) = λ`, `lab(a) = λ + d_y(a, λ)`, `lab(b) = λ + d_y(b, λ)` and
  `lab(a + b) = lab(a) + d_y(b, lab(a))`. They are computed from `y` alone.
- The **`y`-tile produced at `λ` from `τ`** is the pair `t = (Lab(t), ρ(t))`. Here
  `Lab(t) ⊂ Λ` is the set of the four labels, and `ρ(t) = τ + pos_y(λ)` is a decorated
  rhombus in `C`.

By the chart lemma, applied in the chart `x_λ` to the paths `(0, a)`, `(0, b)` and
`(0, a, a + b)`, we get `lab(v) = λ + ψ_{x_λ}^{-1}(v)` and `pos_y(lab(v)) = pos_y(λ) + v`
for each vertex `v` of `τ`. So:
- the vertices of `ρ(t)` are the points `pos_y(μ)` for `μ ∈ Lab(t)`;
- distinct labels of `t` have distinct positions;
- each label is attached to a definite vertex of `ρ(t)`.

**Claim A (a tile looks the same from each of its vertices).** Let `t` be produced at
`λ` from `τ`, and let `λ' = lab(v)` for a vertex `v` of `τ`. Then `τ - v ∈ π_{λ'}`, and
the `y`-tile produced at `λ'` from `τ - v` is `t`.

*Proof.* By the chart lemma, item 2, `π_{λ'} = pat_{r_0}(Θ(x_λ) - v) ∋ τ - v`.
- The labels at `λ'` come from `d_y`-steps along paths of length at most 2 in `τ - v`
  starting at `0`.
- Prefixing a genuine path of length at most 2 from `0` to `v` gives paths of length at
  most 4 in `Θ(x_λ)`.
- Since `4 D' <= N`, the chart lemma gives the labels `λ + ψ_{x_λ}^{-1}(w)` for the
  vertices `w` of `τ`, which is `Lab(t)`.
- Also `(τ - v) + pos_y(λ') = τ - v + pos_y(λ) + v = ρ(t)`. ∎

**Claim B (tiles at a label).** If `λ ∈ Lab(t)`, then `t` is produced at `λ` from the
tile `ρ(t) - pos_y(λ)` of `π_λ`. So at most 10 `y`-tiles contain a given label.

*Proof.* Apply Claim A to the tile at which `t` was produced, with `v` the vertex
labelled `λ`. ∎

Let `𝒦` be the set of all `y`-tiles. Two labels are **`y`-adjacent** if they are the
endpoints of an edge of some `ρ(t)`. For `m <= m_*`:
- `𝒢_λ(m)` is the set of tiles of `Θ(x_λ)` having a vertex at edge distance `<= m`
  from `0`;
- `𝒦_λ(m)` is the set of `t ∈ 𝒦` having a label joined to `λ` by a `y`-adjacent path of
  length `<= m`.

**Lemma 3 (chart isomorphism).** For `m <= m_*`, the map
`τ -> t(τ) = (λ + ψ_{x_λ}^{-1}(V(τ)), τ + pos_y(λ))` is a bijection from `𝒢_λ(m)` onto
`𝒦_λ(m)`. For `τ, τ' ∈ 𝒢_λ(m)`, the common labels of `t(τ)` and `t(τ')` are the images
of the common vertices of `τ` and `τ'`.

*Proof.*
- **Into.** Let `τ ∈ 𝒢_λ(m)` have a vertex `v` with a genuine edge path
  `0 = v_0, ..., v_k = v`, `k <= m`.
  - By the chart lemma, `λ_k = λ + ψ_{x_λ}^{-1}(v)` and `τ - v ∈ π_{λ_k}`.
  - The tile produced at `λ_k` from `τ - v` is `t(τ)`: its labels follow from the chart
    lemma along paths of length `<= k + 2 <= m_* + 2`, and its rhombus is
    `τ - v + pos_y(λ_k) = τ + pos_y(λ)`.
  - Each edge `[v_i, v_{i+1}]` lies in a genuine tile at `v_i`. The tile produced at
    `λ_i` from it shows that `λ_i` and `λ_{i+1}` are `y`-adjacent. So `t(τ) ∈ 𝒦_λ(m)`.
- **Onto.** Let `t ∈ 𝒦_λ(m)` have a label `μ` joined to `λ` by a `y`-adjacent path
  `λ = μ_0, ..., μ_k = μ`, `k <= m`. Put `e_i = pos_y(μ_{i+1}) - pos_y(μ_i) ∈ E` and
  `v_i = e_0 + ... + e_{i-1}`.
  - By induction on `i`, `v_i` is a genuine edge path in `Θ(x_λ)`, and `μ_i` is the label
    `λ_i` of the chart lemma.
  - Given this for `i`: the edge `(μ_i, μ_{i+1})` lies in some `y`-tile, produced at
    `μ_i` by Claim B. So `e_i` is an edge at `0` of `π_{μ_i} = pat_{r_0}(Θ(x_λ) - v_i)`,
    hence a genuine edge at `v_i`.
  - By Claim B, `ρ(t) - pos_y(μ)` is a tile of `π_μ` at `0`, and item 1 of the chart
    lemma identifies the labels. So `t = t(τ)` for `τ = ρ(t) - pos_y(λ) ∈ 𝒢_λ(m)`.
- **Injective and common labels.** `ρ(t(τ))` determines `τ`. Common labels correspond to
  common vertices because `ψ_{x_λ}^{-1}` is injective. ∎

**Step 4 (the developing map).**

*The space `K`.* Take the disjoint union of the closed rhombi `ρ(t)`, `t ∈ 𝒦`. Identify
`(t, p)` with `(t', p')` when `p = p'` and `p` lies in the face
`Fc(t, t') = conv{pos_y(μ) : μ ∈ Lab(t) ∩ Lab(t')}`. Call the quotient `K`, and define
`dev : K -> C` by `[t, p] -> p`.

1. **Faces.** If `λ ∈ Lab(t) ∩ Lab(t')`, then by Claim B and Lemma 3 with `m = 0` we have
   `t = t(τ)` and `t' = t(τ')` for tiles `τ, τ' ∋ 0` of `Θ(x_λ)`. So
   `Fc(t, t') = pos_y(λ) + (τ ∩ τ')` is a common face: a vertex, an edge, or the whole
   rhombus when `t = t'`.
2. **The relation is an equivalence.** Let `p ∈ Fc(t, t') ∩ Fc(t', t'')`, and let `φ` be
   the smallest face of `ρ(t')` containing `p`.
   - `φ` lies in both faces, so its vertices are positions of labels common to `t'` and
     `t`, and to `t'` and `t''`.
   - Distinct labels of `t'` have distinct positions. So the labels of `φ` lie in
     `Lab(t) ∩ Lab(t'')`, and `p ∈ φ ⊆ Fc(t, t'')`.
3. **Open stars.** By Claim B each label lies in at most 10 tiles. For a label `λ`, the
   open star `O(λ)` is the set of classes `[t, p]` with `λ ∈ Lab(t)` and `p` in the
   relative interior of a face of `ρ(t)` containing `pos_y(λ)`.
   - By item 1, its preimage in `ρ(t')` is empty if `λ ∉ Lab(t')`, and the open star of
     the vertex `pos_y(λ)` in `ρ(t')` otherwise. So `O(λ)` is open.
   - The sets `O(λ)` cover `K`. `dev` is well defined and continuous.
4. **Chart regions.** For `m <= m_*` let `R_λ(m) ⊆ K` be the union of the `ρ(t)`,
   `t ∈ 𝒦_λ(m)`, and let `G_λ(m) = pos_y(λ) + ∪ 𝒢_λ(m) ⊂ C`. Then
   `dev : R_λ(m) -> G_λ(m)` is a homeomorphism.
   - `R_λ(m)` is compact, as the image of finitely many rhombi.
   - `dev` maps it onto `G_λ(m)` by Lemma 3.
   - **Injective.** Suppose `[t, p]` and `[t', p]` lie in `R_λ(m)`. By Lemma 3,
     `t = t(τ)` and `t' = t(τ')`, and `p - pos_y(λ) ∈ τ ∩ τ'`. A Penrose tiling is edge to
     edge, so `τ ∩ τ'` is a common face. Its vertices correspond to common labels (Lemma 3),
     so `p ∈ Fc(t, t')` and `[t, p] = [t', p]`.
   - A continuous bijection from a compact space onto a Hausdorff space is a homeomorphism.

**Lemma 4 (uniform local sections).** For every `q ∈ K`, some open set `U_q ∋ q` is mapped
by `dev` homeomorphically onto the open disc `B°(dev(q), 1)`.

*Proof.* Pick `t ∋ q` and a label `λ ∈ Lab(t)`, so `|dev(q) - pos_y(λ)| <= 2`. Let
`m_1 = M(3) <= m_*`, and let `s : G_λ(m_1) -> R_λ(m_1)` be the inverse of `dev`.
- `G_λ(m_1)` contains every tile of `Θ(x_λ) + pos_y(λ)` meeting `B(pos_y(λ), 3)`, together
  with the closed stars of all their vertices. So `B°(dev(q), 1) ⊂ G_λ(m_1)`.
- Put `U_q = s(B°(dev(q), 1))`. Then `q ∈ U_q`, since `t ∈ 𝒦_λ(0)` and `dev` is injective
  on `R_λ(m_1)`.
- **`U_q` is open in `K`.** Let `p ∈ U_q`.
  - Some tile of `R_λ(m_1)` containing `p` has a rhombus meeting `B(pos_y(λ), 3)`. Let `w`
    be one of its labels. By Lemma 3, `w` is at edge distance `<= M(3)` from `λ`.
  - Pick `w` to be a label of the smallest face containing `p`, so `p ∈ O(w)`.
  - Every tile containing `w` lies in `𝒦_λ(M(3)) = 𝒦_λ(m_1)`, so `O(w) ⊆ R_λ(m_1)`.
  - Then `O(w) ∩ dev^{-1}(B°(dev(q), 1))` is an open neighbourhood of `p` contained in
    `U_q`, because `dev` is injective on `R_λ(m_1)`.
- **Homeomorphism.** `dev|_{U_q}` is a restriction of a homeomorphism. ∎

**`K` is Hausdorff.** Let `q ≠ q'` be points of `K`.
- If `dev(q) ≠ dev(q')`, preimages of disjoint discs separate them.
- Suppose `dev(q) = dev(q') = z`, with `q ∈ ρ(t)`, `λ ∈ Lab(t)`, `q' ∈ ρ(t')` and
  `λ' ∈ Lab(t')`. We claim `U_q ∩ U_{q'} = ∅`.
  - Let `r ∈ U_q ∩ U_{q'}`. Then `r = [t_1, z_1] = [t_1', z_1]` with
    `t_1 ∈ 𝒦_λ(M(3))` and `t_1' ∈ 𝒦_{λ'}(M(3))`, both rhombi meeting `B(z, 1)`.
  - A label `w` of the smallest face of `ρ(t_1)` containing `z_1` is common to `t_1` and
    `t_1'`.
  - By Lemma 3, `w` is joined to `λ` and to `λ'` by `y`-adjacent paths of length
    `<= M(3)`. So `t' ∈ 𝒦_λ(2 M(3))`.
  - `2 M(3) <= m_*`, so `dev` is injective on `R_λ(2 M(3)) ∋ q, q'`. This contradicts
    `q ≠ q'`.

**Lemma 5 (covering).** Let `p : K -> C` be a local homeomorphism from a nonempty
Hausdorff space satisfying Lemma 4. Then `p` is a covering map onto `C`. If `K` is
connected, `p` is a homeomorphism.

*Proof.* Let `σ_q = (p|_{U_q})^{-1}`, defined on `B°(p(q), 1)`. Two such sections that
agree at one point of a convex common domain agree on all of it. The agreement set is
open since `p` is a local homeomorphism, and closed since `K` is Hausdorff.

Fix `b ∈ C`. The preimage of `B°(b, 1/2)` is the disjoint union of the sets
`W_e = σ_e(B°(b, 1/2))`, `e ∈ p^{-1}(b)`.
- **They cover.** Let `p(q) ∈ B°(b, 1/2)`, and put `e = σ_q(b)`. Then `σ_e` and `σ_q`
  agree at `b`, hence at `p(q)`, so `q = σ_e(p(q)) ∈ W_e`.
- **They are disjoint.** A common point makes `σ_e` and `σ_{e'}` agree, so `e = e'`.
- Each `W_e` is open and maps homeomorphically onto the disc.

So `p` is a covering over each disc. The fibre cardinality is locally constant, hence
constant, and nonzero. `C` is simply connected and locally path connected, so a connected
covering of `C` is a homeomorphism. ∎

**`K` is connected.**
- Every point of `K` lies in a tile, which is path connected to each of its labels.
- For `λ ∈ Λ` and `s ∈ S`, the vertex `c_y(s, λ) = ψ_{x_λ}(s)` of `Θ(x_λ)` has
  `|c_y(s, λ)| <= D`. It is a vertex of a tile meeting `B(0, D)`, so it is at edge distance
  `<= M(D) <= m_*` from `0`.
- The chart lemma turns such a path into a `y`-adjacent path from `λ` to
  `λ + ψ_{x_λ}^{-1}(c_y(s, λ)) = λ + s`. Adjacent labels are joined by an edge in `K`.
- `Λ` is generated by `S`.

**`dev` is a local homeomorphism.** This is Lemma 4. By Lemma 5, `dev : K -> C` is a
homeomorphism.

**Step 5 (the tiling and the identification).**

*The tiling.* Let `T = {ρ(t) : t ∈ 𝒦}`, with the decorations of the `ρ(t)`.
- **Cover.** `dev` is onto, and every point of `K` lies in a tile.
- **Disjoint interiors.** An interior point of `ρ(t)` is equivalent only to itself, and
  `dev` is injective.
- **Edge to edge.** Let `p ∈ ρ(t) ∩ ρ(t')`. Injectivity of `dev` gives
  `[t, p] = [t', p]`, so `p ∈ Fc(t, t')`. Hence `ρ(t) ∩ ρ(t') = Fc(t, t')`, which is a
  common face by Step 4, item 1.
- **Matching.** If that face is an edge, let `μ` be one of its labels.
  - By Claim B both tiles are produced at `μ`.
  - So `ρ(t) - pos_y(μ)` and `ρ(t') - pos_y(μ)` are adjacent tiles of `π_μ`, which is a
    patch of a genuine Penrose tiling.
  - Their arrows on the common edge match.

So `T` is a tiling of `C` by decorated unit rhombi with sides parallel to the lines
`e^{kπi/5} R`, edge to edge, with matching arrows. That is, `T` is a Penrose tiling
(I4). `0 = pos_y(0)` is a vertex of it. By (I3) and §2 there is a unique `x* ∈ X` with
`Θ(x*) = T`.

*(i) Local patches.* For every `λ ∈ Λ`, `pat_{r_0}(T - pos_y(λ)) = π_λ`.

*Proof.* Let `m_2 = M(r_0 + 1) <= m_*`.
- **`⊇`.** Let `τ` be a tile of `Θ(x_λ)` meeting `B(0, r_0)`. Then `τ ∈ 𝒢_λ(m_2)`, and
  `ρ(t(τ)) = τ + pos_y(λ) ∈ T` with the same decoration.
- **`⊆`.** Let `ρ(t) ∈ T` meet `B(pos_y(λ), r_0)`. Pick an interior point `z` of `ρ(t)`
  with `|z - pos_y(λ)| < r_0 + 1`.
  - `G_λ(m_2)` contains `B(pos_y(λ), r_0 + 1)`, since it contains every tile of
    `Θ(x_λ) + pos_y(λ)` meeting that disc. So `z = dev(p)` for some `p ∈ R_λ(m_2)`.
  - `dev` is injective and `z` is interior to `ρ(t)`, so `p = [t, z]`. Since `p` lies in
    a tile of `𝒦_λ(m_2)`, that tile is `t`.
  - By Lemma 3, `ρ(t) = τ + pos_y(λ)` for some tile `τ` of `Θ(x_λ)`, which meets
    `B(0, r_0)`.
- So the tiles of `T - pos_y(λ)` meeting `B(0, r_0)` are exactly those of
  `pat_{r_0}(Θ(x_λ)) = ℓ(x_λ) = π_λ`, with the same decorations. ∎

*(ii) Positions.* For every `λ ∈ Λ`, `ψ_{x*}(λ) = pos_y(λ)`.

*Proof.* By induction on word length. `ψ_{x*}(0) = 0 = pos_y(0)`. Suppose
`ψ_{x*}(λ) = pos_y(λ)`, and let `s ∈ S`.
- By Lemma 1.1, the induction hypothesis and (i),
  `pat_{r_0}(Θ(x* + λ)) = pat_{r_0}(T - pos_y(λ)) = π_λ`.
- So `c(s, x* + λ) = ĉ_s(π_λ) = c_y(s, λ)`.
- By Lemma 1.2, `ψ_{x*}(λ + s) = pos_y(λ) + c_y(s, λ) = pos_y(λ + s)`. ∎

*(iii) Conclusion.* For every `λ`,
`y(λ) = π_λ = pat_{r_0}(T - pos_y(λ)) = pat_{r_0}(Θ(x*) - ψ_{x*}(λ)) = ℓ(x* + λ)`.
So `y = y_{x*} ∈ Y`.

**Theorem, item 2.** `Y` is exactly the set of `y ∈ A^Λ` all of whose `B(N)`-windows occur
in `Y`, so `Y` is of finite type. ∎

## 5. Consequences for `penrose-derived-full-group-is-finitely-presented`

1. **Theorem G is silent.** `𝒫 ≅ [[Λ ~ X]] ≅ [[Λ ~ Y]]` (ChJN and Proposition 2), and
   `Λ ~ Y` is a free subshift action. By
   `fp-alternating-full-groups-of-free-subshifts-force-sft`, finite presentation of
   `D(𝒫)` would force `Y` to be of finite type, and it is. So no finite-type argument can
   show that `D(𝒫)` is not finitely presented. The negation needs an obstruction that
   sees more than the finite type of the subshift.
2. **The rational polytope exchange obstruction does not apply to torus models.**
   `fp-simple-groups-have-no-rational-polytope-exchange-action` needs facet directions
   that are rational with respect to the period lattice.
   - `Λ ~ X` is a polygon exchange of the torus `C/Lat`, with facets on the five
     directions `iζ^j R`.
   - **Proposition 6.** For every 2-dimensional `Q`-subspace `W ⊂ Q(ζ)`, some direction
     `iζ^j R` meets `W` only in `0`. So for every lattice of periods inside `Q(ζ)` at
     least one facet direction is irrational.
   - *Proof.* Suppose all five directions meet `W`. Put `u = ζ - ζ^4 ∈ iR`, so that
     `Q(ζ) ∩ iζ^j R = ζ^j u Q(√5)`.
     - `W` contains `a = u(p + q√5) ≠ 0` and `b = ζ u (r + s√5) ≠ 0`. These are
       `R`-independent, so `W = Q a + Q b`.
     - Take coordinates in the basis `1, ζ, ζ^2, ζ^3` of `Q(ζ)`. `W` meets
       `ζ^j u Q(√5)` if and only if `det[a, b, ζ^j u, ζ^j u√5] = 0`.
     - For `j = 2, 3, 4` these determinants are `10(pr + ps - qr - 5qs)`,
       `-20(ps - qr)` and `-10(pr - ps + qr - 5qs)`. They were computed exactly in
       `experiments/penrose-rational-directions-2026-09-16/allrational.py`.
     - All three vanish if and only if `ps = qr` and `pr = 5qs`.
     - If any of `p, q, r, s` is `0`, these equations force `a = 0` or `b = 0`. Otherwise
       `p/q = r/s = ρ` and `ρ^2 = 5`, which is impossible in `Q`. ∎
   - For ChJN's `Lat` the directions `j = 0, 1` are rational and `j = 2, 3, 4` are not
     (`rational_dirs.py`).
   - This does not exclude conjugate models of other kinds. It only shows that the
     obstruction cannot be applied to the natural models.
3. **Position in the landscape.** `Λ ~ Y` is a free minimal SFT over `Z^2 ⊕ Z/5`. That is
   the same structural class as Labbé's `Omega_U` over `Z^2`, whose derived full group is
   the live candidate `labbe-shift-derived-full-group-is-finitely-presented`. Deciding
   finite presentation of `D(𝒫)` is therefore at least as delicate as the Labbé problem.
   Neither is resolved here.

## 6. Weak points, for the referee

1. **(I3a), the vertex set determines the tiling.** We derive it from ChJN's assertion
   that `𝒯` is a Cantor set in the vertex-patch topology. For regular `ξ~` it can be
   checked directly on the pentagrid.
   - Two vertices `z, z + ζ^j` of `T_ξ~` have de Bruijn lifts differing by
     `e_j + m(1, 1, 1, 1, 1)`. The index constraint `Σ k_j ∈ {1, ..., 4}` forces `m = 0`.
   - The two pentagrid cells then differ only in the `j`-th strip, inside a common convex
     intersection of the other four strips, so they share an edge.
   - Hence the edge set, and so the tiles, are read off from the vertex set.
   - This check is not written out for singular `ξ~`, and arrows are not treated. A
     referee may prefer to import local derivability of the decorated tiling from the
     vertex set directly.
2. **(I3), the homeomorphism `V' ≅ 𝒯`.** ChJN state it as following from de Bruijn and
   give no proof. It is the standard local constancy of patches for a cut-and-project set
   with polygonal windows whose edges lie on the doubled lines. The de Bruijn papers were
   not fetched and are unverified here.
3. **(I5) at singular points.** The formula `s = Σ k_j ∈ {1, ..., 4}` for vertices of
   limit tilings `T_ξ~` is taken from ChJN lines 491--498.
4. **Step 4, the point-set topology of `K`.** It is written tersely: open stars, Hausdorff
   property, and the covering lemma. Every use of the charts is bounded by `m_*`, and
   `N` was chosen so that the chart lemma applies to paths of length `m_* + 2`. That
   bookkeeping is the second place to check.
5. **Constants.** `r_0`, `D` and `D'` exist by compactness but are not computed, so the
   window size `N` is not effective. Finite type does not need effectivity.
