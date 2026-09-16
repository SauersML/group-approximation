# Finite E_VC models restricted to commensurators (2026-09-16)

Lane z1-07-vc-counter, target `some-non-vc-group-has-a-finite-evc-model`. The results below are
necessary conditions on any witness for that claim. They add a characterization of groups
with a finite `E_VC` model. None of them decides the Juan-Pineda–Leary conjecture.

Nodes supported by this artifact:

- `finite-evc-model-restricts-to-commensurators` (Theorem 1)
- `finite-evc-iff-finite-efin-and-commensurator-models` (Theorem 2)
- `finite-evc-unimodular-weyl-groups-have-finite-efin` (Theorem 3)
- `finite-evc-positive-length-centralizers-have-finite-efin` (Theorem 4 and Corollaries 5, 6)

## 0. Conventions and elementary facts

**CW conventions.**

- A `G`-CW complex is a CW complex with a cellular `G`-action such that an element mapping an
  open cell to itself fixes it pointwise.
- For a point `x` in an open cell `σ` we have `G_x = G_σ`. If `y` lies in the closure of `σ`,
  then `G_σ <= G_y` by continuity.
- A `G`-CW complex is *finite* if it has finitely many `G`-orbits of cells.
- For a family `F` (closed under conjugation and subgroups), a `G`-CW complex `X` is a model for
  `E_F(G)` iff `X^H` is contractible for `H` in `F` and empty for `H` not in `F`
  (Lück–Weiermann, math/0702646, Section 1).
- `VC` and `FIN` are the families of virtually cyclic and of finite subgroups.

**Commensurability (Lück–Weiermann Definition 2.2).**

- For infinite virtually cyclic `V, W <= G`, write `V ~ W` iff `V ∩ W` is infinite.
- An infinite subgroup of an infinite virtually cyclic group has finite index: it meets a
  finite-index infinite cyclic subgroup nontrivially. So `V ~ W` iff `V ∩ W` has finite index
  in both.
- `~` is an equivalence relation. For transitivity: if `U ~ V ~ W`, then `U ∩ V ∩ W` has finite
  index in `V`, so it is infinite.
- `~` is conjugation invariant, and `H <= K` with `H` infinite implies `H ~ K`.
- Write `[C]` for the class of `C`.

**Commensurator and family.** For infinite virtually cyclic `C`:

- The commensurator is `N = N_G[C] = {g : gCg^{-1} ~ C}`. It is a subgroup and depends only on
  `[C]`.
- The family is `G[C] = {finite subgroups of N} ∪ {infinite K <= N virtually cyclic with
  K ~ C}`.
- `G[C]` is closed under `N`-conjugation and under subgroups, since an infinite subgroup of
  `K ~ C` is `~ C`.
- Every `K ~ C` lies in `N`: for `k` in `K`, `kCk^{-1} ~ kKk^{-1} = K ~ C`.

**Generalized index and modular homomorphism.**

- For mutually commensurable `A, B`, put `i(A,B) = [A : A∩B] / [B : A∩B]`, a positive rational.
- For any finite-index `E <= A ∩ B` we have `i(A,B) = [A:E]/[B:E]`. Using a common `E` gives
  `i(A,B) i(B,D) = i(A,D)`.
- `i(gAg^{-1}, gBg^{-1}) = i(A,B)`, and `i(A,B) = [A:B]` when `B <= A`.
- Define `Δ_C : N -> Q_{>0}^×` by `Δ_C(g) = i(gCg^{-1}, C)`. It is a homomorphism:
  `Δ(gh) = i(g(hCh^{-1})g^{-1}, gCg^{-1}) · i(gCg^{-1}, C) = Δ(h)Δ(g)`.
- `Δ_C` depends only on `[C]`: for `C' ~ C`, `i(gC'g^{-1}, C') = i(C',C) Δ_C(g) i(C,C')`.
- `Δ_C` is trivial on `N_G(C)`, on every `K ~ C` (because
  `i(kCk^{-1}, C) = i(kCk^{-1}, kKk^{-1}) i(K, C) = i(C,K) i(K,C) = 1`), and on torsion.
- Call `C` (or `N_G[C]`) *unimodular* if `Δ_C ≡ 1`.

**Finiteness facts used.**

- (F1) Brown's criterion: if a group acts on a contractible `G`-CW complex with finitely many
  orbits of cells and all cell stabilizers of type `F_infinity`, then the group has type
  `F_infinity`. K. S. Brown, *Finiteness properties of groups*, J. Pure Appl. Algebra 44
  (1987), Proposition 1.1. Recalled; the numbering was not re-fetched in this session.
- (F1') *Referee replacement for every use of (F1) below (2026-09-16).* Every application of
  (F1) in this artifact can be derived from the verified source (F5) instead. Let `Γ` act on a
  `Γ`-CW complex `Z` with finitely many orbits of cells, such that
  `𝒢 = {K <= Γ : Z^K nonempty}` consists of virtually cyclic groups and `Z^K` is contractible
  for every `K` in `𝒢`. Then:
  - `𝒢` is a family, and `Z` is a finite model for `E_𝒢(Γ)`.
  - A finite group `F` has a finite-type model for `EF`: the realization of the bar
    construction, with `F^{n+1}` `n`-simplices, freely permuted.
  - Proposition 5.1(ii) of math/0702646, in its "finite type" form ("The same is true if we
    replace 'finite' by 'of finite type' everywhere", checked in the arXiv source on
    2026-09-16), applied to `TR ⊆ FIN` on a virtually cyclic `V` with the finite model of (F2),
    gives a finite-type `EV`.
  - The same proposition applied to `TR ⊆ 𝒢` on `Γ` gives a finite-type `EΓ`, so `Γ` has type
    `F_infinity`.

  The uses are: `Γ = N_G[C]` with `Z = Y_C` (Theorem 1); `Γ = N_G(C)` with `Z = X^C`, where
  `Z^K = X^{KC}` (Theorem 3); and `Γ` a group with a finite `E_FIN` model (Theorem 4 and the
  corollaries). In each case the hypotheses hold by the stated fixed-set computations.
- (F2) Virtually cyclic groups have type `F_infinity`. They have finite 1-dimensional models for
  `E_FIN` (math/0702646, sentence before Corollary 5.4).
- (F3) `F_infinity` passes to finite-index subgroups and overgroups. A finite model for `E_FIN`
  restricts to a finite model on a finite-index subgroup.
- (F4) A finitely generated group has only finitely many subgroups of a given finite index
  `d`. They correspond to transitive actions on `d` points.
- (F5) Lück–Weiermann, arXiv:math/0702646, read from the PDF on 2026-09-16:
  - **Theorem 2.3**: the pushout construction of `E_G(G)` from `E_F(G)`, the
    `E_{F ∩ N_G[H]}(N_G[H])` and the `E_{G[H]}(N_G[H])`.
  - **Remark 2.5**: the maps exist and may be taken cellular, with one of them an inclusion,
    via mapping cylinders.
  - **Proposition 5.1(ii)**: if `F <= G` are families, `E_G(G)` has a finite model, and every
    `H` in `G` has a finite model for `E_{F∩H}(H)`, then `E_F(G)` has a finite model.
  - **Corollary 5.4(ii)**: a finite model for `E_VC G` gives a finite model for `E_FIN G`.
  - **Example 2.6**: `Z[1/p] ⋊_p Z`.

Throughout, `X` is a finite `G`-CW model for `E_VC G`. Every cell stabilizer `G_σ` is virtually
cyclic, since `X^{G_σ}` is nonempty.

## 1. Theorem 1 (restriction to commensurators)

**Theorem 1.** Let `X` be a finite model for `E_VC G`, let `C <= G` be infinite virtually
cyclic, and put `N = N_G[C]`. Let

`Y_C = {x in X : G_x ∩ C is infinite} = {x in X : G_x is infinite and G_x ~ C}`.

Then:

1. `Y_C` is an `N`-invariant subcomplex of `X`.
2. `Y_C` has at most as many `N`-orbits of cells as `X` has `G`-orbits of cells.
3. `Y_C` is a model for `E_{G[C]}(N)`.

Consequently:

- `N` has type `F_infinity`.
- `N` admits a finite model for `E_FIN N`.
- If `Δ_C` is nontrivial, then `N` surjects onto `Z`.

*Proof.*

(i) **Subcomplex.** The two descriptions of `Y_C` agree, because `G_x` is virtually cyclic.
Points of one open cell have one stabilizer, so `Y_C` is a union of open cells. If `σ` is in
`Y_C` and `y` lies in its closure, then `G_y ⊇ G_σ`. `G_y` is virtually cyclic and contains the
infinite group `G_σ`, so `G_y ~ G_σ ~ C` and `y` is in `Y_C`. Hence `Y_C` is a subcomplex.

(ii) **Invariance and isotropy.**

- For `n` in `N`: `G_{nx} = nG_xn^{-1} ~ nCn^{-1} ~ C`.
- For `x` in `Y_C`, every `g` in `G_x` satisfies `gCg^{-1} ~ gG_xg^{-1} = G_x ~ C`, so
  `G_x <= N`. Therefore `N_x = G_x`, an infinite member of `G[C]`.

(iii) **Finiteness.** Let `σ_1, ..., σ_k` represent the `G`-orbits of cells of `X`, with
`V_i = G_{σ_i}`. Suppose `gσ_i` and `g'σ_i` both lie in `Y_C`, and put `h = g'g^{-1}`. Then

`hCh^{-1} ~ h(gV_ig^{-1})h^{-1} = g'V_ig'^{-1} ~ C`,

so `h` is in `N` and `g'σ_i = h(gσ_i)`. Each `G`-orbit contributes at most one `N`-orbit of
cells to `Y_C`.

(iv) **Fixed sets of `H <= N` not in `G[C]`.** Such an `H` is infinite. If `x` is in `Y_C^H`,
then `H <= G_x`, and `H` is infinite inside the virtually cyclic group `G_x ~ C`. So `H` is
virtually cyclic with `H ~ C`, which means `H` is in `G[C]`. Hence `Y_C^H` is empty.

(v) **Infinite `H` in `G[C]`.** If `x` is in `X^H`, then `G_x ⊇ H` is virtually cyclic, and
`G_x ~ H ~ C`. So `Y_C^H = X^H`, which is contractible.

(vi) **Finite `H <= N`.** Let `D_H` be the set of virtually cyclic `D <= G` with `H <= D` and
`D ~ C` (in particular `D` is infinite).

- `Y_C^H` is the union of the `X^D` over `D` in `D_H`. For "contained in": if `x` is in
  `Y_C^H`, take `D = G_x`. For "contains": if `x` is in `X^D`, then `G_x ⊇ D ⊇ H`, and `G_x` is
  virtually cyclic and `~ D ~ C`.
- `D_H` is closed under finite intersections. `D ∩ D'` contains `H`, is virtually cyclic, and
  `D ∩ D' ∩ C` has finite index in `C`. Also `X^D ∪ X^{D'} ⊆ X^{D ∩ D'}`.
- A compact subset of `Y_C^H` lies in a finite subcomplex. That subcomplex lies in finitely
  many `X^{D_j}`, hence in the single contractible `X^{D_1 ∩ ... ∩ D_r}`, which is contained in
  `Y_C^H`. So every map of a sphere into `Y_C^H` is null-homotopic.
- `Y_C^H` is nonempty. Let `C_0 = <c>` have finite index in `C`, and put
  `E = ∩_{h in H} hC_0h^{-1}`. This is a finite intersection of pairwise commensurable infinite
  cyclic groups, because `H <= N`. So `E` is infinite cyclic, `E ~ C`, and `H` normalizes `E`.
  Then `D = HE` is a subgroup containing `E` with index at most `|H|`, so `D` is in `D_H` and
  `X^D` is nonempty.
- `Y_C^H` is a CW complex with all homotopy groups trivial, so it is contractible by Whitehead's
  theorem.

Taking `H = 1` shows `Y_C` is contractible. So `Y_C` is a finite model for `E_{G[C]}(N)`.

**Consequences.**

- `N` has type `F_infinity` by (F1') applied to `Z = Y_C`, whose nonempty fixed sets are those
  of members of `G[C]` and are contractible by (iv)–(vi).
- Every member of `G[C]` is virtually cyclic and has a finite model for `E_FIN` (F2). So
  Proposition 5.1(ii) of math/0702646, applied to `FIN ∩ N <= G[C]`, gives a finite model for
  `E_FIN N`.
- `Δ_C(N)` is a finitely generated subgroup of the free abelian group `Q_{>0}^×`. If it is
  nontrivial, it is free abelian of positive rank and surjects onto `Z`. ∎

## 2. Theorem 2 (characterization)

**Theorem 2.** A group `G` admits a finite model for `E_VC G` if and only if:

- (a) `G` admits a finite model for `E_FIN G`;
- (b) there are finitely many `G`-orbits, under conjugation, of commensurability classes of
  infinite virtually cyclic subgroups;
- (c) for each infinite virtually cyclic `C` (equivalently, for one `C` in each orbit of (b)),
  `N_G[C]` admits a finite model for `E_{G[C]}(N_G[C])`.

*Proof.*

**Forward.**

- (a) is Corollary 5.4(ii) of math/0702646.
- (b): let `σ_1, ..., σ_k` represent the cell orbits of `X`. Every infinite virtually cyclic
  `H` fixes a point `x`, so `H <= G_x = gG_{σ_i}g^{-1}` for some `g` and `i`, and
  `[H] = g[G_{σ_i}]g^{-1}`. There are at most `k` orbits of classes.
- (c) is Theorem 1. The equivalence in (c) holds because
  `N_G[gCg^{-1}] = gN_G[C]g^{-1}`, and conjugating a model gives a model.

**Reverse.** Use Theorem 2.3 of math/0702646 with `F = FIN`, `G = VC` and `~` commensurability.
Properties (2.1) hold, and `N_G[H]` and `G[H]` there are the groups above. Let `I` be the finite
set of representatives from (b), and write `N = N_G[C]` for each `C` in `I`.

- By (c), `N` has a finite model `Y` for `E_{G[C]}(N)`.
- By Proposition 5.1(ii) of math/0702646, `N` has a finite model `Z` for `E_FIN N`, because
  members of `G[C]` are virtually cyclic.
- Choose a cellular `G`-map `i : ∐_{C in I} G ×_N Z -> E_FIN G` and cellular `N`-maps
  `f : Z -> Y`. They exist by the universal property and equivariant cellular approximation
  (Remark 2.5).
- Replace `E_FIN G` by the mapping cylinder of `i`. It is a finite `G`-CW complex,
  `G`-homotopy equivalent to `E_FIN G`, and hence again a model, and `i` becomes an inclusion.
- The resulting pushout is a model for `E_VC G` (Theorem 2.3). Its cells are the cells of the
  target of `f` together with the cells of `cyl(i)` outside the image of `i`. All these
  complexes are finite, `G ×_N (finite N-complex)` is a finite `G`-complex, and `I` is finite.
  So the pushout is finite. ∎

## 3. Theorem 3 (unimodular Weyl groups)

**Theorem 3.** Let `G` have a finite model `X` for `E_VC G`. Let `C <= G` be infinite virtually
cyclic with `Δ_C ≡ 1` on `N_G[C]`. Then:

- the fixed set `X^C` has finitely many `N_G(C)`-orbits of cells;
- `N_G(C)` has type `F_infinity`;
- `X^C` is a finite model for `E_FIN(W_G C)`, where `W_G C = N_G(C)/C`.

If `C = <c>` is infinite cyclic, the same holds for the centralizer `Z_G(c)` and for
`Z_G(c)/<c>`, which have index at most 2 in `N_G(C)` and in `W_G C`.

*Proof.*

**Cells of `X^C` lie in `Y_C`.** Let `N = N_G[C]`, and let `τ_1, ..., τ_m` represent the
`N`-orbits of cells of `Y_C` (Theorem 1), with `W_j = G_{τ_j} = N_{τ_j}`. A cell `σ` of `X^C`
has `C <= G_σ`, so `G_σ ~ C` and `σ` is in `Y_C`.

**Parametrizing the cells.**

- `σ = nτ_j` with `C <= nW_jn^{-1}` iff `n` is in `T_j = {n in N : n^{-1}Cn <= W_j}`.
- `T_j` is stable under left multiplication by `N_G(C)` and right multiplication by `W_j`.
- `nW_j ↦ nτ_j` is a bijection from `T_j/W_j` onto the cells of `X^C` in `Nτ_j`.
- So the `N_G(C)`-orbits of these cells correspond to the double cosets `N_G(C)\T_j/W_j`.

**Injecting double cosets.** Send `N_G(C) n W_j` to the `W_j`-conjugacy class of the subgroup
`n^{-1}Cn <= W_j`.

- It is well defined: `(mnw)^{-1}C(mnw) = w^{-1}(n^{-1}Cn)w` for `m` in `N_G(C)` and `w` in `W_j`.
- It is injective. Suppose `n^{-1}Cn = w^{-1}n'^{-1}Cn'w`. Then `m = n'wn^{-1}` normalizes `C`,
  and `n' = mnw^{-1}`.

**Constant index.** `n^{-1}Cn <= W_j`, and both are commensurable with `C`, so

`[W_j : n^{-1}Cn] = i(W_j, C) · i(C, n^{-1}Cn) = i(W_j, C) · Δ_C(n)`,

using `i(C, n^{-1}Cn) = i(nCn^{-1}, C)`. With `Δ_C ≡ 1` the index is the constant
`i(W_j, C)`. `W_j` is finitely generated, so by (F4) there are finitely many such subgroups,
hence finitely many double cosets and finitely many `N_G(C)`-orbits of cells in `X^C`.

**Conclusions.**

- `X^C` is contractible, since `C` is in `VC`. Its stabilizers `G_σ ∩ N_G(C)` are virtually
  cyclic, so `N_G(C)` has type `F_infinity` by (F1') with `Z = X^C`: for `K <= N_G(C)`,
  `(X^C)^K = X^{KC}` is nonempty only if `KC` (hence `K`) is virtually cyclic, and is then
  contractible.
- `C` acts trivially on `X^C`, so `W = W_G C` acts, cellularly and rigidly.
- For `L <= W` with preimage `L~ <= N_G(C)`, `(X^C)^L = X^{L~}`. If `L` is finite, `L~` is a
  finite extension of `C`, hence virtually cyclic, and the fixed set is contractible. If `L` is
  infinite, `C` has infinite index in `L~`, so `L~` is not virtually cyclic and the fixed set
  is empty.
- Hence `X^C` is a finite model for `E_FIN W`.
- For `C = <c>`, `Z_G(c)` has index at most 2 in `N_G(C)`, and (F3) applies. ∎

**Remark (where unimodularity enters).** Without `Δ_C ≡ 1` the same computation shows that the
cells of `X^C` in `Nτ_j` have index `i(W_j,C) Δ_C(n)`. This can be unbounded; see Section 5.

## 4. Theorem 4 (elements of positive length)

A *homogeneous length* on `G` is a function `ℓ : G -> [0, ∞)` that is conjugation invariant and
satisfies `ℓ(g^n) = |n| ℓ(g)`. Examples:

- `|φ|` for a homomorphism `φ : G -> R`;
- `|ψ|` for a homogeneous quasimorphism `ψ`;
- the stable translation length `lim d(x, g^n x)/n` of an isometric action.

**Theorem 4.** Let `G` have a finite model for `E_VC G`, let `ℓ` be a homogeneous length, and let
`ℓ(g) > 0`. Then:

- (i) `Δ_{<g>} ≡ 1`, and `N_G[<g>] = N_G(<g^M>)` for some `M >= 1`;
- (ii) for every `k >= 1`, `Z_G(g^k)` has type `F_infinity`, and `Z_G(g^k)/<g^k>` admits a
  finite model for `E_FIN`.

*Proof.*

- `g` has infinite order, because `ℓ(g^n) = 0` whenever `g^n = 1`.
- Let `y` be in `N_G[<g>]`. The group `y<g>y^{-1} ∩ <g>` is infinite cyclic. As a subgroup of
  `y<g>y^{-1}` it is generated by some `yg^ay^{-1}`, and as a subgroup of `<g>` by some `g^b`,
  with `a, b != 0`. Hence `yg^ay^{-1} = g^{±b}`.
- Conjugation invariance and homogeneity give `|a|ℓ(g) = |b|ℓ(g)`, so `|a| = |b|`. Then
  `Δ(y) = [y<g>y^{-1} : E]/[<g> : E] = |a|/|b| = 1`, and `y` is in `N_G(<g^{|a|}>)`.
- So `N_G[<g>]` is the directed union of the subgroups `N_G(<g^a>)`, `a >= 1`, ordered by
  divisibility. It is finitely generated by Theorem 1, so it equals one of them.
- Since `ℓ(g^k) = kℓ(g) > 0`, Theorem 3 applies to `C = <g^k>`. ∎

**Corollary 5 (products with Z).** If `G = Q × Z` has a finite model for `E_VC G`, then for
every `q` in `Q`, the centralizer `Z_Q(q)` has type `F_infinity` and admits a finite model for
`E_FIN`.

*Proof.*

- Take `g = (q, 1)` and `φ` the projection to `Z`. Then `Z_G(g) = Z_Q(q) × Z`.
- The map `(x, m) ↦ x q^{-m}` is a homomorphism on `Z_Q(q) × Z`, since `x` commutes with `q`.
  It is onto `Z_Q(q)`, with kernel `<(q,1)>`.
- So `Z_G(g)/<g> ≅ Z_Q(q)`, and Theorem 4(ii) applies. ∎

**Corollary 6 (ascending HNN extensions).** Let `θ : H -> H` be an injective endomorphism, and
let `G = <H, t | t x t^{-1} = θ(x), x in H>` have a finite model for `E_VC G`. Then:

- (a) for every `h` in `H`, `Fix(ι_h ∘ θ) = {x in H : hθ(x)h^{-1} = x}` has type `F_infinity` and
  admits a finite model for `E_FIN`;
- (b) the subgroup of `θ`-periodic points is `Per(θ) = ∪_a Fix(θ^a) = Fix(θ^M)` for some
  `M >= 1`, and it has type `F_infinity`.

*Proof.* Let `φ : G -> Z` send `t ↦ 1` and `H ↦ 0`, with kernel `K = ∪_{i>=0} t^{-i}Ht^i`.

(a)

- Put `g = ht`. Conjugation by `g` restricts to `ψ(x) = hθ~(x)h^{-1}` on `K`, where
  `θ~ = ι_t|_K` extends `θ`.
- Since `tHt^{-1} <= H`, we have `H <= t^{-(i-1)}Ht^{i-1}`. Hence
  `ψ(t^{-i}Ht^i) <= t^{-(i-1)}Ht^{i-1}` for `i >= 1`, and `ψ(H) <= H`.
- A `ψ`-fixed `k` in `t^{-i}Ht^i` equals `ψ^i(k)`, which lies in `H`. So
  `Fix_K(ψ) = Fix(ι_h∘θ)`.
- Every element of `G` is uniquely `k g^m` with `k` in `K`, so
  `Z_G(g) = Fix_K(ψ) × <g>` and `Z_G(g)/<g> ≅ Fix(ι_h∘θ)`.
- Apply Theorem 4(ii) with `ℓ = |φ|`.

(b)

- `φ` forces `yt^ay^{-1} = t^b` to have `a = b`. So `N_G[<t>] = ∪_a Z_G(t^a)`.
- `Z_G(t^a) = Fix_K(θ~^a) ⋊ <t>`, since `kt^m` centralizes `t^a` iff `θ~^a(k) = k`.
- `Fix_K(θ~^a) = Fix(θ^a)`. A `θ~^a`-fixed `k` in `t^{-i}Ht^i` equals `θ~^{ai}(k)`, and
  `θ~^{ai}(t^{-i}Ht^i) = t^{(a-1)i}Ht^{-(a-1)i} <= H`. Hence `N_G[<t>] = Per(θ) ⋊ <t>`.
- By Theorem 4(i), `N_G[<t>] = N_G(<t^M>) = Z_G(t^M)` for some `M`. So `Per(θ) = Fix(θ^M)`.
- `Fix(θ^M)` embeds with index `M` in `Z_G(t^M)/<t^M>`, which has type `F_infinity` by
  Theorem 4(ii); apply (F3). ∎

## 5. Sharpness: the commensurator data alone do not force unimodularity

Let `G = Z[1/p] ⋊_p Z = BS(1,p)` with `p >= 2`, and `C = <1> <= Z[1/p]`. This is Example 2.6 of
math/0702646, where `N_G[C] = G` but `N_G(V) = Z[1/p]` for `V` in `[C]`.

**The model and the modular homomorphism.**

- Let `T` be the Bass–Serre tree of `<a, t | tat^{-1} = a^p>`. It is a finite `G`-CW complex
  with one vertex orbit and one edge orbit, and every stabilizer is an infinite cyclic subgroup
  of `Z[1/p]`.
- Every infinite cyclic subgroup of `Z[1/p]` fixes a vertex, and fixed trees are subtrees. A
  subgroup fixing a vertex is `~ C`. Hence `T` is a finite model for `E_{G[C]}(G)`.
- `Δ_C(t) = i(<p>, <1>) = 1/p`.

**The fixed set of `C`.**

- `T^C` consists of the vertices `x t^k v_0` with `k <= 0`.
- `N_G(C) = Z[1/p]` is not finitely generated.
- The `N_G(C)`-orbits of vertices of `T^C` are indexed by `k <= 0`, and the index
  `[G_{t^k v_0} : C] = p^{-k}` is unbounded.

So the hypothesis `Δ_C ≡ 1` in Theorem 3 cannot be dropped in any argument that only uses the
pair `(N_G[C], Y_C)`. This group has no finite `E_VC` model: it fails BVC, by vPW 1607.03790,
Proposition 1.12.

## 6. Remarks and an open question

- **Few conjugacy classes.** Let `G` be torsion-free with finitely many conjugacy classes, and
  let `c != 1`. Among `c, c^2, c^3, ...` two powers are conjugate, say `yc^ay^{-1} = c^b` with
  `1 <= a < b`, so `Δ_{<c>}(y) = a/b != 1`. Every such commensurator is non-unimodular, and
  Theorems 3 and 4 give nothing. If such a group had a finite `E_VC` model, Theorem 1 would
  still force every `N_G[<c>]` to have type `F_infinity`, a finite `E_FIN` model, and a
  surjection onto `Z`.
- **Open question.** If `G` has a finite `E_VC` model, is `N_G[C]` unimodular for every infinite
  virtually cyclic `C`? Juan-Pineda–Leary predicts yes, since virtually cyclic groups are
  unimodular. A yes would have two consequences:
  - By Theorem 3, every centralizer `Z_G(c)` of an infinite-order element would have type
    `F_infinity`, and `Z_G(c)/<c>` would have a finite `E_FIN` model. This implies the extra
    hypothesis, type `FP_infinity` for these centralizers, of Kochloukova–Martínez-Pérez–Nucinkis
    (arXiv:0903.4079, abstract).
  - No nontrivial torsion-free group with finitely many conjugacy classes would have a finite
    `E_VC` model.

  By Section 5, a proof would have to use data outside a single commensurability class.

## Sources

- W. Lück, M. Weiermann, *On the classifying space of the family of virtually cyclic subgroups*,
  arXiv:math/0702646. PDF text read 2026-09-16: Definition 2.2, Theorem 2.3, Remark 2.5,
  Example 2.6, Proposition 5.1, Corollary 5.4.
- T. von Puttkamer, X. Wu, arXiv:1607.03790v2, Proposition 1.1 and Proposition 1.12 (read
  2026-09-13 by this lane, re-read 2026-09-16), and arXiv:1807.10095 (text read 2026-09-16, no
  commensurator-restriction statement found).
- D. Kochloukova, C. Martínez-Pérez, B. Nucinkis, arXiv:0903.4079v2. Abstract and introduction
  read 2026-09-16: centralizers are an extra hypothesis there.
- D. Degrijse, N. Petrosyan, arXiv:1108.6279. Text read 2026-09-16: commensurators are used for
  dimension bounds only.
- K. S. Brown, J. Pure Appl. Algebra 44 (1987). Recalled, not re-fetched; every use is
  replaced by the derivation (F1') from math/0702646, Proposition 5.1(ii).
- D. Juan-Pineda, I. Leary, Contemp. Math. 407 (2006). Not accessible in this session;
  unverified whether Theorems 1–4 appear there.
- Novelty: Theorems 1, 3 and 4 were not found in the sources read. They are elementary and may
  be folklore.
