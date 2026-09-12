# Level-factoring and HNN models of the ternary Leavitt unit group

Lane `w4-char3-construct`, 2026-09-12. This is the construction side of the open gate
`ternary-leavitt-units-have-a-nontrivial-char-three-rank-model`. It supports:
- `char-three-level-factoring-models-of-leavitt-units-are-trivial` (Section 1);
- `level-unit-hnn-extensions-have-anti-central-rank-models` (Section 2).

## 0. Setting

- `R = L_(F_3)(1,2)`, `G = R^x`, `z = −1`, `PG = G/<z>`, and `ι(g) = s0 g t0 + s1 t1`.
- Rank models are homomorphisms into `M^x`, where `M = prod_ω M_(n_k)(k_k) / ker ρ` over fields `k_k` of
  characteristic three. See `research/artifacts/ternary-leavitt-char-three-rank-model-gate-2026-09-12.md`,
  Section 0.
- **Level unit group.**
  - `L_j = GL_(2^j)(F_3)` embeds in `G` by `a -> Σ_(|α|=|β|=j) a_(αβ) s_α t_β`.
  - Since `s_α t_β = s_(α0) t_(β0) + s_(α1) t_(β1)`, these embeddings are compatible with
    `L_j -> L_(j+1)`, `a -> a ⊗ 1_2`.
  - Put `L = ∪_j L_j`, a locally finite subgroup of `G`. It contains `z`, the signed diagonal `E`
    (each `τ_C` lies in `L_j` once `j` bounds the depth of `C`), and the same-depth permutations in `V`.
- **Level-factoring model.** This is the architecture of
  `research/artifacts/el3-rank-model-compressor-extension-2026-09-12.md`, Section 0, now over `F_3`:
  `σ = lim_ω π_k ∘ τ_k`, with set maps `τ_k : G -> GL_(m_k)(F_3)`, `m_k >= 4`, and representations
  `π_k : GL_(m_k)(F_3) -> GL_(n_k)(k_k)`.
- **Transvection displacement.** `d_k = rk(π_k(t) − 1)/n_k`. All transvections of `GL_m(F_3)` with
  `m >= 2` are conjugate, so `d_k` does not depend on `t`.

## 1. Level-factoring models are trivial in characteristic three

Remark 6 of the characteristic-two artifact confines relator errors to the centre over odd fields, and
records that central errors survive for `G`. They do not: central errors give an embedding of `G` or
`PG` into an algebraic ultraproduct of finite groups, and both groups are nonsofic.

**Lemma 1.1 (displacement sources).**
- (a) If `π_k` has a projective summand of normalized dimension `>= α`, then `d_k >= 2α/3`.
- (b) If `τ_k(g_0)` is a transvection for a fixed `g_0` with `σ(g_0) != 1`, then
  `lim_ω d_k = rk(σ(g_0) − 1) > 0`.

*Proof.*
- (a) A transvection has order three. A projective module restricted to `<t>` is free, so `t − 1` has
  rank `2/3` of its dimension there.
- (b) `rk(π_k(τ_k(g_0)) − 1)/n_k = d_k`. QED

**Lemma 1.2 (amplification).** In every representation `π`, `rk(π([x,u]) − 1) <= 2 rk(π(x) − 1)`.
This is Lemma 2 of the characteristic-two artifact, and its proof does not use the field.

**Lemma 1.3 (non-central commutators reach a transvection).** Let `m >= 4` and let `x ∈ GL_m(F_3)` be
non-central. Then there are transvections `u, u''` such that `[x,u]` or `[[x,u],u'']` is a transvection.
So `rk(π(x) − 1) >= rk(π(t) − 1)/4` in every representation `π` and for every transvection `t`.

*Proof.* A matrix for which every vector is an eigenvector is scalar, so some `v` has `xv ∉ F_3 v`.
1. **First commutator.**
   - Choose `φ != 0` vanishing on `v, xv, x^(−1)v`; `m >= 4` allows this.
   - Put `u = 1 + v⊗φ`, `ψ = φ∘x^(−1)`, `A = xv⊗ψ` and `B = v⊗φ`.
   - `ψ(v) = 0` and `φ(xv) = 0` give `A^2 = B^2 = AB = BA = 0`.
   - `x u x^(−1) = 1 + A` and `u^(−1) = 1 − B`, so `[x,u] = 1 + N` with `N = A − B` and `N^2 = 0`.
   - `N != 0` because `xv, v` are independent and `φ, ψ != 0`. So `rk N ∈ {1, 2}`.
2. **Second commutator.** If `rk N = 2`, write `N = a⊗α + b⊗β` with `a, b` independent and `α, β`
   independent.
   - Take `w` with `α(w) = 1`, so `Nw != 0`.
   - Take `χ != 0` vanishing on `a, b, w`, and put `u'' = 1 + w⊗χ`.
   - `χ∘N = 0`, so `(1+N) u'' (1+N)^(−1) = 1 + (w + Nw)⊗χ`.
   - `χ(w) = 0`, so `[1+N, u''] = 1 + Nw⊗χ`, a transvection.
3. Apply Lemma 1.2 once or twice, using that all transvections are conjugate. QED

**Theorem 1.4.** Let `σ = lim_ω π_k ∘ τ_k` be a level-factoring characteristic-three rank model of `G`
with `lim_ω d_k > 0`. Then `σ` is trivial. The same holds for level-factoring models of `PG`.

*Proof.*
1. **Make it injective.** Suppose `σ` is nontrivial. Then `σ' = σ∘ι` is injective
   (`ternary-leavitt-rank-models-move-z-iff-nontrivial`, (2) ⟹ (3)). It is level-factoring with
   `τ'_k = τ_k∘ι` and the same `π_k`, hence the same `d_k`.
2. **Errors are central.**
   - Fix a finite `F ⊆ G`. For `g, h ∈ F` put `e_k = τ'_k(gh)^(−1) τ'_k(g) τ'_k(h)`.
   - Since `π_k` is a homomorphism, `rk(π_k(τ'_k(g)) π_k(τ'_k(h)) − π_k(τ'_k(gh))) = rk(π_k(e_k) − 1)`.
     That is `o(n_k)` along `ω`, because `σ'` is multiplicative.
   - If `e_k` were non-central on an `ω`-large set, Lemma 1.3 would give `rk(π_k(e_k) − 1) >= d_k n_k/4`
     there, which is a contradiction. So `e_k ∈ {±1}` for `ω`-almost all `k`.
3. **A homomorphism into finite groups.** Let `τ̄_k` be `τ'_k` followed by `GL_(m_k)(F_3) -> PGL_(m_k)(F_3)`.
   By step 2, `Φ = [τ̄_k]_ω : G -> prod_ω PGL_(m_k)(F_3)` is a homomorphism into the algebraic
   ultraproduct.
4. **Its kernel is central.**
   - Suppose `Φ(w) = 1`. Then `τ'_k(w) = ±1` for `ω`-almost all `k`. That is central in `GL_(m_k)(F_3)`,
     so `π_k(τ'_k(w))` commutes with every `π_k(τ'_k(g))`.
   - Hence `σ'(w)` commutes with `σ'(G)`. So `σ'([w,g]) = 1`, and `[w,g] = 1` for all `g` by injectivity.
   - So `w ∈ Z(G)`. The image of `Z(G)` in `PG` is a central normal subgroup of the simple nonabelian
     group `PG` (`odd-leavitt-unit-groups-mod-scalars-are-fp-simple`), hence trivial. So `Z(G) = <z>`.
5. **Contradiction.**
   - `Q = G/ker Φ` is `G` or `PG`, and it embeds in an algebraic ultraproduct of finite groups.
   - Every countable group that embeds in such an ultraproduct is sofic: each finite subset maps
     injectively and partially multiplicatively into a finite group, and left multiplication there is a
     sofic approximation.
   - But `G` is nonsofic (`d-ary-leavitt-groups-nonsofic-over-finite-fields`) and `PG` is nonsofic
     (`projective-leavitt-unit-groups-mod-scalars-are-nonsofic`).
6. **`PG`.** A level-factoring model of `PG`, composed with `G -> PG`, is a level-factoring model of `G`
   with the same `π_k`. It is nontrivial if the model of `PG` is. QED

**Corollary 1.5 (what is excluded).** For `G_3` and for `PG`:
- **(a)** every natural level assignment sending a fixed `g_0` with `σ(g_0) != 1` to a transvection
  (Lemma 1.1(b));
- **(b)** every level-factoring model whose `π_k` has projective share bounded below, whatever `τ_k` does
  (Lemma 1.1(a)). This covers Steinberg modules, projective indecomposables, and free and twisted
  regular modules;
- **(c)** central relator errors. The odd-characteristic remark of the characteristic-two artifact left
  them open; they are fatal here.

**Survivors.**
- The displacement `d_k -> 0` at the level the model factors through.
- Or the model does not factor through level groups at all.
- In particular, any extension of the twisted regular tower of Section 2 to all of `G` must represent
  some element at positive rank distance from the image of the level representation.

**Remark 1.6 (why nonsoficity enters).**
- **Characteristic two:** the conclusion came from `R^x` being finitely presented, infinite and
  simple, hence not LEF.
- **Characteristic three:** the kernel of `Φ` can be `<z>`, so both `G` and `PG` must be non-LEF.
- **Sources:** nonsoficity of both is on main. For `PG`, finite presentation and simplicity also suffice.

## 2. The twisted regular tower and single-letter partial conjugations

**Theorem 2.1 (twisted regular tower).** Let `ε₋ = (1 − [z])/2`, a central idempotent of `F_3[L_j]`. Put
`V_j = F_3[L_j] ε₋`, of dimension `n_j = |L_j|/2`. For `a ∈ L_j`, let `σ_j(a)` be left multiplication by
`[a]` on `V_j`, and put `σ_j(a) = 1` for `a ∉ L_j`.
- Then `σ_reg = lim_ω σ_j : L -> M^x` is an injective anti-central homomorphism.
- For every finite subgroup `Γ ∋ z` of `L` and every `j` with `Γ ⊆ L_j`, `V_j` is a free
  `F_3[Γ]ε₋`-module of rank `[L_j : Γ]`.

*Proof.*
- **Homomorphism.** For `a, b ∈ L_(j_0)`, `σ_j(a) σ_j(b) = σ_j(ab)` for every `j >= j_0`, because the level
  embeddings are compatible.
- **Anti-central.** `σ_j(z) = −1` on `V_j`.
- **Freeness.** `F_3[L_j] = ⊕_(c ∈ Γ\L_j) F_3[Γ] c` as left `F_3[Γ]`-modules, and `ε₋` is central.
- **Injectivity.**
  - `σ(z) − 1 = −2` is invertible.
  - If `a ∉ <z>`, put `Γ = <a, z>`. Since `[a]ε₋ != ε₋`, the operator `[a] − 1` has some rank `r >= 1` on
    `F_3[Γ]ε₋`.
  - Freeness then gives normalized rank `2r/|Γ|` at every stage `j`. QED

**Remark 2.2.**
- **Haar law.** `E ⊆ L`, and freeness over the finite tori is exactly the Haar law of
  `anti-central-rank-models-see-haar-measure-on-signed-diagonal`. On every finite subgroup the statistics
  are those of the twisted regular representation.
- **Level-factoring.** `σ_reg` is level-factoring on `L`, with `τ_j` the inclusion and projective share
  one. So by Theorem 1.4 it has no extension to `G` that is level-factoring on all of `G`.

**Theorem 2.3 (single-letter partial conjugations).** For `g ∈ G` put `B_g = {a ∈ L : g a g^(−1) ∈ L}`
and `φ_g(a) = g a g^(−1)`. There is `X_g ∈ M^x` with `X_g σ_reg(a) X_g^(−1) = σ_reg(φ_g(a))` for every
`a ∈ B_g`.

*Proof.*
1. **The domain.** `B_g` is a subgroup of `L` containing `z`, and `φ_g : B_g -> L` is an injective
   homomorphism fixing `z`.
2. **A finite exhaustion.** Put `Γ_i = B_g ∩ L_i`. These are finite and increasing, with union `B_g`.
   - Let `c(i)` be the least level containing `Γ_i ∪ φ_g(Γ_i)`.
   - Put `i(j) = max{i <= j : c(i) <= j}`, or `0` if there is none. It is nondecreasing and tends to
     infinity.
3. **Exact intertwiners at each stage.** Let `i = i(j) >= 1`.
   - `V_j` is a free `F_3[Γ_i]ε₋`-module of rank `[L_j : Γ_i]` through `σ_j`.
   - It is also free of the same rank through `a -> σ_j(φ_g(a))`, since `φ_g(Γ_i) ⊆ L_j` has the same
     order and contains `z`.
   - Free modules of equal rank are isomorphic, so some `X_j ∈ GL(V_j)` has
     `X_j σ_j(a) = σ_j(φ_g(a)) X_j` for all `a ∈ Γ_i`. Put `X_j = 1` when `i(j) = 0`.
4. **The limit.** A fixed `a ∈ B_g` lies in `Γ_(i(j))` for `ω`-almost all `j`. So `X_g = [X_j]_ω` works,
   with inverse `[X_j^(−1)]_ω`. QED

**Corollary 2.4 (HNN extensions).** Let `I ⊆ G` be countable, and put
`Ĝ_I = <L, t_g (g ∈ I) | t_g a t_g^(−1) = φ_g(a) for a ∈ B_g>`.
- Then `σ_reg` extends to `Ĝ_I` by `t_g -> X_g`, with the `X_g` chosen independently.
- The map `Ĝ_I -> G`, `t_g -> g`, is a homomorphism, and it is onto for `I = G`.

**Remark 2.5 (torsion letters).** Suppose `g^n = 1` and `B_g` is the union of an increasing sequence of
`g`-invariant finite subgroups `Γ_i`. Then the letter keeps its order.
- **Size.** `n` divides `[L_j : Γ_i]` for large `j`, because the order of `GL_(2^j)(F_3)` eventually
  contains every fixed prime power.
- **Transport.** So `V_j` restricted to `Γ_i` is isomorphic to the restriction of a free
  `F_3[Γ_i ⋊ <g>]ε₋`-module. Transporting the action of `g` gives `X_j` with `X_j^n = 1` that intertwines
  `φ_g` on `Γ_i`.
- **Example.** The Thompson three-cycle `[0] -> [10] -> [11] -> [0]`. Its domain is the block group of
  the three cylinders, exhausted by the `g`-invariant block groups with equal suffix length in each block.

**Consequence 2.6 (for the "no" direction).**
- **What holds.** Every relation of `G` that follows from the relations of `L`, single-letter partial
  conjugations, and orders of torsion letters as in Remark 2.5, holds in an anti-central model injective
  on `L`.
- **What a proof needs.** A proof that every characteristic-three rank model of `G` is trivial must use
  a relation of `G` that fails in `Ĝ_G`. Such a relation involves two or more letters outside `L`, with
  intermediate products outside `L`. Examples:
  - the multiplication table of `V` on depth-changing elements, `t_g t_h = t_(gh)`;
  - commutation of disjointly supported depth-changing elements of `V`;
  - Steinberg commutators of two non-level root elements, such as `[x_12(t0), x_23(s0)] = x_13(1)` for
    the compressor pair. Neither factor nor the product lies in `L`.
- **Family R4.** The rank-four assembly uses relations of the third kind.

## 3. Where the construction stops

- **Outside the level image.** Depth-changing letters must be represented away from the level
  representation (Theorem 1.4 with Remark 2.2).
- **The coherence cocycle.**
  - For `g, h ∈ G`, `c(g,h) = X_g X_h X_(gh)^(−1)` commutes with `σ_reg(B_(g,h))`, where
    `B_(g,h) = B_h ∩ φ_h^(−1)(B_g)`.
  - Each `X_g` is unique up to the commutant of `σ_reg(B_g)`.
  - A model of `G` extending `σ_reg` is the same thing as a commutant correction of the intertwiners that
    satisfies every relation of `G`. This records the shape of the remaining freedom. It is a
    restatement, not a reduction.
- **Locality via Fock space: an idea with a gap.**
  - **The seed.** `Λ^odd(F_3^(2^j))` carries the exact Haar law on the depth-`j` torus at the minimal
    dimension `2^(2^j − 1)`.
  - **Locality.** `Λ(U ⊕ U') = Λ(U) ⊗ Λ(U')` turns clopen partitions into tensor factors. A letter
    supported on a clopen `A` could then act on the `A`-factor. Disjointly supported letters would commute
    automatically, as even operators on different factors.
  - **The gap.** Intertwiners need the block restrictions `⊗_i Λ(U)^(⊗ m_i)` and `⊗_i Λ(U)^(⊗ m'_i)`, with
    exponents that differ by depth, to be rank-close after conjugation.
    - For elements of order prime to three the characters decay, so they are.
    - For 3-subgroups this needs the non-projective part of `Λ(U)^(⊗m)` to have vanishing proportion. That
      is not proved here.
  - **Level images are excluded anyway.** A Fock extension whose letters lie in `Λ(GL)` would be
    level-factoring with positive displacement, which Theorem 1.4 excludes.
