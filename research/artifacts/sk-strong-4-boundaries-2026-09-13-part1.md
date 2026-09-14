# sk-strong-4 part 1: topological freeness is the exact hypothesis for the note's proof

Lane `sk-strong-4`, 2026-09-13. All results below are proved here in full; none is reviewed.

## 0. What this corrects
`finite-model-subshift-elementary-groups-simple-kazhdan-lef` (sk-general-actions-a) ends with
"Topological freeness is not enough for the tower partition; for that case use
`steinberg-elementary-groups-are-simple-mod-centre`." The first half is right: a point with a
nontrivial stabilizer has no small clopen neighborhood, so `X` need not partition into small sets.
The conclusion drawn from it is too weak. The note's argument never needs a partition. It needs
small clopen sets inside every nonempty open set, and that is available exactly under topological
freeness.

## 1. Setting and notation
`Γ` is a countable group acting by homeomorphisms on a compact Hausdorff zero-dimensional space
`X` (a subshift, or any Cantor system; finite `X` is allowed). `k` is a field, `LC(X,k)` the ring
of locally constant functions, `e_U` the indicator of a clopen `U`, and
`R = LC(X,k) ⋊ Γ = ⊕_{γ∈Γ} LC(X,k) u_γ`, with `u_γ f u_γ^{-1} = f∘γ^{-1}`, so `u_γ e_U u_γ^{-1} = e_{γU}`.
Coefficients are unique: `r = Σ_γ f_γ u_γ` with finitely many `f_γ ≠ 0`. Multiplication is
`(f u_α)(f' u_β) = f (f'∘α^{-1}) u_{αβ}`.

`Fix(γ) = {x : γx = x}`, a closed set. The action is **topologically free** if `Fix(γ)` has empty
interior for every `γ ≠ e`; **free** if `Fix(γ) = ∅` for every `γ ≠ e`; **minimal** if the only
closed invariant sets are `∅` and `X`. For finite `F ⊆ Γ`, a clopen `V` is **`F`-free** if
`γV ∩ V = ∅` for every `γ ∈ F \ {e}`.

`E_{ij}` is the matrix unit, `e_{ij}(r) = I_n + rE_{ij}` for `i ≠ j`, `EL_n(R) = ⟨e_{ij}(r)⟩`, and
`EL_n(R,I)` is the normal closure in `EL_n(R)` of `{e_{ij}(a) : a ∈ I}` for an ideal `I`.

## 2. The tower lemma, and why it is exactly topological freeness

**Lemma 1.** The following are equivalent.
1. The action is topologically free.
2. For every finite `F ⊆ Γ` and every nonempty open `U ⊆ X` there is a nonempty clopen `V ⊆ U`
   that is `F`-free.

*Proof.* (1)⇒(2). `Y = ⋃_{γ∈F\{e}} Fix(γ)` is a finite union of closed sets with empty interior,
so `Y` is closed with empty interior and `U \ Y` is nonempty and open. Pick `x ∈ U \ Y` and a
clopen `U' ⊆ U` with `x ∈ U'`. For each `γ ∈ F \ {e}` we have `γx ≠ x`, so by zero-dimensionality
there are disjoint clopen `A_γ ∋ x` and `B_γ ∋ γx`. Put
`V = U' ∩ ⋂_{γ∈F\{e}} (A_γ ∩ γ^{-1}B_γ)`. Each `γ^{-1}B_γ` is clopen because `γ` is a
homeomorphism, so `V` is clopen, and `x ∈ V`. For `γ ∈ F \ {e}`, `V ⊆ A_γ` and `γV ⊆ B_γ`, and
`A_γ ∩ B_γ = ∅`, so `γV ∩ V = ∅`.

(2)⇒(1). If some `γ_0 ≠ e` has `Fix(γ_0) ⊇ U_0` with `U_0` nonempty open, apply (2) to
`F = {γ_0}` and `U = U_0`: the resulting `V` is a nonempty subset of `Fix(γ_0)`, so `γ_0V = V` and
`γ_0V ∩ V = V ≠ ∅`, contradicting `F`-freeness. ∎

Quantifying over every nonempty open `U` is what makes this an equivalence. The weaker statement
with `U = X` holds for many actions that are not topologically free, since the small set can be
chosen away from the fixed region.

**Lemma 2 (density).** Assume the action is topologically free and let `F ⊆ Γ` be finite and
`𝒫` a finite clopen partition of `X`. Say `V` is *admissible* if it is nonempty clopen, `F`-free,
and contained in one atom of `𝒫`. Then every nonempty open `W ⊆ X` contains an admissible `V`,
and a function `h ∈ LC(X,k)` vanishing on every admissible `V` is `0`.

*Proof.* `W` meets some atom `P ∈ 𝒫`, and `W ∩ P` is nonempty open, so Lemma 1 applies inside it.
If `h ≠ 0`, then `{h ≠ 0}` is nonempty open, so it contains an admissible `V`, on which `h` does
not vanish. ∎

**Lemma 2'.** Under the same hypotheses, if `γ ∈ Γ` and `h ∈ LC(X,k)` vanishes on `γV` for every
admissible `V`, then `h = 0`.

*Proof.* If `h ≠ 0` then `γ^{-1}{h ≠ 0}` is nonempty open, so it contains an admissible `V` by
Lemma 2, and then `γV ⊆ {h ≠ 0}`. ∎

Lemmas 2 and 2' replace the partition step. The admissible sets do not cover `X`; they cover the
dense open set `X \ ⋃_{γ∈F\{e}} Fix(γ)`, and a locally constant function is determined there.

## 3. The noncommuting root

**Proposition 3.** Assume the action is topologically free. Let `n ≥ 2`, `g ∈ GL_n(R)`, and let
`B ⊆ Γ` be finite and symmetric with `e ∈ B` such that every entry of `g` and of `g^{-1}` lies in
`Σ_{γ∈B} LC(X,k)u_γ`. Let `𝒫` be a finite clopen partition on which every `f∘α` is constant, for
`α ∈ B` and `f` a coefficient of an entry of `g` or `g^{-1}`. Call `V` admissible if it is
nonempty clopen, `(B^{-1}B)`-free, and inside one atom of `𝒫`. If `g` commutes with `e_{ij}(e_V)`
for every `i ≠ j` and every admissible `V`, then `g = cI_n` with `c ∈ LC(X,k)^×`. For `k = F_2`,
`g = I_n`.

*Proof.* `g` commutes with `e_{ij}(r)` iff `g·rE_{ij} = rE_{ij}·g`. Comparing entries,
`(g·rE_{ij})_{pq} = g_{pi} r δ_{jq}` and `(rE_{ij}·g)_{pq} = δ_{pi} r g_{jq}`, so the condition is

- `g_{pi} r = 0` for `p ≠ i`;
- `r g_{jq} = 0` for `q ≠ j`;
- `g_{ii} r = r g_{jj}`.

Take `r = e_V` with `V` admissible.

*Off-diagonal.* Write `g_{pi} = Σ_{γ∈B} f_γ u_γ`. Then
`g_{pi}e_V = Σ_γ f_γ (e_V∘γ^{-1}) u_γ = Σ_γ f_γ e_{γV} u_γ`, so `f_γ e_{γV} = 0` for every `γ`,
that is, `f_γ` vanishes on `γV`. By Lemma 2', `f_γ = 0`. So `g_{pi} = 0` whenever `p ≠ i`; as `i`
ranges over all indices (with any `j ≠ i`, available since `n ≥ 2`), every off-diagonal entry of
`g` vanishes.

*Diagonal.* Write `g_{ii} = Σ_γ f_γ u_γ` and `g_{jj} = Σ_γ h_γ u_γ`. From `g_{ii}e_V = e_V g_{jj}`
and uniqueness of coefficients, `f_γ e_{γV} = e_V h_γ` for every `γ ∈ B`. For `γ ≠ e` we have
`γ ∈ B ⊆ B^{-1}B`, so `γV ∩ V = ∅`; the left side is supported in `γV` and the right side in `V`,
so both vanish, and Lemma 2' gives `f_γ = 0 = h_γ`. For `γ = e`, `f_e` and `h_e` agree on every
admissible `V`, so `f_e = h_e` by Lemma 2. Hence `g_{ii} = g_{jj} = c ∈ LC(X,k)` for all `i ≠ j`,
and `g = cI_n`.

*The unit.* `c` is a unit of `R`: if `cb = 1` with `b = Σ b_γ u_γ`, then `c b_e = 1` and
`c b_γ = 0` for `γ ≠ e`, so `c` is a unit of `LC(X,k)`. For `k = F_2` every value of `c` lies in
`F_2^× = {1}`, so `c = 1` and `g = I_n`. ∎

Over `F_q` with `q > 2` the conclusion stops at `g = cI_n` with `c` a locally constant unit, which
is the known obstruction (ROSTER-D warning): the extra roots `e_{ij}(e_V u_γ)` are needed. This
lane stays at `k = F_2`.

**Corollary 3'.** For a topologically free action and `n ≥ 2`, `Z(EL_n(LC(X,F_2) ⋊ Γ)) = 1`.

## 4. The tower group and the commutator

Fix `g ≠ I_n` in `GL_n(R)`, `B`, `𝒫` as in Proposition 3, and an admissible `V`. Put `d = n|B|`
and, for `α,β ∈ B`, `ε_{αβ} = e_{αV}u_{αβ^{-1}}`.

**Proposition 4.** `ε_{αβ}ε_{α'β'} = δ_{βα'} ε_{αβ'}`, the map `ψ(E_{(p,α),(q,β)}) = ε_{αβ}E_{pq}`
extends to an injective multiplicative `k`-linear map `M_d(k) → M_n(R)`, and for `n ≥ 3` the group
`H = {I_n − ψ(I_d) + ψ(A) : A ∈ GL_d(k)} ≅ GL_d(k)` lies in `EL_n(R)`.

*Proof.* `ε_{αβ}ε_{α'β'} = e_{αV}(e_{α'V}∘βα^{-1})u_{αβ^{-1}α'β'^{-1}}
= e_{αV}e_{αβ^{-1}α'V}u_{αβ^{-1}α'β'^{-1}}`, and
`e_{αV}e_{αβ^{-1}α'V} = e_{α(V ∩ β^{-1}α'V)}`, which is `0` unless `β^{-1}α' = e` because
`β^{-1}α' ∈ B^{-1}B` and `V` is `(B^{-1}B)`-free. When `β = α'` the group index collapses to
`αβ'^{-1}`, giving `ε_{αβ'}`. Injectivity: two distinct `ε_{αβ}`, `ε_{α'β'}` either sit in
different `u_γ`-components, or have `αβ^{-1} = α'β'^{-1}` with `α ≠ α'`, and then `αV ∩ α'V = ∅`,
so their coefficients are supported on disjoint clopen sets. `ψ(I_d) = e_W I_n` with
`W = ⨆_{α∈B} αV`. For membership in `EL_n`, transvections generate `GL_d(k)`; the transvection
between `(p,α)` and `(q,β)` with `p ≠ q` maps to `e_{pq}(ε_{αβ})`, and for `p = q` it is the
commutator `[e_{pp'}(ε_{αβ}), e_{p'p}(ε_{ββ})]` for any `p' ≠ p`, using `ε_{αβ}ε_{ββ} = ε_{αβ}`
and `ε_{ββ}ε_{αβ} = 0`. This is the identity already in the manuscript, with `u^{a-b}` replaced by
`u_{αβ^{-1}}`. ∎

**Proposition 5.** With `h = e_{ij}(e_V)` and `k = [g,h]`, both `k − I_n` and `k^{-1} − I_n` lie in
`ψ(M_d(F_2))`, so `k ∈ H`.

*Proof.* `(f u_α)e_V(f' u_β) = f e_{αV}(f'∘α^{-1})u_{αβ}`, whose coefficient is supported in `αV`
and is constant there because `f` and `f'∘α^{-1}` are constant on `αV` (the choice of `𝒫`); over
`F_2` it is `0` or `e_{αV}`, and `αβ = α(β^{-1})^{-1}`, so the product is `0` or `ε_{α,β^{-1}}`
with `β^{-1} ∈ B`. The entries of `ghg^{-1} − I_n = g e_V E_{ij} g^{-1}` are sums of such products,
and `h^{-1} = h = I_n + ε_{ee}E_{ij}`, so `k − I_n = (ghg^{-1} − h)h` and
`k^{-1} − I_n = h(ghg^{-1} − h)` lie in `ψ(M_d(F_2))`. Since `ψ` is injective and multiplicative,
`k ∈ H`. ∎

## 5. The theorems

**Theorem 6.** Let `Γ` be a countable group acting minimally and topologically freely on a compact
Hausdorff zero-dimensional space `X`, let `R = LC(X,F_2) ⋊ Γ`, and let `n ≥ 3`. Then `EL_n(R)` is
simple with trivial centre. No freeness is used.

*Proof.* Let `1 ≠ N ⊴ EL_n(R)` and `1 ≠ g ∈ N`. Choose `B` and `𝒫` as in Proposition 3. By
Proposition 3 some `h = e_{ij}(e_V)` with `V` admissible fails to commute with `g`, so
`k = [g,h] ∈ N \ {1}`. By Propositions 4 and 5, `k` lies in `H ≅ GL_d(F_2) = PSL_d(F_2)`, which is
simple because `d = n|B| ≥ 3`. So `N ∩ H` is a nontrivial normal subgroup of `H`, hence `H ⊆ N`,
and `e_{pq}(e_V) ∈ N` for all `p ≠ q`. The level `J = {r ∈ R : e_{pq}(r) ∈ N for all p ≠ q}` is a
two-sided ideal, by additivity and `e_{pq}(sr) = [e_{pl}(s), e_{lq}(r)]`,
`e_{pq}(rs) = [e_{pl}(r), e_{lq}(s)]` for `l ∉ {p,q}`. It contains `e_V`, so it contains every
`e_{γV} = u_γ e_V u_γ^{-1}`. The set `⋃_γ γV` is open, nonempty and invariant, so it is `X` by
minimality, and compactness gives `γ_1V, …, γ_mV` covering `X`; then
`1 = 1 − Π_i(1 − e_{γ_iV}) ∈ J`, so `J = R` and `N = EL_n(R)`. The centre is trivial by
Corollary 3'. ∎

**Theorem 7 (the boundary, as an iff).** Let `Γ` be a countable group acting on a compact Hausdorff
zero-dimensional space `X`, `R = LC(X,F_2) ⋊ Γ`, `n ≥ 3`. Then `EL_n(R)` is simple if and only if
the action is minimal and topologically free.

*Proof.* (⇐) is Theorem 6. (⇒) Suppose the action is not minimal or not topologically free. The
transformation groupoid `Γ ⋉ X` is Hausdorff and ample, its Steinberg algebra is `R`
(`crossed-products-are-transformation-steinberg-algebras`), and it is effective exactly when the
action is topologically free and minimal exactly when the action is. By
`steinberg-algebra-simple-iff-minimal-effective` (reviewed PASS) `R` is not simple, so it has an
ideal `I` with `0 ≠ I ≠ R`. Then `EL_n(R,I)` is normal in `EL_n(R)`, nontrivial because
`e_{12}(a) ≠ I_n` for `0 ≠ a ∈ I`, and proper because `EL_n(R) → EL_n(R/I)` is onto with
`EL_n(R,I)` inside its kernel, while `EL_n(R/I) ≠ 1` since `1 ≠ 0` in `R/I`. So `EL_n(R)` is not
simple. ∎

**Corollary 8.** An action with a dense free orbit is topologically free.

*Proof.* If `Fix(γ) ⊇ U` with `U` nonempty open and `γ ≠ e`, the dense orbit meets `U`, so some
point of it is fixed by `γ`. ∎

So Theorem 6 applies to every minimal action with one free orbit, which is what the Toeplitz
constructions supply directly (`rf-toeplitz-subshifts-over-residually-finite-groups`, Theorem T);
`rf-toeplitz-subshifts-act-freely` is not needed for simplicity.

## 6. Model tests
- **`Γ = Z`, `X` an infinite minimal subshift.** No periodic points, so the action is free and
  Theorem 6 gives the manuscript's simplicity statement.
- **Finite `X`.** Topological freeness forces freeness (points are isolated), minimality forces a
  single orbit, so `Γ` is finite, `R ≅ M_{|X|}(F_2)` and `EL_n(R) = SL_{n|X|}(F_2)`, simple for
  `n ≥ 3`. Theorem 6 needs no infiniteness hypothesis, and gives the right answer here.
- **Trivial action of `Γ ≠ 1` on a point.** Not topologically free; `R = F_2[Γ]`, which is not
  simple, and `EL_n(R)` has the proper nontrivial normal subgroup `EL_n(R, ω)` for the
  augmentation ideal `ω`. Theorem 7 predicts this.
- **Non-minimal.** `X` with a proper closed invariant `Y` gives the ideal of functions vanishing on
  `Y`; this is `subshift-elementary-group-simple-iff-infinite-minimal` in the `Z` case.
- **A minimal non-topologically-free action.** Take `Γ = Δ × N` with `N ≠ 1` finite and `N` acting
  trivially, `Δ` acting minimally. Then `Fix(ν) = X` for `ν ∈ N`, `R ↠ LC(X,F_2)⋊Δ` has nonzero
  kernel, and `EL_n(R)` is not simple. The tower lemma fails at `F = N`, as it must.
