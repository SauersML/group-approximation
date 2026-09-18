---
rg: 2
id: thompson-f-commensurated-subgroups-are-trivial-or-normal-proof
kind: route
title: "A fundamental interval of one element of H and a disjoint-support commutator put F(I) into H; simplicity of F(I) ≅ F′ spreads it to all of F′"
target: thompson-f-commensurated-subgroups-are-trivial-or-normal
requires:
  - thompson-f-rigid-interval-subgroups-facts
---

**Notation and imports** (`thompson-f-rigid-interval-subgroups-facts`).
- For dyadic `0 < a < b < 1`, `F(a,b)` is the set of `g ∈ F` that are the identity outside a compact subset
  of `(a,b)`. By (F2) it is the commutant of `F[a,b] ≅ F`, so `F(a,b) ≅ F′`.
- (F1): `F′` is simple and equals the set of elements supported in a compact subset of `(0,1)`. So each
  `F(a,b)` is an infinite simple group.
- (F4): `F′` acts transitively on increasing pairs of dyadic rationals in `(0,1)`.
- Supports: `supp g` is the closure of `{t : g t ≠ t}`. Elements with disjoint supports commute, and
  `supp(k g k⁻¹) = k(supp g)`.

**Lemma 0.** An infinite simple group `S` has no proper finite-index subgroup. *Proof.* A finite-index
subgroup contains a finite-index normal subgroup (the kernel of the action on cosets), which is `1` or `S`;
it is not `1` because `S` is infinite. ∎

**Theorem.** If `H ≤ F` is commensurated and `H ≠ 1`, then `H ⊇ F′`.

*Step 1 (a fundamental interval).* Pick `h ∈ H ∖ {1}` and `t₀ ∈ (0,1)` with `h t₀ ≠ t₀`. Replacing `h` by
`h⁻¹` we may assume `h t₀ > t₀`. Choose dyadic `a < b` with `t₀ < a < b < h t₀`, and put `I = (a,b)`. Let
`(p,q)` be the component of `{t : h t ≠ t}` containing `t₀`. On `(p,q)` the map `h` has no fixed point and
`h t > t`, so the intervals `h^m [t₀, h t₀)`, `m ∈ Z`, are pairwise disjoint. Hence
`h^m(Ī) ∩ Ī = ∅` for every `m ≠ 0`, and `h^m(Ī) ∩ h^(m′)(Ī) = ∅` for `m ≠ m′`.

*Step 2 (commensuration gives a power).* Let `f ∈ F(a,b)`. Since `H ∩ f H f⁻¹` has finite index in `H`, the
subgroup `⟨h⟩ ∩ f H f⁻¹` has finite index in `⟨h⟩`, so it equals `n_f Z` for some `n_f ≥ 1`. For every
`m ∈ n_f Z` we have `f⁻¹ h^m f ∈ H`, and `h^(−m) ∈ H`, so

`u_(f,m) := f⁻¹ · (h^m f h^(−m)) ∈ H`

(note `f⁻¹ h^m f h^(−m) = f⁻¹ · (h^m f h^(−m))` as a product of two elements). Here `f⁻¹` is supported in `Ī`
and `k_(f,m) := h^m f h^(−m)` in `h^m(Ī)`.

*Step 3 (the commutator trick).* Let `f₁, f₂ ∈ F(a,b)`. Put `m₁ = n_(f₁)` and `m₂ = 2 n_(f₁) n_(f₂)`, so
`m₁ ≠ m₂`, both nonzero, `m_i ∈ n_(f_i) Z`. Write `u_i = a_i k_i` with `a_i = f_i⁻¹` supported in `Ī`
and `k_i` supported in `h^(m_i)(Ī)`. The three sets `Ī`, `h^(m₁)(Ī)`, `h^(m₂)(Ī)` are pairwise disjoint
(Step 1). So `k₁` commutes with `a₁, a₂, k₂`, and `k₂` commutes with `a₁, a₂`. Therefore

`[u₁, u₂] = a₁k₁ a₂k₂ k₁⁻¹a₁⁻¹ k₂⁻¹a₂⁻¹ = a₁a₂a₁⁻¹a₂⁻¹ · k₁k₂k₁⁻¹k₂⁻¹ = [f₁⁻¹, f₂⁻¹] · 1`,

using `[k₁,k₂] = 1` (disjoint supports). Hence `[f₁⁻¹, f₂⁻¹] ∈ H` for all `f₁, f₂ ∈ F(a,b)`, so `H`
contains the commutator subgroup of `F(a,b)`. As `F(a,b) ≅ F′` is simple and non-abelian, it is perfect,
so `F(a,b) ⊆ H`.

*Step 4 (spreading).* Let `g ∈ F`. `F(a,b) ∩ gHg⁻¹` has finite index in `F(a,b)`, because
`[H : H ∩ gHg⁻¹] < ∞` and `F(a,b) ⊆ H`. By Lemma 0 it is all of `F(a,b)`. So `g⁻¹ F(a,b) g = F(g⁻¹a, g⁻¹b)`
lies in `H` for every `g ∈ F`. By (F4), `g⁻¹(a), g⁻¹(b)` can be any dyadic pair `a′ < b′`. Every element of
`F′` is supported in a compact subset of some `(a′,b′)` (F1), hence lies in `F(a′,b′) ⊆ H`. So `H ⊇ F′`. ∎

A subgroup containing `F′` is normal, since `F/F′` is abelian. Conversely every normal subgroup is
commensurated, so the Theorem also reproves that nontrivial normal subgroups of `F` contain `F′`.

**Corollary 1 (tdlc hulls).** Let `φ : F → G` have dense image, `G` totally disconnected locally compact.
By van Dantzig, `G` has a compact open subgroup `U`.
- `H_U = φ⁻¹(U)` is commensurated in `F`: `[H_U : H_U ∩ gH_Ug⁻¹] ≤ [U : U ∩ φ(g)Uφ(g)⁻¹] < ∞`, since the
  intersection of two compact open subgroups has finite index in each.
- If `H_U = 1`, then `φ(F) ∩ U = 1`. But `φ(F)` is dense and `U` is open, so `φ(F) ∩ U` is dense in `U`,
  hence `U = 1`, `G` is discrete and `G = φ(F)`. By the Theorem `ker φ` is `1` or contains `F′`.
- Otherwise `φ(F′) ⊆ U`. Let `N` be the closure of `φ(F′)`; it is compact. It is normalized by the dense
  subgroup `φ(F)`, hence by `G`. The image of `F/F′` is dense in `G/N`, so `G/N` is abelian and `G` is
  compact-by-abelian, hence amenable. ∎

**Corollary 2 (locally finite graphs).** Let `F` act on a connected locally finite graph `X`. For a vertex
`v`, `[Stab(v) : Stab(v) ∩ Stab(gv)]` is the size of the `Stab(v)`-orbit of `gv`, which lies in a finite
sphere around `v`; so `Stab(v) = Stab_F(v)` is commensurated. If some `Stab(v) ≠ 1`, then `F′` fixes `v`. It
then permutes the finitely many neighbours of `v`; a finite quotient of the infinite simple group `F′` is
trivial, so `F′` fixes them, and by connectedness `F′` fixes every vertex. ∎

**Calibration.** Finiteness is essential: in the group `Z ≀ Z` the base `Z^(Z)` is normal, while in
`BS(1,2) = Z[1/2] ⋊ Z` the subgroup `Z` is commensurated and not normal. Both lack rigid stabilizers with
simple commutants, the input of Steps 3–4. In Thompson's `T` the finite cyclic subgroups are commensurated
and not normal, so torsion (where Step 1 fails) is essential too.
