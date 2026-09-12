# Lane `sp-relhomotopy` — relative homotopy invariance of singular cohomology over any `R`

Owner: `sp-relhomotopy`.  Files owned: `GroupApproximation/CharClass/RelHomotopy*.lean`
(new).  Deliverable: `relPullback R f hf n = relPullback R g hg n` for two maps of pairs
`(X, A) → (Y, B)` joined by a homotopy carrying `A × I` into `B`, over an **arbitrary**
commutative ring `R`.  This retires the `F₂`-only cut of
`CharClass/RelativeLineHomotopy.lean` for the odd side.

## GREEN (with job counts)

*(nothing yet)*

## AUTHORED, UNVERIFIED

Two new files, both leaves (nothing imports them yet), first probe in flight on the cold
clone `ring-b-end`.

`GroupApproximation/CharClass/RelHomotopyPrism.lean` (chain level)

| declaration | content |
|---|---|
| `homotopyCorestrict hf hg H hH` | the corestricted homotopy `A × I → B` |
| `sInclusion_whiskerRight_h` | `i ▷ I ≫ H.h = H_A.h ≫ j` in `TopCat` (`ext`, `rfl`) |
| `topCat_homotopy_toSSet_h` | the `h` field of `TopCat.Homotopy.toSSet`, as a `rfl` lemma |
| `toSSet_h_naturality` | the square through `toSSet`: `whisker_exchange`, `μ_natural_left_assoc`, `Functor.map_comp` |
| `toSimplicialObjectHomotopy_h_naturality` | generic in `SSet`; `SSet.yonedaEquiv_symm_comp` |
| `toChainHomotopy_hom_naturality` | generic in a preadditive `C`; **the lemma Mathlib does not have** |
| `prismCoeffFunctor`, `prismSimpHom`, `prismHom` | the prism at coefficients `R` |
| `prismHom_eq`, `singularChainMap_eq_app` | the two `rfl` bridges to Mathlib's shapes |
| `prismHom_naturality` | `C(i) ≫ P_X = P_A ≫ C(j)` |
| `prismHom_mapsTo_subChain` | the prism carries `A`-chains to `B`-chains |
| `prism_comm_zero`, `prism_comm_succ` | Mathlib's `Homotopy.comm` with `dNext`/`prevD` resolved |

`GroupApproximation/CharClass/RelHomotopyInvariance.lean` (cochain level, endpoint)

| declaration | content |
|---|---|
| `relCochain_apply_eq_zero_of_mem_subChain` | a relative cochain kills the whole subordinate submodule |
| `prismCochain`, `prismCochain_mem_relCochainSubmodule` | the dual prism, and that it lands in the relative cochains |
| `relPrism`, `relPrismHom`, `relPrismHom_eq`, `relPrismHom_eq_zero` | the `Homotopy.hom` family |
| `prism_cochain_comm_zero`, `prism_cochain_comm_succ` | the chain identity composed on the right with `φ` |
| `relHomotopy` | `Homotopy (relCochainMap R f hf) (relCochainMap R g hg)` |
| `RelativeSupport.relPullback_eq_of_homotopy` | **the theorem** |
| `RelativeSupport.relPullback_eq_of_path_param` | two slices joined by a path in the parameter space |
| `RelativeSupport.relPullback_eq_of_contractible_param` | the `LIXHsq` interface, over any `R`, every degree |

`#audit_axioms` on the endpoint and on the contractible-parameter corollary.

## Plan, at lemma precision (2026-09-10, first hour)

Read first: `notes/LIX_STRONGER_PROGRAM_2026-09-10.md`, `FLEET_TRAPS.md`,
`sp-coeff.md` "Deliverable 3", `sp-design.md` §4.3–4.4, and, in the tree,
`RelativeCochains.lean`, `RelativeFunctorial.lean`, `RelativeLineHomotopy.lean`,
`RelativeHomotopyInvariance.lean`, `SubordinateChains.lean`,
`SubChainSubspaceBridge.lean`, `CupProduct.lean`, `SingularCohomology.lean`, and at the
Mathlib pin `81a5d257`: `AlgebraicTopology/SingularHomology/HomotopyInvariance.lean`,
`Topology/Homotopy/TopCat/ToSSet.lean`, `Topology/Homotopy/TopCat/Basic.lean`,
`Topology/Category/TopCat/Monoidal.lean`, `AlgebraicTopology/SimplicialSet/Homotopy.lean`,
`AlgebraicTopology/SimplicialSet/Homology/HomotopyInvariance.lean`,
`AlgebraicTopology/SimplicialObject/ChainHomotopy.lean`,
`AlgebraicTopology/SimplicialObject/Homotopy.lean`, `Algebra/Homology/Homotopy.lean`.

### 0. The two facts that shape the design

* **The relative cochain complex is the annihilator subcomplex, not a quotient.**
  `relCochainSubmodule R X A n = {φ | ∀ σ subordinate to A, φ [σ] = 0}` — cochains killing
  the *generators* of `subChainSubmodule R X A n`, hence (by
  `subChainSubmodule_induction`) killing the whole submodule.  So the thing to prove is
  the transpose of "the prism carries `A`-chains into `B`-chains".
* **Everything on the cochain side is composition in `ModuleCat`, definitionally.**
  `cochainPullback f p φ = singularChainMap R f p ≫ φ` and
  `cochainCoboundary R Z p φ = ∂_{p+1} ≫ φ` are both `rfl` (the vendored proofs of
  `cochainPullback_eval` and `cochainCoboundary_eval` both open with exactly that `rfl`
  `have`).  Consequence: the homotopy identity on relative cochains is the chain-level
  identity of `Homotopy.comm` **composed on the right with `φ`** — no elementwise
  computation with prisms anywhere, only `Preadditive.add_comp`.

### 1. `RelHomotopyPrism.lean` — the chain-level work

The one square Mathlib does not have is naturality of `toChainHomotopy` in the space.  It
factors into four steps, none of which touches the prism decomposition.

1. `relHomotopyCorestrict` (`TopCat` level).  From `H : TopCat.Homotopy f g` and
   `hH : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ B`, build
   `H.corestrict hf hg hH : TopCat.Homotopy (restrictPairMap f hf) (restrictPairMap g hg)`
   between maps `TopCat.of A ⟶ TopCat.of B`.  Underlying map `(t, a) ↦ ⟨H (t, a.1), _⟩`.
2. `sInclusion_whiskerRight_h` (`TopCat` level).  `sInclusion A ▷ I ≫ H.h = H_A.h ≫ sInclusion B`.
   By `TopCat.whiskerRight_apply` and `TopCat.Homotopy.h_hom_apply` (which **swaps** its
   coordinates: `F.h p = F (I.homeomorph p.2, p.1)`) this is `rfl` after `ext`.
3. `toSSet_h_naturality` (`SSet` level).
   `(TopCat.toSSet.map (sInclusion A) ▷ Δ[1]) ≫ H.toSSet.h = H_A.toSSet.h ≫ TopCat.toSSet.map (sInclusion B)`.
   `TopCat.Homotopy.toSSet`'s `h` field is `_ ◁ stdSimplex.toSSetObjI ≫ μ TopCat.toSSet _ _ ≫ TopCat.toSSet.map H.h`,
   so the square is exactly: `whisker_exchange` (move the `▷` past the `◁`), then
   `Functor.LaxMonoidal.μ_natural_left` (move it past `μ`), then `Functor.map_comp` on
   step 2.  **This is the "lax-monoidal naturality" the lead flagged as the risk; at the
   pin it is two named lemmas, both `@[reassoc (attr := simp)]`, and it does not need any
   description of `μ` on elements.**
4. `toSimplicialObjectHomotopy_h_naturality` (`SimplicialObject` level).  From a square
   `(u ▷ Δ[1]) ≫ H'.h = H.h ≫ v` of `SSet.Homotopy`s deduce
   `u.app _ ≫ H'.toSimplicialObjectHomotopy.h i = H.toSimplicialObjectHomotopy.h i ≫ v.app _`
   for every `i`.  `toSimplicialObjectHomotopy.h i` is
   `x ↦ (yonedaEquiv.symm x ▷ Δ[1] ≫ H.h).app _ (prodStdSimplex.nonDegenerateEquiv₁ i).1`,
   and `SSet.yonedaEquiv_symm_comp` gives `yonedaEquiv.symm (u.app _ x) = yonedaEquiv.symm x ≫ u`;
   then `comp_whiskerRight` and the square.  Elementwise in `TypeCat`, one `ext`.
5. `toChainHomotopy_hom_naturality` (chain level, stated for a general preadditive `C`).
   From `∀ i, u.app _ ≫ H'.h i = H.h i ≫ v.app _` conclude
   `u.app (op ⦋p⦌) ≫ ToChainHomotopy.hom H' p (p+1) = ToChainHomotopy.hom H p (p+1) ≫ v.app (op ⦋p+1⦌)`.
   `ToChainHomotopy.hom_eq` is `@[simp]`: `hom H p (p+1) = -∑ k : Fin (p+1), (-1)^k • H.h k`,
   so this is `Preadditive.comp_sum`/`sum_comp`, `comp_zsmul`/`zsmul_comp`, `comp_neg`/`neg_comp`
   applied termwise.  **No additivity of the coefficient functor is used** — the map is
   pushed *inside* the sum, never through it.
6. `prismHom_mapsTo_subChain`.  With
   `P R H p := (H.singularChainComplexFunctorObjMap (ModuleCat.of R R)).hom p (p+1) : C_p(X) ⟶ C_{p+1}(Y)`:
   `∀ c ∈ subChainSubmodule R X A p, (P R H p).hom c ∈ subChainSubmodule R Y B (p+1)`.
   By `subChainSubmodule_induction`; on a generator `[σ]` with `σ` subordinate to `A`,
   `exists_pushSimplex_of_subordinate` writes `σ = pushSimplex (sInclusion A) p τ`, so
   `[σ] = singularChainMap R (sInclusion A) p [τ]` (`singularChainMap_generator`), step 5
   moves `P` past it, and `singularChainMap_sInclusion_mem` lands the result in the
   submodule.  (The `p = 0` case is not special: only `hom p (p+1)` is ever used.)

### 2. `RelHomotopyInvariance.lean` — the transpose, and the theorem

7. `relCochain_apply_eq_zero`.  A relative cochain kills every element of the subordinate
   submodule, not only the generators (`subChainSubmodule_induction`).
8. `relPrism R H … q : (relCochainComplex R Y B).X (q+1) ⟶ (relCochainComplex R X A).X q`,
   `φ ↦ ⟨P R H q ≫ φ.1, _⟩`, well defined by 6 + 7.
9. `relPrismHom i j`, the `Homotopy.hom` field: `dite (j + 1 = i)` with an `eqToHom` cast,
   `0` otherwise; `zero` is `dif_neg`.  Only `hom (j+1) j` is ever consumed, because for
   `ComplexShape.up ℕ` both `dNext i` and `prevD i` read that family (`dNext_eq`,
   `prevD_eq`, and `prevD_eq_zero` at `i = 0`).
10. `relHomotopy : Homotopy (relCochainMap R f hf) (relCochainMap R g hg)`.  `comm n` is,
    after `Subtype.ext`, the absolute identity
    `singularChainMap f n ≫ φ = (dNext n P + prevD n P + singularChainMap g n) ≫ φ`,
    i.e. `Homotopy.comm n` of Mathlib's chain homotopy composed on the right with `φ`.
    Split `n = 0` / `n + 1` exactly as Mathlib's own `toChainHomotopy` does.
11. `RelativeSupport.relPullback_eq_of_homotopy (R) [CommRing R] {X Y A B f g} (hf hg) (H) (hH) (n) :
     relPullback R f hf n = relPullback R g hg n` — `Homotopy.homologyMap_eq`.
12. Corollaries in the vocabulary the consumers use: a `ContinuousMap.Homotopy` form, a
    "homotopic through maps of pairs" form, and the **contractible-parameter** form
    matching `RelativeLineHomotopy.relPullback_eq_of_homotopy_of_line`'s interface
    (`H : TopCat.of (P × X) ⟶ Y`, `hH` at every parameter, two slices `b`, `b'`), obtained
    by composing `H` with a path `b ⇝ b'` (contractible ⟹ path-connected).  This is the
    shape `LIXHsq.lean` needs, over any `R` and in **every** degree including `0` and with
    no line hypothesis.

### 3. Constraints honoured

* `CharClass/RelativeLineHomotopy.lean` is NOT imported by either file.
* No `sorry`; `#audit_axioms` on the endpoint theorem
  (`[propext, Classical.choice, Quot.sound]`).
* New files only, under the `RelHomotopy` prefix; `sp-coeff`'s files untouched.

## NEEDS

* From `sp-coeff`: nothing blocking.  My files use only `relCochainComplex`,
  `relCochainMap`, `relPullback`, `relCohomology`, all of which already carry
  `(R : Type) [CommRing R]`, so a later `K`-generalisation of the `Relative*` layer does
  not move my statements.  Name coordination sent by SendMessage.
* Not my job, noted for the lead and for `sp-oddside`.  Once this is green,
  `CharClass/LIXHsq.lean`'s `relPullback_lixGL_eq_lixGR` (the `hsq` binder) is a **drop-in
  substitution**: its `hcut` step currently reads

  ```lean
  RelativeSupport.relPullback_eq_of_homotopy_of_line contractibleSpace_lixI _ _
    (cmap (lixHomotopyFun hGc hGu)) (lixHomotopy_mapsTo hGc hGu)
    (lixHomotopy_end_one hGc hGu hGe) (lixHomotopy_end_zero hGc hGu)
    (lixGL_mapsTo hGc hGu hGe) (lixFar_mapsTo hGc hGu) (2 * lixRank dd)
    (by have := two_le_two_mul_lixRank dd; omega) (lixULine hGc hGu)
  ```

  and becomes

  ```lean
  RelativeSupport.relPullback_eq_of_contractible_param (ZMod 2) contractibleSpace_lixI _ _
    (cmap (lixHomotopyFun hGc hGu)) (lixHomotopy_mapsTo hGc hGu)
    (lixHomotopy_end_one hGc hGu hGe) (lixHomotopy_end_zero hGc hGu)
    (lixGL_mapsTo hGc hGu hGe) (lixFar_mapsTo hGc hGu) (2 * lixRank dd)
  ```

  — the same argument list with the coefficient ring in front and the last two arguments
  (the degree bound `1 ≤ n` and the line witness `lixULine`) **dropped**, because neither
  hypothesis is needed any more.  The other `F₂`-only step in that file,
  `relPullback_lixKHomeo_eq_id`, is *not* retired by this file alone, but it is one line
  away.  sp-design's §4.5 item 2 ("`GL_r(ℂ)` acts trivially on `H^{2r}(ℂ^r, ℂ^r∖0; K)`",
  which is what Half B needs) is exactly `relPullback_eq_of_homotopy` fed the **linear**
  homotopy `H (t, v) = γ t *ᵥ v`, where `γ : Path g 1` is a path in `GL_r(ℂ)`: every
  `γ t` is invertible, so `H` carries `I × (ℂ^r ∖ {0})` into `ℂ^r ∖ {0}`, which is the
  `hH` hypothesis verbatim.  No line hypothesis, no degree restriction, any coefficient
  ring.  That construction is `sp-oddside`'s to land, in their own files.

## TRAPS

*(filled as they are hit; cross-lane ones also appended to `notes/lix-lane-reports/FLEET_TRAPS.md`)*

* `TopCat.Homotopy.h` **swaps** its coordinates relative to the homotopy's application:
  `F.h p = F (I.homeomorph p.2, p.1)`, `p : ↑(X ⊗ I)`.  Easy to get backwards; the
  `@[simp]` lemma `TopCat.Homotopy.h_hom_apply` states it.
* A nested type ascription on `(relCochainComplex R X A).X n` does not elaborate
  (FLEET_TRAPS line 56, cc-relative 09-06): state a `∀ ψ : T, …` helper and apply it.
