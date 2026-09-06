import GroupApproximation.CharClass.RelativeSubspaceIso

/-!
# The relative group of a product pair over a contractible base

For a contractible `B`, the slice `v ↦ (b, v)` is a map of pairs
`(E, S) → (B × E, B × S)` and induces an isomorphism on relative cohomology.  The
case `cc-lix-odd` consumes is `E = ℂ^r` and `S` the complement of the origin, where
the target is the local model of `RelativeLocalModel.lean`.

The **underlying map is exported by name** (`sliceMap`, and `slicePairMap` for its
action on pairs) rather than being buried inside `asIso`.  That is deliberate and
was asked for: a consumer whose own map is also a `relPullback` can then use
`relPullback_comp` to turn a composite of induced maps into a *single* induced map,
so an equation between cohomology maps becomes an equation between continuous maps
of pairs, provable pointwise by `relPullback_eq_of_eq`.

Both bijectivity inputs to the five lemma come from the same two-line pattern: the
slice followed by the projection is the identity on the nose, and the projection
off a contractible factor is a homotopy equivalence, so the slice's pullback is the
inverse of a bijection.  No second homotopy is constructed anywhere.

## Main definitions

* `sliceCMap`, `sndCMap`, `subSliceCMap`, `subSndCMap` — the four continuous maps.
* `sliceMap`, `sndMap`, `slicePairMap` — the same as `TopCat` morphisms.
* `prodSubHomeo` — `{q : B × E | q.2 ∈ S} ≃ₜ B × S`.

## Main results

* `relPullback_slice_bijective` — the slice induces a bijection on relative
  cohomology, for any `S`, in every positive degree.
* `relCohomologyProdIso` — the bundled isomorphism `cc-lix-odd` consumes, and
  `relCohomologyProdIso_hom`, which names its underlying map.
-/

open CategoryTheory Limits AlgebraicTopology
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

namespace RelativeSupport

noncomputable section

variable {B E : Type} [TopologicalSpace B] [TopologicalSpace E]

/-! ## 0. A bijection with a bijective right inverse -/

theorem bijective_of_comp_eq_id {α β : Type*} {f : α → β} {g : β → α}
    (hf : Function.Bijective f) (h : ∀ a, g (f a) = a) : Function.Bijective g := by
  refine ⟨?_, fun a => ⟨f a, h a⟩⟩
  intro x y hxy
  obtain ⟨a, rfl⟩ := hf.2 x
  obtain ⟨b, rfl⟩ := hf.2 y
  rw [h a, h b] at hxy
  exact congrArg f hxy

/-! ## 1. The four maps -/

/-- The slice `v ↦ (b, v)`. -/
def sliceCMap (b : B) (E : Type) [TopologicalSpace E] : C(E, B × E) :=
  ⟨fun v => (b, v), by fun_prop⟩

/-- The projection `(u, v) ↦ v`. -/
def sndCMap (B E : Type) [TopologicalSpace B] [TopologicalSpace E] : C(B × E, E) :=
  ⟨fun q => q.2, by fun_prop⟩

/-- The slice on the subspaces. -/
def subSliceCMap (b : B) {E : Type} [TopologicalSpace E] (S : Set E) :
    C(↥S, ↥{q : B × E | q.2 ∈ S}) :=
  ⟨fun v => ⟨(b, (v : E)), v.2⟩, by fun_prop⟩

/-- The projection on the subspaces. -/
def subSndCMap (B : Type) [TopologicalSpace B] {E : Type} [TopologicalSpace E] (S : Set E) :
    C(↥{q : B × E | q.2 ∈ S}, ↥S) :=
  ⟨fun q => ⟨(q : B × E).2, q.2⟩, by fun_prop⟩

/-- The slice, as a morphism of spaces. -/
def sliceMap (b : B) (E : Type) [TopologicalSpace E] : TopCat.of E ⟶ TopCat.of (B × E) :=
  cmap (sliceCMap b E)

/-- The projection, as a morphism of spaces. -/
def sndMap (B E : Type) [TopologicalSpace B] [TopologicalSpace E] :
    TopCat.of (B × E) ⟶ TopCat.of E :=
  cmap (sndCMap B E)

/-- The slice is a map of pairs `(E, S) → (B × E, {q | q.2 ∈ S})`. -/
theorem slice_mapsTo (b : B) (S : Set E) :
    ∀ v ∈ S, (ConcreteCategory.hom (sliceMap b E)) v ∈ {q : B × E | q.2 ∈ S} :=
  fun _ hv => hv

/-- The slice as a map of pairs, named so that a consumer can rewrite along it. -/
abbrev slicePairMap (b : B) (E : Type) [TopologicalSpace E] :
    TopCat.of E ⟶ TopCat.of (B × E) := sliceMap b E

theorem slice_comp_snd (b : B) (E : Type) [TopologicalSpace E] :
    sliceMap b E ≫ sndMap B E = 𝟙 (TopCat.of E) := rfl

theorem subSlice_comp_subSnd (b : B) (S : Set E) :
    restrictPairMap (sliceMap b E) (slice_mapsTo b S) ≫ cmap (subSndCMap B S)
      = 𝟙 (TopCat.of ↥S) := rfl

/-! ## 2. Functoriality of the ambient pullback -/

theorem absPull_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (m : ℕ) :
    absPull (f ≫ g) m = absPull g m ≫ absPull f m := by
  show HomologicalComplex.homologyMap
    ((singularCochainComplexFunctor (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2))).map
      (f ≫ g).op) m = _
  rw [show ((f ≫ g).op : Opposite.op Z ⟶ Opposite.op X) = g.op ≫ f.op from rfl,
    CategoryTheory.Functor.map_comp, HomologicalComplex.homologyMap_comp]

/-- If `f ≫ g` is the identity and `g`'s pullback is bijective, so is `f`'s. -/
theorem absPull_bijective_of_comp {X Y : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : f ≫ g = 𝟙 X) (m : ℕ) (hg : Function.Bijective (absPull g m).hom) :
    Function.Bijective (absPull f m).hom := by
  refine bijective_of_comp_eq_id hg (fun a => ?_)
  have h : absPull g m ≫ absPull f m = 𝟙 ((cochainCx (ZMod 2) X).homology m) := by
    rw [← absPull_comp, hfg, absPull_id_eq]
  have h2 := congrArg (fun u => u.hom a) h
  simp only [ModuleCat.comp_apply] at h2
  exact h2

/-! ## 3. The two homotopy equivalences off a contractible factor -/

/-- The punctured product as a product: `{q : B × E | q.2 ∈ S} ≃ₜ B × S`. -/
def prodSubHomeo (B : Type) [TopologicalSpace B] {E : Type} [TopologicalSpace E] (S : Set E) :
    ↥{q : B × E | q.2 ∈ S} ≃ₜ B × ↥S where
  toFun q := ((q : B × E).1, ⟨(q : B × E).2, q.2⟩)
  invFun p := ⟨(p.1, (p.2 : E)), p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The projection `B × E → E` as a homotopy equivalence, for contractible `B`.
A top-level definition, not a `have`: a `have`-bound *data* term is opaque, so
`.toFun` could not be unfolded at the use site. -/
def prodSndHomotopyEquiv (B E : Type) [TopologicalSpace B] [TopologicalSpace E]
    [ContractibleSpace B] : ContinuousMap.HomotopyEquiv (B × E) E :=
  (Homeomorph.prodComm B E).toHomotopyEquiv.trans (prodContractibleEquiv E B)

theorem prodSndHomotopyEquiv_toFun (B E : Type) [TopologicalSpace B] [TopologicalSpace E]
    [ContractibleSpace B] : (prodSndHomotopyEquiv B E).toFun = sndCMap B E := by
  apply ContinuousMap.ext
  intro q
  show (prodContractibleEquiv E B).toFun _ = _
  rw [prodContractibleEquiv_toFun]
  rfl

/-- The same on the subspaces. -/
def subSndHomotopyEquiv (B : Type) [TopologicalSpace B] {E : Type} [TopologicalSpace E]
    [ContractibleSpace B] (S : Set E) :
    ContinuousMap.HomotopyEquiv ↥{q : B × E | q.2 ∈ S} ↥S :=
  ((prodSubHomeo B S).trans (Homeomorph.prodComm B ↥S)).toHomotopyEquiv.trans
    (prodContractibleEquiv ↥S B)

theorem subSndHomotopyEquiv_toFun (B : Type) [TopologicalSpace B] {E : Type}
    [TopologicalSpace E] [ContractibleSpace B] (S : Set E) :
    (subSndHomotopyEquiv B S).toFun = subSndCMap B S := by
  apply ContinuousMap.ext
  intro q
  show (prodContractibleEquiv ↥S B).toFun _ = _
  rw [prodContractibleEquiv_toFun]
  rfl

theorem absPull_snd_bijective (hB : ContractibleSpace B) (m : ℕ) :
    Function.Bijective (absPull (sndMap B E) m).hom := by
  haveI := hB
  have hb := (pullEquivOfHomotopyEquiv (prodSndHomotopyEquiv B E) m).bijective
  rw [show (pullEquivOfHomotopyEquiv (prodSndHomotopyEquiv B E) m :
      Hmod2 (TopCat.of E) m → Hmod2 (TopCat.of (B × E)) m)
      = fun a => pullMap (prodSndHomotopyEquiv B E).toFun m a from rfl,
    prodSndHomotopyEquiv_toFun] at hb
  exact hb

theorem absPull_subSnd_bijective (hB : ContractibleSpace B) (S : Set E) (m : ℕ) :
    Function.Bijective (absPull (cmap (subSndCMap B S)) m).hom := by
  haveI := hB
  have hb := (pullEquivOfHomotopyEquiv (subSndHomotopyEquiv B S) m).bijective
  rw [show (pullEquivOfHomotopyEquiv (subSndHomotopyEquiv B S) m :
      Hmod2 (TopCat.of ↥S) m → Hmod2 (TopCat.of ↥{q : B × E | q.2 ∈ S}) m)
      = fun a => pullMap (subSndHomotopyEquiv B S).toFun m a from rfl,
    subSndHomotopyEquiv_toFun] at hb
  exact hb

/-! ## 4. The slice induces a bijection on relative cohomology -/

theorem relPullback_slice_bijective (hB : ContractibleSpace B) (b : B) (S : Set E) (n : ℕ) :
    Function.Bijective
      (relPullback (ZMod 2) (sliceMap b E) (slice_mapsTo b S) (n + 1)).hom := by
  refine relPullback_bijective_of_absolute (sliceMap b E) (slice_mapsTo b S) n
    (fun m => absPull_bijective_of_comp (sliceMap b E) (sndMap B E)
      (slice_comp_snd b E) m (absPull_snd_bijective hB m))
    (fun m => ?_)
  exact absPull_bijective_of_comp (restrictPairMap (sliceMap b E) (slice_mapsTo b S))
    (cmap (subSndCMap B S)) (subSlice_comp_subSnd b S) m (absPull_subSnd_bijective hB S m)

/-! ## 5. The statement `cc-lix-odd` consumes -/

/-- **The relative group of a product pair over a contractible base is the relative
group of the fibre pair.**  The underlying map is `relPullback` along `sliceMap`;
see `relCohomologyProdIso_hom`. -/
def relCohomologyProdIsoGen (hB : ContractibleSpace B) (b : B) (n : ℕ) (hn : 2 ≤ n)
    {E : Type} [TopologicalSpace E] (S : Set E) :
    relCohomology (ZMod 2) (TopCat.of (B × E)) {q : B × E | q.2 ∈ S} n
      ≅ relCohomology (ZMod 2) (TopCat.of E) S n :=
  haveI : IsIso (relPullback (ZMod 2) (sliceMap b E) (slice_mapsTo b S) n) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact (ConcreteCategory.isIso_iff_bijective _).2
      (relPullback_slice_bijective hB b S m)
  asIso (relPullback (ZMod 2) (sliceMap b E) (slice_mapsTo b S) n)

@[simp] theorem relCohomologyProdIsoGen_hom (hB : ContractibleSpace B) (b : B) (n : ℕ)
    (hn : 2 ≤ n) {E : Type} [TopologicalSpace E] (S : Set E) :
    (relCohomologyProdIsoGen hB b n hn S).hom
      = relPullback (ZMod 2) (sliceMap b E) (slice_mapsTo b S) n := rfl

/-- **The statement agreed with `cc-lix-odd`**, verbatim: the complex fibre and the
complement of the origin.  A specialisation of `relCohomologyProdIsoGen`. -/
def relCohomologyProdIso (hB : ContractibleSpace B) (b : B) (r n : ℕ) (hn : 2 ≤ n) :
    relCohomology (ZMod 2) (TopCat.of (B × (Fin r → ℂ))) {q | q.2 ≠ 0} n
      ≅ relCohomology (ZMod 2) (TopCat.of (Fin r → ℂ)) (puncturedSet r) n :=
  relCohomologyProdIsoGen hB b n hn (puncturedSet r)

/-- The underlying map of `relCohomologyProdIso` is `relPullback` along the slice —
exported so that a composite of induced maps can be collapsed by
`relPullback_comp` into a single induced map. -/
@[simp] theorem relCohomologyProdIso_hom (hB : ContractibleSpace B) (b : B) (r n : ℕ)
    (hn : 2 ≤ n) :
    (relCohomologyProdIso hB b r n hn).hom
      = relPullback (ZMod 2) (sliceMap b (Fin r → ℂ))
          (slice_mapsTo b (puncturedSet r)) n := rfl

end

end RelativeSupport

end GroupApproximation.CharClass
