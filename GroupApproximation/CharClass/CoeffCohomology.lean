import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CohomologyCupProduct
import GroupApproximation.CharClass.CoeffLeibniz

/-!
# Singular cohomology and its cup product over an arbitrary coefficient ring

The vendored `CohomologyCupProduct.lean` descends the Alexander–Whitney cochain
cup product to singular cohomology **at `ZMod 2`**.  Nothing in those 653 lines
uses `1 = -1`: the only coefficient-specific inputs are the Leibniz consequences,
which `CoeffLeibniz.lean` now supplies over any `[CommRing K]`.  This file
replays the descent over `K`.

The vendored `ZMod 2` declarations are **not** edited and **not** replaced: they
remain exactly as they are, and each generic declaration here is *definitionally*
the vendored one at `K = ZMod 2` (see §7), so the `F₂` instance and the
`Cartan*`/`Steenrod*` files that speak the vendored vocabulary are untouched.

## Main declarations

* `cochainCxK K X` — the singular `K`-cochain complex of `X`;
  `cohomologyK K X n` — `H^n(X; K)`.
* `cocycleClassK` — the class of a cocycle, with surjectivity and the vanishing
  of coboundary classes.
* `cupK` — the cohomology cup product, with `cupK_mk` (the class of the cochain
  cup) and naturality `cohPullbackK_cupK`.
* `oneK` — the unit class in `H^0`.
* `cohPullbackK` — the pullback along a continuous map, with
  `cohPullbackK_cocycleClassK`.
-/

open CategoryTheory Limits AlgebraicTopology
  GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
  GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation.CharClass

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

/-! ## 0. The cochain complex and the cohomology object -/

/-- The singular `K`-cochain complex of `X`. -/
abbrev cochainCxK (K : Type) [CommRing K] (X : TopCat.{0}) :
    CochainComplex (ModuleCat.{0} K) ℕ :=
  (singularCochainComplexFunctor K (ModuleCat.of K K)).obj (Opposite.op X)

/-- `H^n(X; K)`, the `n`-th singular cohomology of `X` with coefficients in the
commutative ring `K`. -/
abbrev cohomologyK (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} K :=
  (cochainCxK K X).homology n

/-! ## 1. Cohomology class of a cocycle -/

/-- The cohomology class of a cocycle `φ` (a `n`-cochain with `δφ = 0`). -/
def cocycleClassK (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup K X n) (hφ : cochainCoboundary K X n φ = 0) :
    cohomologyK K X n :=
  ((cochainCxK K X).homologyπ n).hom
    ((cochainCxK K X).cyclesMk φ (n + 1) (by simp [ComplexShape.next]) hφ)

/-- The class only depends on the cochain, not on the cocycle proof. -/
theorem cocycleClassK_congr (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ)
    {φ φ' : singularCochainGroup K X n} (h : φ = φ')
    (hφ : cochainCoboundary K X n φ = 0) (hφ' : cochainCoboundary K X n φ' = 0) :
    cocycleClassK K X n φ hφ = cocycleClassK K X n φ' hφ' := by
  subst h; rfl

/-- The `iCycles` of a cycle is a cocycle. -/
theorem cochainCoboundary_iCyclesK (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ)
    (c : (cochainCxK K X).cycles n) :
    cochainCoboundary K X n (((cochainCxK K X).iCycles n).hom c) = 0 := by
  have h := (cochainCxK K X).iCycles_d n (n + 1)
  change ((cochainCxK K X).iCycles n ≫ (cochainCxK K X).d n (n + 1)).hom c = 0
  rw [h]; rfl

theorem iCycles_cyclesMkK (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup K X n) (hφ : cochainCoboundary K X n φ = 0) :
    ((cochainCxK K X).iCycles n).hom
      ((cochainCxK K X).cyclesMk φ (n + 1) (by simp [ComplexShape.next]) hφ) = φ :=
  (cochainCxK K X).i_cyclesMk _ _ _ _

/-- `cyclesMk (iCycles c) = c`. -/
theorem cyclesMk_iCyclesK (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ)
    (c : (cochainCxK K X).cycles n) :
    (cochainCxK K X).cyclesMk (((cochainCxK K X).iCycles n).hom c) (n + 1)
        (by simp [ComplexShape.next]) (cochainCoboundary_iCyclesK K X n c) = c := by
  apply (ModuleCat.mono_iff_injective ((cochainCxK K X).iCycles n)).1 inferInstance
  exact (cochainCxK K X).i_cyclesMk _ _ _ _

/-- Every cohomology class is the class of a cocycle. -/
theorem cocycleClassK_surjective (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ)
    (a : cohomologyK K X n) :
    ∃ (φ : singularCochainGroup K X n) (hφ : cochainCoboundary K X n φ = 0),
      cocycleClassK K X n φ hφ = a := by
  have hepi : Function.Surjective ((cochainCxK K X).homologyπ n).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  obtain ⟨c, hc⟩ := hepi a
  refine ⟨((cochainCxK K X).iCycles n).hom c, cochainCoboundary_iCyclesK K X n c, ?_⟩
  rw [cocycleClassK, cyclesMk_iCyclesK, hc]

/-- The zero cochain has zero class. -/
theorem cocycleClassK_zero (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ)
    (h0 : cochainCoboundary K X n (0 : singularCochainGroup K X n) = 0) :
    cocycleClassK K X n 0 h0 = 0 := by
  rw [cocycleClassK]
  have h : (cochainCxK K X).cyclesMk (0 : singularCochainGroup K X n) (n + 1)
      (by simp [ComplexShape.next]) h0 = 0 := by
    apply (ModuleCat.mono_iff_injective ((cochainCxK K X).iCycles n)).1 inferInstance
    rw [map_zero]
    exact (cochainCxK K X).i_cyclesMk _ _ _ _
  rw [h, map_zero]

/-- `δ ∘ δ = 0`. -/
theorem cochainCoboundary_cochainCoboundaryK (K : Type) [CommRing K] (X : TopCat.{0}) (m : ℕ)
    (η : singularCochainGroup K X m) :
    cochainCoboundary K X (m + 1) (cochainCoboundary K X m η) = 0 := by
  change ((cochainCxK K X).d m (m + 1) ≫ (cochainCxK K X).d (m + 1) (m + 2)).hom η = 0
  rw [(cochainCxK K X).d_comp_d]; rfl

/-- A coboundary has zero cohomology class. -/
theorem cocycleClassK_coboundary_zero (K : Type) [CommRing K] (X : TopCat.{0}) (m : ℕ)
    (η : singularCochainGroup K X m)
    (hcoc : cochainCoboundary K X (m + 1) (cochainCoboundary K X m η) = 0) :
    cocycleClassK K X (m + 1) (cochainCoboundary K X m η) hcoc = 0 := by
  have h : (cochainCxK K X).cyclesMk (cochainCoboundary K X m η) (m + 2)
      (by simp [ComplexShape.next]) hcoc = (cochainCxK K X).toCycles m (m + 1) η := by
    apply (ModuleCat.mono_iff_injective ((cochainCxK K X).iCycles (m + 1))).1 inferInstance
    change ((forget₂ (ModuleCat K) Ab).map ((cochainCxK K X).iCycles (m + 1)))
        ((cochainCxK K X).cyclesMk (cochainCoboundary K X m η) (m + 2)
          (by simp [ComplexShape.next]) hcoc) = _
    rw [(cochainCxK K X).i_cyclesMk]
    change cochainCoboundary K X m η = _
    exact (ConcreteCategory.congr_hom ((cochainCxK K X).toCycles_i m (m + 1)).symm η)
  rw [cocycleClassK, h]
  change ((cochainCxK K X).toCycles m (m + 1) ≫ (cochainCxK K X).homologyπ (m + 1)).hom η = 0
  rw [HomologicalComplex.toCycles_comp_homologyπ]
  rfl

/-- Compatibility of `cocycleClassK` with the degree cast. -/
theorem cocycleClassK_cast (K : Type) [CommRing K] (X : TopCat.{0}) {m m' : ℕ} (h : m = m')
    (φ : singularCochainGroup K X m) (hφ : cochainCoboundary K X m φ = 0)
    (hφ' : cochainCoboundary K X m' (cochainCast h φ) = 0) :
    cocycleClassK K X m' (cochainCast h φ) hφ' =
      (eqToHom (by rw [h]) : cohomologyK K X m ⟶ cohomologyK K X m').hom
        (cocycleClassK K X m φ hφ) := by
  unfold cochainCast; aesop

/-- A degree-cast coboundary has zero cohomology class. -/
theorem cocycleClassK_cast_coboundary_zero (K : Type) [CommRing K] (X : TopCat.{0})
    (m m' : ℕ) (h : m + 1 = m') (η : singularCochainGroup K X m)
    (hcoc : cochainCoboundary K X m' (cochainCast h (cochainCoboundary K X m η)) = 0) :
    cocycleClassK K X m' (cochainCast h (cochainCoboundary K X m η)) hcoc = 0 := by
  rw [cocycleClassK_cast K X h (cochainCoboundary K X m η)
        (cochainCoboundary_cochainCoboundaryK K X m η) hcoc,
    cocycleClassK_coboundary_zero]
  simp

/-! ## 2. Cup with a fixed cocycle -/

/-- The cochain map `φ ↦ φ ⌣ ψ` as a `ModuleCat` morphism `C^p ⟶ C^{p+q}`. -/
def cupRightMorK (K : Type) [CommRing K] (X : TopCat.{0}) (p q : ℕ)
    (ψ : singularCochainGroup K X q) :
    (cochainCxK K X).X p ⟶ (cochainCxK K X).X (p + q) :=
  ModuleCat.ofHom
    { toFun := fun φ => cochainCup p q φ ψ
      map_add' := fun φ φ' => cochainCup_add_left p q φ φ' ψ
      map_smul' := fun s φ => cochainCup_smul_left p q s φ ψ }

@[simp] theorem cupRightMorK_hom (K : Type) [CommRing K] (X : TopCat.{0}) (p q : ℕ)
    (ψ : singularCochainGroup K X q) (φ : (cochainCxK K X).X p) :
    (cupRightMorK K X p q ψ).hom φ = cochainCup p q φ ψ := rfl

/-- The cochain map `ψ ↦ φ ⌣ ψ` as a `ModuleCat` morphism `C^q ⟶ C^{p+q}`. -/
def cupLeftFixedMorK (K : Type) [CommRing K] (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup K X p) :
    (cochainCxK K X).X q ⟶ (cochainCxK K X).X (p + q) :=
  ModuleCat.ofHom
    { toFun := fun ψ => cochainCup p q φ ψ
      map_add' := fun ψ ψ' => cochainCup_add_right p q φ ψ ψ'
      map_smul' := fun s ψ => cochainCup_smul_right p q s φ ψ }

@[simp] theorem cupLeftFixedMorK_hom (K : Type) [CommRing K] (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup K X p) (ψ : (cochainCxK K X).X q) :
    (cupLeftFixedMorK K X p q φ).hom ψ = cochainCup p q φ ψ := rfl

/-- The cup with a fixed cocycle on the right sends cycles to cocycles. -/
theorem cupRightK_cocycle_cond (K : Type) [CommRing K] (X : TopCat.{0}) (p q : ℕ)
    (ψ : singularCochainGroup K X q) (hψ : cochainCoboundary K X q ψ = 0) :
    ((cochainCxK K X).iCycles p ≫ cupRightMorK K X p q ψ) ≫
        (cochainCxK K X).d (p + q) (p + q + 1) = 0 := by
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro c
  show cochainCoboundary K X (p + q)
      (cochainCup p q (((cochainCxK K X).iCycles p).hom c) ψ) = 0
  exact cochainCup_respects_cocycles p q _ ψ (cochainCoboundary_iCyclesK K X p c) hψ

/-- The cup with a fixed cocycle on the left sends cycles to cocycles. -/
theorem cupLeftFixedK_cocycle_cond (K : Type) [CommRing K] (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup K X p) (hφ : cochainCoboundary K X p φ = 0) :
    ((cochainCxK K X).iCycles q ≫ cupLeftFixedMorK K X p q φ) ≫
        (cochainCxK K X).d (p + q) (p + q + 1) = 0 := by
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro c
  show cochainCoboundary K X (p + q)
      (cochainCup p q φ (((cochainCxK K X).iCycles q).hom c)) = 0
  exact cochainCup_respects_cocycles p q φ _ hφ (cochainCoboundary_iCyclesK K X q c)

/-- Cup with a fixed right cocycle, from cycles to cohomology. -/
def cupLeftMorK (K : Type) [CommRing K] (X : TopCat.{0}) (p q : ℕ)
    (ψ : singularCochainGroup K X q) (hψ : cochainCoboundary K X q ψ = 0) :
    (cochainCxK K X).cycles p ⟶ cohomologyK K X (p + q) :=
  (cochainCxK K X).liftCycles ((cochainCxK K X).iCycles p ≫ cupRightMorK K X p q ψ)
      (p + q + 1) (by simp [ComplexShape.next]) (cupRightK_cocycle_cond K X p q ψ hψ)
    ≫ (cochainCxK K X).homologyπ (p + q)

/-- Cup with a fixed left cocycle, from cycles to cohomology. -/
def cupRightMorK' (K : Type) [CommRing K] (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup K X p) (hφ : cochainCoboundary K X p φ = 0) :
    (cochainCxK K X).cycles q ⟶ cohomologyK K X (p + q) :=
  (cochainCxK K X).liftCycles ((cochainCxK K X).iCycles q ≫ cupLeftFixedMorK K X p q φ)
      (p + q + 1) (by simp [ComplexShape.next]) (cupLeftFixedK_cocycle_cond K X p q φ hφ)
    ≫ (cochainCxK K X).homologyπ (p + q)

theorem cupLeftMorK_cyclesMk (K : Type) [CommRing K] (X : TopCat.{0}) (p q : ℕ)
    (ψ : singularCochainGroup K X q) (hψ : cochainCoboundary K X q ψ = 0)
    (φ : singularCochainGroup K X p) (hφ : cochainCoboundary K X p φ = 0) :
    (cupLeftMorK K X p q ψ hψ).hom
        ((cochainCxK K X).cyclesMk φ (p + 1) (by simp [ComplexShape.next]) hφ)
      = cocycleClassK K X (p + q) (cochainCup p q φ ψ)
          (cochainCup_respects_cocycles p q φ ψ hφ hψ) := by
  unfold cupLeftMorK cocycleClassK
  simp only [ModuleCat.comp_apply]
  apply congrArg ((cochainCxK K X).homologyπ (p + q)).hom
  apply (ModuleCat.mono_iff_injective ((cochainCxK K X).iCycles (p + q))).1 inferInstance
  calc
    _ = ((cochainCxK K X).iCycles p ≫ cupRightMorK K X p q ψ).hom
          ((cochainCxK K X).cyclesMk φ (p + 1) (by simp [ComplexShape.next]) hφ) :=
      ConcreteCategory.congr_hom
        ((cochainCxK K X).liftCycles_i
          ((cochainCxK K X).iCycles p ≫ cupRightMorK K X p q ψ)
          (p + q + 1) (by simp [ComplexShape.next]) (cupRightK_cocycle_cond K X p q ψ hψ)) _
    _ = cochainCup p q φ ψ := by
      rw [ModuleCat.comp_apply, cupRightMorK_hom, iCycles_cyclesMkK]
    _ = _ := ((cochainCxK K X).i_cyclesMk _ _ _ _).symm

theorem cupRightMorK'_cyclesMk (K : Type) [CommRing K] (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup K X p) (hφ : cochainCoboundary K X p φ = 0)
    (ψ : singularCochainGroup K X q) (hψ : cochainCoboundary K X q ψ = 0) :
    (cupRightMorK' K X p q φ hφ).hom
        ((cochainCxK K X).cyclesMk ψ (q + 1) (by simp [ComplexShape.next]) hψ)
      = cocycleClassK K X (p + q) (cochainCup p q φ ψ)
          (cochainCup_respects_cocycles p q φ ψ hφ hψ) := by
  unfold cupRightMorK' cocycleClassK
  simp only [ModuleCat.comp_apply]
  apply congrArg ((cochainCxK K X).homologyπ (p + q)).hom
  apply (ModuleCat.mono_iff_injective ((cochainCxK K X).iCycles (p + q))).1 inferInstance
  calc
    _ = ((cochainCxK K X).iCycles q ≫ cupLeftFixedMorK K X p q φ).hom
          ((cochainCxK K X).cyclesMk ψ (q + 1) (by simp [ComplexShape.next]) hψ) :=
      ConcreteCategory.congr_hom
        ((cochainCxK K X).liftCycles_i
          ((cochainCxK K X).iCycles q ≫ cupLeftFixedMorK K X p q φ)
          (p + q + 1) (by simp [ComplexShape.next]) (cupLeftFixedK_cocycle_cond K X p q φ hφ)) _
    _ = cochainCup p q φ ψ := by
      rw [ModuleCat.comp_apply, cupLeftFixedMorK_hom, iCycles_cyclesMkK]
    _ = _ := ((cochainCxK K X).i_cyclesMk _ _ _ _).symm

theorem cupLeftMorK_apply (K : Type) [CommRing K] (X : TopCat.{0}) (p q : ℕ)
    (ψ : singularCochainGroup K X q) (hψ : cochainCoboundary K X q ψ = 0)
    (c : (cochainCxK K X).cycles p) :
    (cupLeftMorK K X p q ψ hψ).hom c
      = cocycleClassK K X (p + q) (cochainCup p q (((cochainCxK K X).iCycles p).hom c) ψ)
          (cochainCup_respects_cocycles p q _ ψ (cochainCoboundary_iCyclesK K X p c) hψ) := by
  conv_lhs => rw [← cyclesMk_iCyclesK K X p c]
  exact cupLeftMorK_cyclesMk K X p q ψ hψ (((cochainCxK K X).iCycles p).hom c)
    (cochainCoboundary_iCyclesK K X p c)

theorem cupRightMorK'_apply (K : Type) [CommRing K] (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup K X p) (hφ : cochainCoboundary K X p φ = 0)
    (c : (cochainCxK K X).cycles q) :
    (cupRightMorK' K X p q φ hφ).hom c
      = cocycleClassK K X (p + q) (cochainCup p q φ (((cochainCxK K X).iCycles q).hom c))
          (cochainCup_respects_cocycles p q φ _ hφ (cochainCoboundary_iCyclesK K X q c)) := by
  conv_lhs => rw [← cyclesMk_iCyclesK K X q c]
  exact cupRightMorK'_cyclesMk K X p q φ hφ (((cochainCxK K X).iCycles q).hom c)
    (cochainCoboundary_iCyclesK K X q c)

/-- If two cochains are equal and one has zero class, so does the other. -/
theorem cocycleClassK_eq_zero_of_eq (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ)
    {φ φ' : singularCochainGroup K X n} (h : φ = φ')
    (hφ : cochainCoboundary K X n φ = 0) (hφ' : cochainCoboundary K X n φ' = 0)
    (h0 : cocycleClassK K X n φ' hφ' = 0) :
    cocycleClassK K X n φ hφ = 0 :=
  (cocycleClassK_congr K X n h hφ hφ').trans h0

/-- The cup of a coboundary `δη` (left factor) with a cocycle `ψ` has zero class. -/
theorem cocycleClassK_cup_coboundary_left_zero (K : Type) [CommRing K] (X : TopCat.{0})
    (m q : ℕ) (η : singularCochainGroup K X m) (ψ : singularCochainGroup K X q)
    (hψ : cochainCoboundary K X q ψ = 0)
    (hcoc : cochainCoboundary K X (m + 1 + q)
        (cochainCup (m + 1) q (cochainCoboundary K X m η) ψ) = 0) :
    cocycleClassK K X (m + 1 + q)
        (cochainCup (m + 1) q (cochainCoboundary K X m η) ψ) hcoc = 0 := by
  refine cocycleClassK_eq_zero_of_eq K X (m + 1 + q)
    (cochainCup_coboundary_left' m q η ψ hψ) hcoc ?_ ?_
  · rw [← cochainCup_coboundary_left' m q η ψ hψ]; exact hcoc
  · exact cocycleClassK_cast_coboundary_zero K X (m + q) (m + 1 + q) (aw_degree_left_succ m q).symm
      (cochainCup m q η ψ) _

/-- The cup of a cocycle `φ` with a coboundary `δη` (right factor) has zero class. -/
theorem cocycleClassK_cup_coboundary_right_zero (K : Type) [CommRing K] (X : TopCat.{0})
    (p m : ℕ) (φ : singularCochainGroup K X p) (hφ : cochainCoboundary K X p φ = 0)
    (η : singularCochainGroup K X m)
    (hcoc : cochainCoboundary K X (p + (m + 1))
        (cochainCup p (m + 1) φ (cochainCoboundary K X m η)) = 0) :
    cocycleClassK K X (p + (m + 1))
        (cochainCup p (m + 1) φ (cochainCoboundary K X m η)) hcoc = 0 := by
  refine cocycleClassK_eq_zero_of_eq K X (p + (m + 1))
    (cochainCup_coboundary_right' p m φ η hφ) hcoc ?_ ?_
  · rw [← cochainCup_coboundary_right' p m φ η hφ]; exact hcoc
  · exact cocycleClassK_cast_coboundary_zero K X (p + m) (p + (m + 1))
      (aw_degree_right_succ p m).symm ((-1 : K) ^ p • cochainCup p m φ η) _

/-- The cup of `(d_i p).hom η` (left factor) with a cocycle `ψ` has zero class. -/
theorem cocycleClassK_cup_d_left_zero (K : Type) [CommRing K] (X : TopCat.{0}) (q i p : ℕ)
    (η : (cochainCxK K X).X i) (ψ : singularCochainGroup K X q)
    (hψ : cochainCoboundary K X q ψ = 0)
    (hcoc : cochainCoboundary K X (p + q)
        (cochainCup p q (((cochainCxK K X).d i p).hom η) ψ) = 0) :
    cocycleClassK K X (p + q) (cochainCup p q (((cochainCxK K X).d i p).hom η) ψ) hcoc = 0 := by
  by_cases h : (ComplexShape.up ℕ).Rel i p
  · obtain rfl : i + 1 = p := h
    exact cocycleClassK_cup_coboundary_left_zero K X i q η ψ hψ hcoc
  · have hz : cochainCup p q (((cochainCxK K X).d i p).hom η) ψ = 0 := by
      rw [(cochainCxK K X).shape i p h]; simp
    exact cocycleClassK_eq_zero_of_eq K X (p + q) hz hcoc (map_zero _)
      (cocycleClassK_zero K X (p + q) (map_zero _))

/-- The cup of a cocycle `φ` with `(d_i q).hom η` (right factor) has zero class. -/
theorem cocycleClassK_cup_d_right_zero (K : Type) [CommRing K] (X : TopCat.{0}) (p i q : ℕ)
    (φ : singularCochainGroup K X p) (hφ : cochainCoboundary K X p φ = 0)
    (η : (cochainCxK K X).X i)
    (hcoc : cochainCoboundary K X (p + q)
        (cochainCup p q φ (((cochainCxK K X).d i q).hom η)) = 0) :
    cocycleClassK K X (p + q) (cochainCup p q φ (((cochainCxK K X).d i q).hom η)) hcoc = 0 := by
  by_cases h : (ComplexShape.up ℕ).Rel i q
  · obtain rfl : i + 1 = q := h
    exact cocycleClassK_cup_coboundary_right_zero K X p i φ hφ η hcoc
  · have hz : cochainCup p q φ (((cochainCxK K X).d i q).hom η) = 0 := by
      rw [(cochainCxK K X).shape i q h]; simp
    exact cocycleClassK_eq_zero_of_eq K X (p + q) hz hcoc (map_zero _)
      (cocycleClassK_zero K X (p + q) (map_zero _))

/-- The cup-with-right-cocycle map kills coboundaries (cokernel condition). -/
theorem cupLeftMorK_toCycles (K : Type) [CommRing K] (X : TopCat.{0}) (p q : ℕ)
    (ψ : singularCochainGroup K X q) (hψ : cochainCoboundary K X q ψ = 0) :
    (cochainCxK K X).toCycles ((ComplexShape.up ℕ).prev p) p ≫ cupLeftMorK K X p q ψ hψ = 0 := by
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro η
  show (cupLeftMorK K X p q ψ hψ).hom
      (((cochainCxK K X).toCycles ((ComplexShape.up ℕ).prev p) p).hom η) = 0
  rw [cupLeftMorK_apply]
  have heq : cochainCup p q (((cochainCxK K X).iCycles p).hom
        (((cochainCxK K X).toCycles ((ComplexShape.up ℕ).prev p) p).hom η)) ψ
      = cochainCup p q (((cochainCxK K X).d ((ComplexShape.up ℕ).prev p) p).hom η) ψ := by
    rw [← ModuleCat.comp_apply, (cochainCxK K X).toCycles_i]
  refine cocycleClassK_eq_zero_of_eq K X (p + q) heq _ ?_ ?_
  · rw [← heq]
    exact cochainCup_respects_cocycles p q _ ψ (cochainCoboundary_iCyclesK K X p _) hψ
  · exact cocycleClassK_cup_d_left_zero K X q ((ComplexShape.up ℕ).prev p) p η ψ hψ _

/-- The cup-with-left-cocycle map kills coboundaries (cokernel condition). -/
theorem cupRightMorK'_toCycles (K : Type) [CommRing K] (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup K X p) (hφ : cochainCoboundary K X p φ = 0) :
    (cochainCxK K X).toCycles ((ComplexShape.up ℕ).prev q) q ≫ cupRightMorK' K X p q φ hφ = 0 := by
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro η
  show (cupRightMorK' K X p q φ hφ).hom
      (((cochainCxK K X).toCycles ((ComplexShape.up ℕ).prev q) q).hom η) = 0
  rw [cupRightMorK'_apply]
  have heq : cochainCup p q φ (((cochainCxK K X).iCycles q).hom
        (((cochainCxK K X).toCycles ((ComplexShape.up ℕ).prev q) q).hom η))
      = cochainCup p q φ (((cochainCxK K X).d ((ComplexShape.up ℕ).prev q) q).hom η) := by
    rw [← ModuleCat.comp_apply, (cochainCxK K X).toCycles_i]
  refine cocycleClassK_eq_zero_of_eq K X (p + q) heq _ ?_ ?_
  · rw [← heq]
    exact cochainCup_respects_cocycles p q φ _ hφ (cochainCoboundary_iCyclesK K X q _)
  · exact cocycleClassK_cup_d_right_zero K X p ((ComplexShape.up ℕ).prev q) q φ hφ η _

/-! ## 3. Descent to cohomology in each variable -/

/-- Cup with a fixed right cocycle, descended to `H^p ⟶ H^{p+q}`. -/
def cupHomologyLeftK (K : Type) [CommRing K] (X : TopCat.{0}) (p q : ℕ)
    (ψ : singularCochainGroup K X q) (hψ : cochainCoboundary K X q ψ = 0) :
    cohomologyK K X p ⟶ cohomologyK K X (p + q) :=
  ((cochainCxK K X).homologyIsCokernel ((ComplexShape.up ℕ).prev p) p rfl).desc
    (CokernelCofork.ofπ (cupLeftMorK K X p q ψ hψ) (cupLeftMorK_toCycles K X p q ψ hψ))

/-- Cup with a fixed left cocycle, descended to `H^q ⟶ H^{p+q}`. -/
def cupHomologyRightK (K : Type) [CommRing K] (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup K X p) (hφ : cochainCoboundary K X p φ = 0) :
    cohomologyK K X q ⟶ cohomologyK K X (p + q) :=
  ((cochainCxK K X).homologyIsCokernel ((ComplexShape.up ℕ).prev q) q rfl).desc
    (CokernelCofork.ofπ (cupRightMorK' K X p q φ hφ) (cupRightMorK'_toCycles K X p q φ hφ))

theorem homologyπ_cupHomologyLeftK (K : Type) [CommRing K] (X : TopCat.{0}) (p q : ℕ)
    (ψ : singularCochainGroup K X q) (hψ : cochainCoboundary K X q ψ = 0) :
    (cochainCxK K X).homologyπ p ≫ cupHomologyLeftK K X p q ψ hψ = cupLeftMorK K X p q ψ hψ :=
  ((cochainCxK K X).homologyIsCokernel ((ComplexShape.up ℕ).prev p) p rfl).fac
    (CokernelCofork.ofπ (cupLeftMorK K X p q ψ hψ) (cupLeftMorK_toCycles K X p q ψ hψ))
    WalkingParallelPair.one

theorem homologyπ_cupHomologyRightK (K : Type) [CommRing K] (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup K X p) (hφ : cochainCoboundary K X p φ = 0) :
    (cochainCxK K X).homologyπ q ≫ cupHomologyRightK K X p q φ hφ = cupRightMorK' K X p q φ hφ :=
  ((cochainCxK K X).homologyIsCokernel ((ComplexShape.up ℕ).prev q) q rfl).fac
    (CokernelCofork.ofπ (cupRightMorK' K X p q φ hφ) (cupRightMorK'_toCycles K X p q φ hφ))
    WalkingParallelPair.one

/-- `cupHomologyLeftK` on the class of `φ` is the class of `φ ⌣ ψ`. -/
theorem cupHomologyLeftK_apply (K : Type) [CommRing K] (X : TopCat.{0}) (p q : ℕ)
    (ψ : singularCochainGroup K X q) (hψ : cochainCoboundary K X q ψ = 0)
    (φ : singularCochainGroup K X p) (hφ : cochainCoboundary K X p φ = 0) :
    (cupHomologyLeftK K X p q ψ hψ).hom (cocycleClassK K X p φ hφ)
      = cocycleClassK K X (p + q) (cochainCup p q φ ψ)
          (cochainCup_respects_cocycles p q φ ψ hφ hψ) := by
  rw [cocycleClassK,
    show (cupHomologyLeftK K X p q ψ hψ).hom
          (((cochainCxK K X).homologyπ p).hom
            ((cochainCxK K X).cyclesMk φ (p + 1) (by simp [ComplexShape.next]) hφ))
        = ((cochainCxK K X).homologyπ p ≫ cupHomologyLeftK K X p q ψ hψ).hom
            ((cochainCxK K X).cyclesMk φ (p + 1) (by simp [ComplexShape.next]) hφ) from rfl,
    homologyπ_cupHomologyLeftK, cupLeftMorK_cyclesMk]

/-- `cupHomologyRightK` on the class of `ψ` is the class of `φ ⌣ ψ`. -/
theorem cupHomologyRightK_apply (K : Type) [CommRing K] (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup K X p) (hφ : cochainCoboundary K X p φ = 0)
    (ψ : singularCochainGroup K X q) (hψ : cochainCoboundary K X q ψ = 0) :
    (cupHomologyRightK K X p q φ hφ).hom (cocycleClassK K X q ψ hψ)
      = cocycleClassK K X (p + q) (cochainCup p q φ ψ)
          (cochainCup_respects_cocycles p q φ ψ hφ hψ) := by
  rw [cocycleClassK,
    show (cupHomologyRightK K X p q φ hφ).hom
          (((cochainCxK K X).homologyπ q).hom
            ((cochainCxK K X).cyclesMk ψ (q + 1) (by simp [ComplexShape.next]) hψ))
        = ((cochainCxK K X).homologyπ q ≫ cupHomologyRightK K X p q φ hφ).hom
            ((cochainCxK K X).cyclesMk ψ (q + 1) (by simp [ComplexShape.next]) hψ) from rfl,
    homologyπ_cupHomologyRightK, cupRightMorK'_cyclesMk]

/-! ## 4. The cohomology cup product -/

/-- The chosen cycle representative of a cohomology class. -/
def classCycleReprK (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ) (a : cohomologyK K X n) :
    (cochainCxK K X).cycles n :=
  Function.surjInv
    ((ModuleCat.epi_iff_surjective ((cochainCxK K X).homologyπ n)).1 inferInstance) a

theorem homologyπ_classCycleReprK (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ)
    (a : cohomologyK K X n) :
    ((cochainCxK K X).homologyπ n).hom (classCycleReprK K X n a) = a :=
  Function.surjInv_eq
    ((ModuleCat.epi_iff_surjective ((cochainCxK K X).homologyπ n)).1 inferInstance) a

/-- A chosen cocycle representative of a cohomology class. -/
def classReprK (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ) (a : cohomologyK K X n) :
    singularCochainGroup K X n :=
  ((cochainCxK K X).iCycles n).hom (classCycleReprK K X n a)

theorem classReprK_isCocycle (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ)
    (a : cohomologyK K X n) : cochainCoboundary K X n (classReprK K X n a) = 0 :=
  cochainCoboundary_iCyclesK K X n (classCycleReprK K X n a)

theorem cocycleClassK_classReprK (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ)
    (a : cohomologyK K X n) :
    cocycleClassK K X n (classReprK K X n a) (classReprK_isCocycle K X n a) = a := by
  rw [cocycleClassK,
    show (cochainCxK K X).cyclesMk (classReprK K X n a) (n + 1) (by simp [ComplexShape.next])
          (classReprK_isCocycle K X n a)
        = classCycleReprK K X n a from cyclesMk_iCyclesK K X n (classCycleReprK K X n a)]
  exact homologyπ_classCycleReprK K X n a

/-- The **cohomology-level cup product** `H^p(X; K) → H^q(X; K) → H^{p+q}(X; K)`. -/
def cupK {K : Type} [CommRing K] {X : TopCat.{0}} {p q : ℕ}
    (a : cohomologyK K X p) (b : cohomologyK K X q) : cohomologyK K X (p + q) :=
  (cupHomologyLeftK K X p q (classReprK K X q b) (classReprK_isCocycle K X q b)).hom a

/-- **Well-definedness / computation rule.** -/
theorem cupK_mk {K : Type} [CommRing K] {X : TopCat.{0}} {p q : ℕ}
    (φ : singularCochainGroup K X p) (hφ : cochainCoboundary K X p φ = 0)
    (ψ : singularCochainGroup K X q) (hψ : cochainCoboundary K X q ψ = 0) :
    cupK (cocycleClassK K X p φ hφ) (cocycleClassK K X q ψ hψ)
      = cocycleClassK K X (p + q) (cochainCup p q φ ψ)
          (cochainCup_respects_cocycles p q φ ψ hφ hψ) := by
  rw [cupK, cupHomologyLeftK_apply]
  have key := cupHomologyRightK_apply K X p q φ hφ
    (classReprK K X q (cocycleClassK K X q ψ hψ)) (classReprK_isCocycle K X q _)
  rw [cocycleClassK_classReprK] at key
  have key2 := cupHomologyRightK_apply K X p q φ hφ ψ hψ
  rw [← key, ← key2]

/-! ## 5. The pullback and naturality -/

/-- The pullback `f^* : H^n(Y; K) ⟶ H^n(X; K)` of a continuous map `f : X ⟶ Y`. -/
def cohPullbackK (K : Type) [CommRing K] {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    cohomologyK K Y n ⟶ cohomologyK K X n :=
  (singularCohomologyFunctor K (ModuleCat.of K K) n).map f.op

/-- The cochain pullback commutes with the coboundary. -/
theorem cochainPullback_cochainCoboundaryK (K : Type) [CommRing K] {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) (φ : singularCochainGroup K Y n) :
    cochainCoboundary K X n (cochainPullback f n φ)
      = cochainPullback f (n + 1) (cochainCoboundary K Y n φ) := by
  have hcomm := ((singularCochainComplexFunctor K (ModuleCat.of K K)).map f.op).comm n (n + 1)
  change ((cochainCxK K X).d n (n + 1)).hom
      ((((singularCochainComplexFunctor K (ModuleCat.of K K)).map f.op).f n).hom φ) = _
  rw [← ModuleCat.comp_apply, hcomm]
  rfl

/-- The cochain pullback of a cocycle is a cocycle. -/
theorem cochainPullback_cocycleK (K : Type) [CommRing K] {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (φ : singularCochainGroup K Y n) (hφ : cochainCoboundary K Y n φ = 0) :
    cochainCoboundary K X n (cochainPullback f n φ) = 0 := by
  rw [cochainPullback_cochainCoboundaryK, hφ]
  show (((singularCochainComplexFunctor K (ModuleCat.of K K)).map f.op).f (n + 1)).hom 0 = 0
  rw [map_zero]

/-- The pullback of the class of a cocycle is the class of the pullback cochain. -/
theorem cohPullbackK_cocycleClassK (K : Type) [CommRing K] {X Y : TopCat.{0}} (f : X ⟶ Y)
    (n : ℕ) (φ : singularCochainGroup K Y n) (hφ : cochainCoboundary K Y n φ = 0) :
    (cohPullbackK K f n).hom (cocycleClassK K Y n φ hφ)
      = cocycleClassK K X n (cochainPullback f n φ) (cochainPullback_cocycleK K f n φ hφ) := by
  unfold cocycleClassK
  rw [show (ModuleCat.Hom.hom (cohPullbackK K f n))
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          ((singularCochainComplexFunctor K (ModuleCat.of K K)).map f.op) n)) from rfl]
  rw [← ModuleCat.comp_apply, HomologicalComplex.homologyπ_naturality, ModuleCat.comp_apply]
  apply congrArg ((cochainCxK K X).homologyπ n).hom
  apply (ModuleCat.mono_iff_injective ((cochainCxK K X).iCycles n)).1 inferInstance
  calc
    _ = (((cochainCxK K Y).iCycles n ≫
          ((singularCochainComplexFunctor K (ModuleCat.of K K)).map f.op).f n).hom)
          ((cochainCxK K Y).cyclesMk φ (n + 1) (by simp [ComplexShape.next]) hφ) :=
      ConcreteCategory.congr_hom
        (HomologicalComplex.cyclesMap_i
          ((singularCochainComplexFunctor K (ModuleCat.of K K)).map f.op) n) _
    _ = cochainPullback f n φ := by
      rw [ModuleCat.comp_apply, iCycles_cyclesMkK]
      rfl
    _ = _ := (iCycles_cyclesMkK K X n _ _).symm

/-- **Naturality of the cup product.** `f^*(a ⌣ b) = f^* a ⌣ f^* b`. -/
theorem cohPullbackK_cupK (K : Type) [CommRing K] {X Y : TopCat.{0}} (f : X ⟶ Y) (p q : ℕ)
    (a : cohomologyK K Y p) (b : cohomologyK K Y q) :
    (cohPullbackK K f (p + q)).hom (cupK a b)
      = cupK ((cohPullbackK K f p).hom a) ((cohPullbackK K f q).hom b) := by
  obtain ⟨φ, hφ, rfl⟩ := cocycleClassK_surjective K Y p a
  obtain ⟨ψ, hψ, rfl⟩ := cocycleClassK_surjective K Y q b
  rw [cupK_mk, cohPullbackK_cocycleClassK, cohPullbackK_cocycleClassK,
    cohPullbackK_cocycleClassK, cupK_mk]
  exact cocycleClassK_congr K X (p + q) (cochainCup_naturality f p q φ ψ) _ _

/-! ## 6. The unit -/

/-- The unit cochain is a cocycle.  Over `ZMod 2` this is `1 + 1 = 0`; over a
general ring it is `(-1)^0 + (-1)^1 = 0`. -/
theorem cochainCoboundary_cochainOneK (K : Type) [CommRing K] (X : TopCat.{0}) :
    cochainCoboundary K X 0 (cochainOne (R := K) (Z := X)) = 0 := by
  apply cochain_ext; intro σ
  rw [cochainCoboundary_eval, cochainEval_zero]
  simp only [cochainOne_eval, mul_one]
  show ∑ x : Fin 2, (-1 : K) ^ (x : ℕ) = 0
  rw [Fin.sum_univ_two]
  simp

/-- The unit class `1 ∈ H^0(X; K)`. -/
def oneK (K : Type) [CommRing K] (X : TopCat.{0}) : cohomologyK K X 0 :=
  cocycleClassK K X 0 (cochainOne (R := K) (Z := X)) (cochainCoboundary_cochainOneK K X)

/-! ## 7. The `ZMod 2` instance is the vendored one

Each bridge below is `rfl`: the generic declarations are *definitionally* the
vendored `ZMod 2` ones, so the `F₂` layer and the files that speak the vendored
vocabulary (`cocycleClass`, `cohPullback`, …) are unaffected by this file. -/

theorem cohomologyK_zmod2 (X : TopCat.{0}) (n : ℕ) :
    cohomologyK (ZMod 2) X n = cohomologyZMod2 X n := rfl

theorem cocycleClassK_zmod2 (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) X n) (hφ : cochainCoboundary (ZMod 2) X n φ = 0) :
    cocycleClassK (ZMod 2) X n φ hφ = cocycleClass X n φ hφ := rfl

theorem cohPullbackK_zmod2 {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    cohPullbackK (ZMod 2) f n = cohPullback f n := rfl

end

end GroupApproximation.CharClass
