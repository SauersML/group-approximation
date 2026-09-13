import Mathlib.Analysis.Complex.Circle
import Mathlib.Data.Set.Card
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Homotopy.Basic

/-!
# Simple closed curves and their isotopy classes

The curve theory behind mapping class groups of surfaces, following Farb–Margalit, *A Primer on
Mapping Class Groups*, §1.2. Everything is stated for an arbitrary topological space `X`; a
surface is the case of interest.

* A *simple closed curve* in `X` is a continuous injective map `Circle → X`
  (`SimpleClosedCurve X`). In a Hausdorff space it is a closed embedding, because the circle is
  compact.
* An *isotopy* of simple closed curves is a homotopy through simple closed curves
  (`SimpleClosedCurve.Isotopic`). It is Mathlib's `ContinuousMap.HomotopicWith` with the predicate
  `Function.Injective`.
* Curves are unoriented: `γ` and `δ` are identified when `γ` is isotopic to `δ` or to `δ`
  reversed. `CurveClass X` is the quotient.
* The *geometric intersection number* `CurveClass.intersectionNumber a b ∈ ℕ∞` is the least number
  of intersection points of representatives of `a` and `b` (F–M §1.2.3), and the least value is
  attained. Farb–Margalit minimize over free homotopy classes; for simple closed curves the two
  agree by F–M Prop. 1.10, which is not proved here.

Homeomorphisms act on curves and on classes (`SimpleClosedCurve.map`, `CurveClass.map`), and the
intersection number is invariant. A homotopy through injective maps between two homeomorphisms
moves each curve to an isotopic one (`SimpleClosedCurve.isotopic_map_of_homotopyWith`), so isotopic
homeomorphisms act equally on classes (`CurveClass.map_eq_of_homotopyWith`).
-/

namespace GroupApproximation
namespace SurfaceCurves

open Topology unitInterval

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A time-slice of a homotopy through injective maps is injective. -/
theorem homotopyWith_injective_slice {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {f₀ f₁ : C(A, B)} (F : ContinuousMap.HomotopyWith f₀ f₁ fun f => Function.Injective f)
    (t : I) {a b : A} (h : F (t, a) = F (t, b)) : a = b :=
  F.prop t (show F.toHomotopy.curry t a = F.toHomotopy.curry t b from h)

/-- A simple closed curve in `X`: a continuous injective map from the circle
(Farb–Margalit §1.2.2). -/
structure SimpleClosedCurve (X : Type*) [TopologicalSpace X] extends C(Circle, X) where
  /-- The curve has no self-intersections. -/
  injective' : Function.Injective toFun

namespace SimpleClosedCurve

instance instFunLike : FunLike (SimpleClosedCurve X) Circle X where
  coe γ := γ.toFun
  coe_injective γ δ h := by
    obtain ⟨⟨_, _⟩, _⟩ := γ
    obtain ⟨⟨_, _⟩, _⟩ := δ
    congr

instance instContinuousMapClass : ContinuousMapClass (SimpleClosedCurve X) Circle X where
  map_continuous γ := γ.continuous_toFun

@[ext]
theorem ext {γ δ : SimpleClosedCurve X} (h : ∀ z, γ z = δ z) : γ = δ :=
  DFunLike.ext γ δ h

@[simp]
theorem coe_toContinuousMap (γ : SimpleClosedCurve X) : ⇑γ.toContinuousMap = γ :=
  rfl

protected theorem continuous (γ : SimpleClosedCurve X) : Continuous γ :=
  γ.continuous_toFun

protected theorem injective (γ : SimpleClosedCurve X) : Function.Injective γ :=
  γ.injective'

/-- In a Hausdorff space a simple closed curve is a closed embedding. -/
theorem isClosedEmbedding [T2Space X] (γ : SimpleClosedCurve X) : IsClosedEmbedding γ :=
  γ.continuous.isClosedEmbedding γ.injective

/-- The image of a simple closed curve. -/
def carrier (γ : SimpleClosedCurve X) : Set X :=
  Set.range γ

theorem mem_carrier {γ : SimpleClosedCurve X} {x : X} : x ∈ γ.carrier ↔ ∃ z, γ z = x :=
  Iff.rfl

theorem isCompact_carrier (γ : SimpleClosedCurve X) : IsCompact γ.carrier :=
  isCompact_range γ.continuous

theorem isClosed_carrier [T2Space X] (γ : SimpleClosedCurve X) : IsClosed γ.carrier :=
  γ.isCompact_carrier.isClosed

/-- The same curve traversed in the opposite direction. -/
noncomputable def reverse (γ : SimpleClosedCurve X) : SimpleClosedCurve X where
  toFun z := γ z⁻¹
  continuous_toFun := γ.continuous.comp continuous_inv
  injective' := γ.injective.comp inv_injective

@[simp]
theorem reverse_apply (γ : SimpleClosedCurve X) (z : Circle) : γ.reverse z = γ z⁻¹ :=
  rfl

@[simp]
theorem reverse_reverse (γ : SimpleClosedCurve X) : γ.reverse.reverse = γ :=
  ext fun z => by simp

@[simp]
theorem carrier_reverse (γ : SimpleClosedCurve X) : γ.reverse.carrier = γ.carrier :=
  inv_surjective.range_comp γ

/-- The image of a simple closed curve under a homeomorphism. -/
def map (h : X ≃ₜ Y) (γ : SimpleClosedCurve X) : SimpleClosedCurve Y where
  toFun z := h (γ z)
  continuous_toFun := h.continuous.comp γ.continuous
  injective' := h.injective.comp γ.injective

@[simp]
theorem map_apply (h : X ≃ₜ Y) (γ : SimpleClosedCurve X) (z : Circle) : γ.map h z = h (γ z) :=
  rfl

@[simp]
theorem map_refl (γ : SimpleClosedCurve X) : γ.map (Homeomorph.refl X) = γ :=
  ext fun _ => rfl

theorem map_trans (h₁ : X ≃ₜ Y) (h₂ : Y ≃ₜ Z) (γ : SimpleClosedCurve X) :
    γ.map (h₁.trans h₂) = (γ.map h₁).map h₂ :=
  ext fun _ => rfl

@[simp]
theorem map_symm_map (h : X ≃ₜ Y) (γ : SimpleClosedCurve X) : (γ.map h).map h.symm = γ :=
  ext fun z => h.symm_apply_apply (γ z)

@[simp]
theorem carrier_map (h : X ≃ₜ Y) (γ : SimpleClosedCurve X) : (γ.map h).carrier = h '' γ.carrier :=
  Set.range_comp h γ

theorem map_reverse (h : X ≃ₜ Y) (γ : SimpleClosedCurve X) : γ.reverse.map h = (γ.map h).reverse :=
  ext fun _ => rfl

/-- The number of intersection points of two simple closed curves, as a value in `ℕ∞`. -/
noncomputable def meetCount (γ δ : SimpleClosedCurve X) : ℕ∞ :=
  (γ.carrier ∩ δ.carrier).encard

theorem meetCount_comm (γ δ : SimpleClosedCurve X) : γ.meetCount δ = δ.meetCount γ := by
  simp only [meetCount]
  rw [Set.inter_comm]

theorem meetCount_eq_zero_iff {γ δ : SimpleClosedCurve X} :
    γ.meetCount δ = 0 ↔ Disjoint γ.carrier δ.carrier := by
  rw [meetCount, Set.encard_eq_zero, Set.disjoint_iff_inter_eq_empty]

@[simp]
theorem meetCount_map (h : X ≃ₜ Y) (γ δ : SimpleClosedCurve X) :
    (γ.map h).meetCount (δ.map h) = γ.meetCount δ := by
  simp only [meetCount, carrier_map]
  rw [← Set.image_inter h.injective, h.injective.encard_image]

@[simp]
theorem meetCount_reverse_left (γ δ : SimpleClosedCurve X) :
    γ.reverse.meetCount δ = γ.meetCount δ := by
  simp only [meetCount, carrier_reverse]

@[simp]
theorem meetCount_reverse_right (γ δ : SimpleClosedCurve X) :
    γ.meetCount δ.reverse = γ.meetCount δ := by
  simp only [meetCount, carrier_reverse]

/-- Two simple closed curves are *isotopic* when a homotopy through simple closed curves joins
them (Farb–Margalit §1.2.2). -/
def Isotopic (γ δ : SimpleClosedCurve X) : Prop :=
  ContinuousMap.HomotopicWith γ.toContinuousMap δ.toContinuousMap fun f => Function.Injective f

namespace Isotopic

variable {γ δ ε : SimpleClosedCurve X}

theorem refl (γ : SimpleClosedCurve X) : Isotopic γ γ :=
  ContinuousMap.HomotopicWith.refl _ γ.injective

theorem symm (h : Isotopic γ δ) : Isotopic δ γ :=
  ContinuousMap.HomotopicWith.symm h

theorem trans (h₁ : Isotopic γ δ) (h₂ : Isotopic δ ε) : Isotopic γ ε :=
  ContinuousMap.HomotopicWith.trans h₁ h₂

/-- Reversing both curves preserves isotopy. -/
theorem reverse (h : Isotopic γ δ) : Isotopic γ.reverse δ.reverse := by
  obtain ⟨F⟩ := h
  exact ⟨{ toFun := fun p => F (p.1, p.2⁻¹)
           continuous_toFun := F.continuous.comp (by fun_prop)
           map_zero_left := fun z => F.apply_zero z⁻¹
           map_one_left := fun z => F.apply_one z⁻¹
           prop' := fun t a b hab => inv_injective <|
             homotopyWith_injective_slice F t (show F (t, a⁻¹) = F (t, b⁻¹) from hab) }⟩

/-- A homeomorphism carries isotopic curves to isotopic curves. -/
theorem map (h : Isotopic γ δ) (e : X ≃ₜ Y) : Isotopic (γ.map e) (δ.map e) := by
  obtain ⟨F⟩ := h
  exact ⟨{ toFun := fun p => e (F p)
           continuous_toFun := e.continuous.comp F.continuous
           map_zero_left := fun z => congrArg e (F.apply_zero z)
           map_one_left := fun z => congrArg e (F.apply_one z)
           prop' := fun t a b hab => homotopyWith_injective_slice F t
             (e.injective (show e (F (t, a)) = e (F (t, b)) from hab)) }⟩

end Isotopic

/-- Homeomorphisms joined by a homotopy through injective maps move a simple closed curve to
isotopic curves. This is how a mapping class acts on isotopy classes of curves. -/
theorem isotopic_map_of_homotopyWith {f₀ f₁ : X ≃ₜ Y}
    (H : ContinuousMap.HomotopyWith (f₀ : C(X, Y)) (f₁ : C(X, Y))
      fun f => Function.Injective f)
    (γ : SimpleClosedCurve X) : Isotopic (γ.map f₀) (γ.map f₁) :=
  ⟨{ toFun := fun p => H (p.1, γ p.2)
     continuous_toFun := H.continuous.comp (continuous_fst.prodMk (γ.continuous.comp continuous_snd))
     map_zero_left := fun z => H.apply_zero (γ z)
     map_one_left := fun z => H.apply_one (γ z)
     prop' := fun t a b hab => γ.injective <|
       homotopyWith_injective_slice H t (show H (t, γ a) = H (t, γ b) from hab) }⟩

/-- Isotopy of unoriented simple closed curves: `γ` is isotopic to `δ` or to `δ` reversed. -/
def UnorientedIsotopic (γ δ : SimpleClosedCurve X) : Prop :=
  Isotopic γ δ ∨ Isotopic γ δ.reverse

theorem unorientedIsotopic_equivalence : Equivalence (UnorientedIsotopic (X := X)) where
  refl γ := Or.inl (Isotopic.refl γ)
  symm := by
    rintro γ δ (h | h)
    · exact Or.inl h.symm
    · refine Or.inr ?_
      simpa using h.reverse.symm
  trans := by
    rintro γ δ ε (h₁ | h₁) (h₂ | h₂)
    · exact Or.inl (h₁.trans h₂)
    · exact Or.inr (h₁.trans h₂)
    · exact Or.inr (h₁.trans h₂.reverse)
    · refine Or.inl (h₁.trans ?_)
      simpa using h₂.reverse

theorem unorientedIsotopic_reverse (γ : SimpleClosedCurve X) :
    UnorientedIsotopic γ γ.reverse :=
  Or.inr (by simpa using Isotopic.refl γ)

instance curveSetoid : Setoid (SimpleClosedCurve X) where
  r := UnorientedIsotopic
  iseqv := unorientedIsotopic_equivalence

theorem equiv_iff {γ δ : SimpleClosedCurve X} : γ ≈ δ ↔ UnorientedIsotopic γ δ :=
  Iff.rfl

end SimpleClosedCurve

/-- Isotopy classes of unoriented simple closed curves in `X`. -/
def CurveClass (X : Type*) [TopologicalSpace X] : Type _ :=
  Quotient (SimpleClosedCurve.curveSetoid (X := X))

namespace CurveClass

/-- The isotopy class of a simple closed curve. -/
def mk (γ : SimpleClosedCurve X) : CurveClass X :=
  Quotient.mk _ γ

theorem mk_surjective : Function.Surjective (mk : SimpleClosedCurve X → CurveClass X) :=
  fun a => Quotient.exists_rep (s := SimpleClosedCurve.curveSetoid) a

theorem mk_eq_mk {γ δ : SimpleClosedCurve X} :
    mk γ = mk δ ↔ SimpleClosedCurve.UnorientedIsotopic γ δ :=
  ⟨fun h => SimpleClosedCurve.equiv_iff.1 (Quotient.exact h),
    fun h => Quotient.sound (SimpleClosedCurve.equiv_iff.2 h)⟩

@[simp]
theorem mk_reverse (γ : SimpleClosedCurve X) : mk γ.reverse = mk γ :=
  (mk_eq_mk.2 (SimpleClosedCurve.unorientedIsotopic_reverse γ)).symm

/-- The action of a homeomorphism on isotopy classes of simple closed curves. -/
def map (h : X ≃ₜ Y) : CurveClass X → CurveClass Y :=
  Quotient.map (SimpleClosedCurve.map h) fun γ δ hγδ => by
    rcases SimpleClosedCurve.equiv_iff.1 hγδ with hγδ | hγδ
    · exact SimpleClosedCurve.equiv_iff.2 (Or.inl (hγδ.map h))
    · refine SimpleClosedCurve.equiv_iff.2 (Or.inr ?_)
      rw [← SimpleClosedCurve.map_reverse]
      exact hγδ.map h

@[simp]
theorem map_mk (h : X ≃ₜ Y) (γ : SimpleClosedCurve X) : map h (mk γ) = mk (γ.map h) :=
  rfl

@[simp]
theorem map_refl (a : CurveClass X) : map (Homeomorph.refl X) a = a := by
  obtain ⟨γ, rfl⟩ := mk_surjective a
  rw [map_mk, SimpleClosedCurve.map_refl]

theorem map_trans (h₁ : X ≃ₜ Y) (h₂ : Y ≃ₜ Z) (a : CurveClass X) :
    map (h₁.trans h₂) a = map h₂ (map h₁ a) := by
  obtain ⟨γ, rfl⟩ := mk_surjective a
  simp only [map_mk, SimpleClosedCurve.map_trans]

@[simp]
theorem map_symm_map (h : X ≃ₜ Y) (a : CurveClass X) : map h.symm (map h a) = a := by
  obtain ⟨γ, rfl⟩ := mk_surjective a
  rw [map_mk, map_mk, SimpleClosedCurve.map_symm_map]

/-- Isotopic homeomorphisms act equally on isotopy classes of simple closed curves. -/
theorem map_eq_of_homotopyWith {f₀ f₁ : X ≃ₜ Y}
    (H : ContinuousMap.HomotopyWith (f₀ : C(X, Y)) (f₁ : C(X, Y))
      fun f => Function.Injective f)
    (a : CurveClass X) : map f₀ a = map f₁ a := by
  obtain ⟨γ, rfl⟩ := mk_surjective a
  rw [map_mk, map_mk]
  exact mk_eq_mk.2 (Or.inl (SimpleClosedCurve.isotopic_map_of_homotopyWith H γ))

/-- The geometric intersection number of two isotopy classes of simple closed curves: the least
number of intersection points of representatives (Farb–Margalit §1.2.3). -/
noncomputable def intersectionNumber (a b : CurveClass X) : ℕ∞ :=
  sInf {n | ∃ γ δ : SimpleClosedCurve X, mk γ = a ∧ mk δ = b ∧ γ.meetCount δ = n}

theorem intersectionNumber_le_meetCount (γ δ : SimpleClosedCurve X) :
    intersectionNumber (mk γ) (mk δ) ≤ γ.meetCount δ :=
  sInf_le ⟨γ, δ, rfl, rfl, rfl⟩

/-- The geometric intersection number is realized by a pair of representatives. -/
theorem exists_meetCount_eq_intersectionNumber (a b : CurveClass X) :
    ∃ γ δ : SimpleClosedCurve X, mk γ = a ∧ mk δ = b ∧
      γ.meetCount δ = intersectionNumber a b := by
  obtain ⟨γ, rfl⟩ := mk_surjective a
  obtain ⟨δ, rfl⟩ := mk_surjective b
  have hne : {n | ∃ γ' δ' : SimpleClosedCurve X, mk γ' = mk γ ∧ mk δ' = mk δ ∧
      γ'.meetCount δ' = n}.Nonempty :=
    ⟨γ.meetCount δ, γ, δ, rfl, rfl, rfl⟩
  exact csInf_mem hne

theorem intersectionNumber_comm (a b : CurveClass X) :
    intersectionNumber a b = intersectionNumber b a := by
  unfold intersectionNumber
  congr 1
  ext n
  constructor
  · rintro ⟨γ, δ, hγ, hδ, rfl⟩
    exact ⟨δ, γ, hδ, hγ, SimpleClosedCurve.meetCount_comm δ γ⟩
  · rintro ⟨γ, δ, hγ, hδ, rfl⟩
    exact ⟨δ, γ, hδ, hγ, SimpleClosedCurve.meetCount_comm δ γ⟩

theorem intersectionNumber_map_le (h : X ≃ₜ Y) (a b : CurveClass X) :
    intersectionNumber (map h a) (map h b) ≤ intersectionNumber a b := by
  obtain ⟨γ, δ, rfl, rfl, hγδ⟩ := exists_meetCount_eq_intersectionNumber a b
  rw [← hγδ, map_mk, map_mk, ← SimpleClosedCurve.meetCount_map h γ δ]
  exact intersectionNumber_le_meetCount _ _

/-- The geometric intersection number is invariant under homeomorphisms. -/
@[simp]
theorem intersectionNumber_map (h : X ≃ₜ Y) (a b : CurveClass X) :
    intersectionNumber (map h a) (map h b) = intersectionNumber a b := by
  refine le_antisymm (intersectionNumber_map_le h a b) ?_
  simpa using intersectionNumber_map_le h.symm (map h a) (map h b)

/-- Two classes have intersection number zero exactly when they have disjoint representatives. -/
theorem intersectionNumber_eq_zero_iff {a b : CurveClass X} :
    intersectionNumber a b = 0 ↔
      ∃ γ δ : SimpleClosedCurve X, mk γ = a ∧ mk δ = b ∧ Disjoint γ.carrier δ.carrier := by
  constructor
  · intro h0
    obtain ⟨γ, δ, hγ, hδ, hγδ⟩ := exists_meetCount_eq_intersectionNumber a b
    exact ⟨γ, δ, hγ, hδ, SimpleClosedCurve.meetCount_eq_zero_iff.1 (hγδ.trans h0)⟩
  · rintro ⟨γ, δ, rfl, rfl, hγδ⟩
    exact nonpos_iff_eq_zero.1 ((intersectionNumber_le_meetCount γ δ).trans_eq
      (SimpleClosedCurve.meetCount_eq_zero_iff.2 hγδ))

end CurveClass

end SurfaceCurves
end GroupApproximation
