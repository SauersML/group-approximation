import GroupApproximation.AlgTop.CochainLeibniz
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SingularCohomologyHomotopyInvariance
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Topology.Homotopy.Equiv

/-!
# Integral singular cohomology `Hⁿ(X; R)` and its element-level API

The vendored HamSandwich development already constructs the singular *cochain
complex* functor `singularCochainComplexFunctor R M` and the singular
*cohomology* functor `singularCohomologyFunctor R M n`, generic in a commutative
ring `R` and a coefficient module `M`, together with unconditional homotopy
invariance. What it develops on top of that is specialized to `ZMod 2`.

This file supplies the same element-level API — cohomology classes of cocycles,
chosen representatives, the pullback and its functoriality — for an **arbitrary**
commutative coefficient ring, with `R = ℤ` as the case the counterexample
programme needs. Nothing here is `ZMod 2`-specific.

## Main definitions

* `cochainCx R X` — the singular cochain complex `C^•(X; R)`.
* `cohomology R X n` — `Hⁿ(X; R)`; `cohomologyℤ X n` for `R = ℤ`.
* `IsCocycle R X n φ` — the cocycle condition `δφ = 0` (reducible).
* `cocycleClass R X n φ hφ` — the class of a cocycle.
* `classRepr R X n a` — a chosen cocycle representative of a class.
* `cohPullback R f n` — the pullback `f^* : Hⁿ(Y; R) ⟶ Hⁿ(X; R)`.
* `cohCast R X h` — degree transport along an equality of degrees.

## Main results

* `cocycleClass_surjective` — every class is the class of a cocycle.
* `cocycleClass_coboundary_zero`, `cocycleClass_cast_coboundary_zero` — a
  coboundary is nullhomologous, also after a degree relabelling.
* `cohPullback_cocycleClass` — the pullback of a class is the class of the
  pullback cochain.
* `cohPullback_id`, `cohPullback_comp` — contravariant functoriality.
* `cohPullback_eq_of_homotopy` — homotopy invariance.
-/

open CategoryTheory Limits AlgebraicTopology
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation.AlgTop

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

/-! ## 0. The cochain complex and the cohomology groups -/

/-- The singular cochain complex `C^•(X; R)` with coefficients in the ring `R`
itself, i.e. `Hom(C_•(X), R)`. -/
abbrev cochainCx (R : Type) [CommRing R] (X : TopCat.{0}) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  (singularCochainComplexFunctor R (ModuleCat.of R R)).obj (Opposite.op X)

/-- The `n`-th singular cohomology `Hⁿ(X; R)`, definitionally
`(singularCohomologyFunctor R (ModuleCat.of R R) n).obj (op X)`. -/
abbrev cohomology (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} R :=
  (cochainCx R X).homology n

/-- Integral singular cohomology `Hⁿ(X; ℤ)`. -/
abbrev cohomologyℤ (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} ℤ := cohomology ℤ X n

/-- `cohomology` is the constructed singular cohomology functor's value. -/
theorem cohomology_eq (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    cohomology R X n
      = (singularCohomologyFunctor R (ModuleCat.of R R) n).obj (Opposite.op X) := rfl

/-- A `p`-cochain is a **cocycle** when its coboundary vanishes. -/
abbrev IsCocycle (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup R X n) : Prop :=
  cochainCoboundary R X n φ = 0

/-! ## 1. Linearity of the coboundary -/

@[simp]
theorem cochainCoboundary_zero (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    cochainCoboundary R X n (0 : singularCochainGroup R X n) = 0 := by
  unfold cochainCoboundary
  exact map_zero _

theorem cochainCoboundary_add (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (φ ψ : singularCochainGroup R X n) :
    cochainCoboundary R X n (φ + ψ)
      = cochainCoboundary R X n φ + cochainCoboundary R X n ψ := by
  unfold cochainCoboundary
  exact map_add _ _ _

theorem cochainCoboundary_smul (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (s : R) (φ : singularCochainGroup R X n) :
    cochainCoboundary R X n (s • φ) = s • cochainCoboundary R X n φ := by
  unfold cochainCoboundary
  exact map_smul _ _ _

/-- `δ ∘ δ = 0`. -/
theorem cochainCoboundary_cochainCoboundary (R : Type) [CommRing R] (X : TopCat.{0}) (m : ℕ)
    (η : singularCochainGroup R X m) :
    cochainCoboundary R X (m + 1) (cochainCoboundary R X m η) = 0 := by
  change ((cochainCx R X).d m (m + 1) ≫ (cochainCx R X).d (m + 1) (m + 2)).hom η = 0
  rw [(cochainCx R X).d_comp_d]
  rfl

/-! ## 2. Cohomology classes of cocycles -/

/-- The cohomology class of a cocycle `φ`. -/
def cocycleClass (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup R X n) (hφ : IsCocycle R X n φ) : cohomology R X n :=
  ((cochainCx R X).homologyπ n).hom
    ((cochainCx R X).cyclesMk φ (n + 1) (by simp [ComplexShape.next]) hφ)

/-- The class depends only on the cochain, not on the cocycle proof. -/
theorem cocycleClass_congr (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    {φ φ' : singularCochainGroup R X n} (h : φ = φ')
    (hφ : IsCocycle R X n φ) (hφ' : IsCocycle R X n φ') :
    cocycleClass R X n φ hφ = cocycleClass R X n φ' hφ' := by
  subst h; rfl

/-- The image of a cycle under `iCycles` is a cocycle. -/
theorem cochainCoboundary_iCycles (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (c : (cochainCx R X).cycles n) :
    IsCocycle R X n (((cochainCx R X).iCycles n).hom c) := by
  have h := (cochainCx R X).iCycles_d n (n + 1)
  change ((cochainCx R X).iCycles n ≫ (cochainCx R X).d n (n + 1)).hom c = 0
  rw [h]; rfl

theorem iCycles_cyclesMk (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup R X n) (hφ : IsCocycle R X n φ) :
    ((cochainCx R X).iCycles n).hom
      ((cochainCx R X).cyclesMk φ (n + 1) (by simp [ComplexShape.next]) hφ) = φ :=
  (cochainCx R X).i_cyclesMk _ _ _ _

theorem cyclesMk_iCycles (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (c : (cochainCx R X).cycles n) :
    (cochainCx R X).cyclesMk (((cochainCx R X).iCycles n).hom c) (n + 1)
        (by simp [ComplexShape.next]) (cochainCoboundary_iCycles R X n c) = c := by
  apply (ModuleCat.mono_iff_injective ((cochainCx R X).iCycles n)).1 inferInstance
  exact (cochainCx R X).i_cyclesMk _ _ _ _

/-- **Every cohomology class is the class of a cocycle.** -/
theorem cocycleClass_surjective (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (a : cohomology R X n) :
    ∃ (φ : singularCochainGroup R X n) (hφ : IsCocycle R X n φ),
      cocycleClass R X n φ hφ = a := by
  have hepi : Function.Surjective ((cochainCx R X).homologyπ n).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  obtain ⟨c, hc⟩ := hepi a
  refine ⟨((cochainCx R X).iCycles n).hom c, cochainCoboundary_iCycles R X n c, ?_⟩
  rw [cocycleClass, cyclesMk_iCycles, hc]

/-- The zero cochain has zero class. -/
theorem cocycleClass_zero (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (h0 : IsCocycle R X n (0 : singularCochainGroup R X n)) :
    cocycleClass R X n 0 h0 = 0 := by
  rw [cocycleClass]
  have h : (cochainCx R X).cyclesMk (0 : singularCochainGroup R X n) (n + 1)
      (by simp [ComplexShape.next]) h0 = 0 := by
    apply (ModuleCat.mono_iff_injective ((cochainCx R X).iCycles n)).1 inferInstance
    rw [map_zero]
    exact (cochainCx R X).i_cyclesMk _ _ _ _
  rw [h, map_zero]

/-- `cyclesMk` is additive. -/
theorem cyclesMk_add (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (φ ψ : singularCochainGroup R X n) (hφ : IsCocycle R X n φ) (hψ : IsCocycle R X n ψ)
    (hs : IsCocycle R X n (φ + ψ)) :
    (cochainCx R X).cyclesMk (φ + ψ) (n + 1) (by simp [ComplexShape.next]) hs
      = (cochainCx R X).cyclesMk φ (n + 1) (by simp [ComplexShape.next]) hφ
        + (cochainCx R X).cyclesMk ψ (n + 1) (by simp [ComplexShape.next]) hψ := by
  apply (ModuleCat.mono_iff_injective ((cochainCx R X).iCycles n)).1 inferInstance
  rw [map_add, iCycles_cyclesMk, iCycles_cyclesMk, iCycles_cyclesMk]

/-- `cyclesMk` is `R`-linear. -/
theorem cyclesMk_smul (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) (s : R)
    (φ : singularCochainGroup R X n) (hφ : IsCocycle R X n φ)
    (hs : IsCocycle R X n (s • φ)) :
    (cochainCx R X).cyclesMk (s • φ) (n + 1) (by simp [ComplexShape.next]) hs
      = s • (cochainCx R X).cyclesMk φ (n + 1) (by simp [ComplexShape.next]) hφ := by
  apply (ModuleCat.mono_iff_injective ((cochainCx R X).iCycles n)).1 inferInstance
  show ((cochainCx R X).iCycles n).hom _ = ((cochainCx R X).iCycles n).hom _
  rw [map_smul, iCycles_cyclesMk, iCycles_cyclesMk]

/-- Taking the class of a cocycle is additive. -/
theorem cocycleClass_add (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (φ ψ : singularCochainGroup R X n) (hφ : IsCocycle R X n φ) (hψ : IsCocycle R X n ψ)
    (hs : IsCocycle R X n (φ + ψ)) :
    cocycleClass R X n (φ + ψ) hs
      = cocycleClass R X n φ hφ + cocycleClass R X n ψ hψ := by
  rw [cocycleClass, cocycleClass, cocycleClass, cyclesMk_add R X n φ ψ hφ hψ hs, map_add]

/-- Taking the class of a cocycle is `R`-linear. -/
theorem cocycleClass_smul (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) (s : R)
    (φ : singularCochainGroup R X n) (hφ : IsCocycle R X n φ)
    (hs : IsCocycle R X n (s • φ)) :
    cocycleClass R X n (s • φ) hs = s • cocycleClass R X n φ hφ := by
  rw [cocycleClass, cocycleClass, cyclesMk_smul R X n s φ hφ hs, map_smul]

/-- **A coboundary is nullhomologous.** -/
theorem cocycleClass_coboundary_zero (R : Type) [CommRing R] (X : TopCat.{0}) (m : ℕ)
    (η : singularCochainGroup R X m)
    (hcoc : IsCocycle R X (m + 1) (cochainCoboundary R X m η)) :
    cocycleClass R X (m + 1) (cochainCoboundary R X m η) hcoc = 0 := by
  have h : (cochainCx R X).cyclesMk (cochainCoboundary R X m η) (m + 2)
      (by simp [ComplexShape.next]) hcoc = (cochainCx R X).toCycles m (m + 1) η := by
    apply (ModuleCat.mono_iff_injective ((cochainCx R X).iCycles (m + 1))).1 inferInstance
    change ((forget₂ (ModuleCat R) Ab).map ((cochainCx R X).iCycles (m + 1)))
        ((cochainCx R X).cyclesMk (cochainCoboundary R X m η) (m + 2)
          (by simp [ComplexShape.next]) hcoc) = _
    rw [(cochainCx R X).i_cyclesMk]
    change cochainCoboundary R X m η = _
    exact (ConcreteCategory.congr_hom ((cochainCx R X).toCycles_i m (m + 1)).symm η)
  rw [cocycleClass, h]
  change ((cochainCx R X).toCycles m (m + 1) ≫ (cochainCx R X).homologyπ (m + 1)).hom η = 0
  rw [HomologicalComplex.toCycles_comp_homologyπ]
  rfl

/-! ## 3. Degree transport -/

/-- **Degree transport for cohomology classes.** Every degree-arithmetic mismatch
downstream should be routed through this morphism rather than through rewriting a
`ℕ` inside the dependent type. -/
def cohCast (R : Type) [CommRing R] (X : TopCat.{0}) {m m' : ℕ} (h : m = m') :
    cohomology R X m ⟶ cohomology R X m' :=
  eqToHom (by rw [h])

@[simp]
theorem cohCast_refl (R : Type) [CommRing R] (X : TopCat.{0}) (m : ℕ) :
    cohCast R X (rfl : m = m) = 𝟙 _ := rfl

/-- A degree transport along an equality of a degree with itself is the identity. -/
@[simp]
theorem cohCast_self_apply (R : Type) [CommRing R] (X : TopCat.{0}) {m : ℕ} (h : m = m)
    (a : cohomology R X m) : (cohCast R X h).hom a = a := by
  unfold cohCast
  simp

/-- Degree transports compose. -/
theorem cohCast_comp (R : Type) [CommRing R] (X : TopCat.{0}) {m m' m'' : ℕ}
    (h : m = m') (h' : m' = m'') (a : cohomology R X m) :
    (cohCast R X h').hom ((cohCast R X h).hom a) = (cohCast R X (h.trans h')).hom a := by
  subst h; subst h'
  unfold cohCast
  simp

/-- Compatibility of `cocycleClass` with the cochain degree cast. -/
theorem cocycleClass_cast (R : Type) [CommRing R] (X : TopCat.{0}) {m m' : ℕ} (h : m = m')
    (φ : singularCochainGroup R X m) (hφ : IsCocycle R X m φ)
    (hφ' : IsCocycle R X m' (cochainCast h φ)) :
    cocycleClass R X m' (cochainCast h φ) hφ'
      = (cohCast R X h).hom (cocycleClass R X m φ hφ) := by
  subst h
  rw [cohCast_self_apply]
  exact cocycleClass_congr R X m (cochainCast_self _ φ) hφ' hφ

/-- **A degree-relabelled coboundary is nullhomologous.** -/
theorem cocycleClass_cast_coboundary_zero (R : Type) [CommRing R] (X : TopCat.{0})
    (m m' : ℕ) (h : m + 1 = m') (η : singularCochainGroup R X m)
    (hcoc : IsCocycle R X m' (cochainCast h (cochainCoboundary R X m η))) :
    cocycleClass R X m' (cochainCast h (cochainCoboundary R X m η)) hcoc = 0 := by
  rw [cocycleClass_cast R X h (cochainCoboundary R X m η)
        (cochainCoboundary_cochainCoboundary R X m η) hcoc,
    cocycleClass_coboundary_zero]
  simp

/-- If two cochains are equal and one has zero class, so does the other. -/
theorem cocycleClass_eq_zero_of_eq (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    {φ φ' : singularCochainGroup R X n} (h : φ = φ')
    (hφ : IsCocycle R X n φ) (hφ' : IsCocycle R X n φ')
    (h0 : cocycleClass R X n φ' hφ' = 0) :
    cocycleClass R X n φ hφ = 0 :=
  (cocycleClass_congr R X n h hφ hφ').trans h0

/-! ## 4. Chosen cocycle representatives -/

/-- The chosen cycle representative of a cohomology class. -/
def classCycleRepr (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) (a : cohomology R X n) :
    (cochainCx R X).cycles n :=
  Function.surjInv
    ((ModuleCat.epi_iff_surjective ((cochainCx R X).homologyπ n)).1 inferInstance) a

theorem homologyπ_classCycleRepr (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (a : cohomology R X n) :
    ((cochainCx R X).homologyπ n).hom (classCycleRepr R X n a) = a :=
  Function.surjInv_eq
    ((ModuleCat.epi_iff_surjective ((cochainCx R X).homologyπ n)).1 inferInstance) a

/-- A chosen cocycle representative of a cohomology class. -/
def classRepr (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) (a : cohomology R X n) :
    singularCochainGroup R X n :=
  ((cochainCx R X).iCycles n).hom (classCycleRepr R X n a)

theorem classRepr_isCocycle (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (a : cohomology R X n) : IsCocycle R X n (classRepr R X n a) :=
  cochainCoboundary_iCycles R X n (classCycleRepr R X n a)

theorem cocycleClass_classRepr (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (a : cohomology R X n) :
    cocycleClass R X n (classRepr R X n a) (classRepr_isCocycle R X n a) = a := by
  rw [cocycleClass,
    show (cochainCx R X).cyclesMk (classRepr R X n a) (n + 1) (by simp [ComplexShape.next])
          (classRepr_isCocycle R X n a)
        = classCycleRepr R X n a from cyclesMk_iCycles R X n (classCycleRepr R X n a)]
  exact homologyπ_classCycleRepr R X n a

/-! ## 5. The pullback and its functoriality -/

/-- The **pullback** `f^* : Hⁿ(Y; R) ⟶ Hⁿ(X; R)` of a continuous map `f : X ⟶ Y`,
as the action of the singular cohomology functor. -/
def cohPullback (R : Type) [CommRing R] {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    cohomology R Y n ⟶ cohomology R X n :=
  (singularCohomologyFunctor R (ModuleCat.of R R) n).map f.op

/-- The cochain pullback commutes with the coboundary: it is a cochain map. -/
theorem cochainPullback_cochainCoboundary (R : Type) [CommRing R] {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) (φ : singularCochainGroup R Y n) :
    cochainCoboundary R X n (cochainPullback f n φ)
      = cochainPullback f (n + 1) (cochainCoboundary R Y n φ) := by
  have hcomm := ((singularCochainComplexFunctor R (ModuleCat.of R R)).map f.op).comm n (n + 1)
  change ((cochainCx R X).d n (n + 1)).hom
      ((((singularCochainComplexFunctor R (ModuleCat.of R R)).map f.op).f n).hom φ) = _
  rw [← ModuleCat.comp_apply, hcomm]
  rfl

/-- The cochain pullback of a cocycle is a cocycle. -/
theorem cochainPullback_cocycle (R : Type) [CommRing R] {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (φ : singularCochainGroup R Y n) (hφ : IsCocycle R Y n φ) :
    IsCocycle R X n (cochainPullback f n φ) := by
  have hφ' : cochainCoboundary R Y n φ = 0 := hφ
  show cochainCoboundary R X n (cochainPullback f n φ) = 0
  rw [cochainPullback_cochainCoboundary, hφ']
  show (((singularCochainComplexFunctor R (ModuleCat.of R R)).map f.op).f (n + 1)).hom 0 = 0
  rw [map_zero]

/-- **The pullback of the class of a cocycle is the class of the pullback
cochain.** -/
theorem cohPullback_cocycleClass (R : Type) [CommRing R] {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (φ : singularCochainGroup R Y n) (hφ : IsCocycle R Y n φ) :
    (cohPullback R f n).hom (cocycleClass R Y n φ hφ)
      = cocycleClass R X n (cochainPullback f n φ) (cochainPullback_cocycle R f n φ hφ) := by
  unfold cocycleClass
  rw [show (ModuleCat.Hom.hom (cohPullback R f n))
        = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            ((singularCochainComplexFunctor R (ModuleCat.of R R)).map f.op) n)) from rfl]
  rw [← ModuleCat.comp_apply, HomologicalComplex.homologyπ_naturality, ModuleCat.comp_apply]
  apply congrArg ((cochainCx R X).homologyπ n).hom
  apply (ModuleCat.mono_iff_injective ((cochainCx R X).iCycles n)).1 inferInstance
  calc
    _ = (((cochainCx R Y).iCycles n ≫
          ((singularCochainComplexFunctor R (ModuleCat.of R R)).map f.op).f n).hom)
          ((cochainCx R Y).cyclesMk φ (n + 1) (by simp [ComplexShape.next]) hφ) :=
      ConcreteCategory.congr_hom
        (HomologicalComplex.cyclesMap_i
          ((singularCochainComplexFunctor R (ModuleCat.of R R)).map f.op) n) _
    _ = cochainPullback f n φ := by
      rw [ModuleCat.comp_apply, iCycles_cyclesMk]
      rfl
    _ = _ := (iCycles_cyclesMk R X n _ _).symm

/-- Contravariant functoriality: the identity pulls back to the identity. -/
@[simp]
theorem cohPullback_id (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    cohPullback R (𝟙 X) n = 𝟙 _ := by
  unfold cohPullback
  rw [op_id]
  exact (singularCohomologyFunctor R (ModuleCat.of R R) n).map_id _

/-- Contravariant functoriality: a composite pulls back in the opposite order. -/
theorem cohPullback_comp (R : Type) [CommRing R] {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) :
    cohPullback R (f ≫ g) n = cohPullback R g n ≫ cohPullback R f n := by
  unfold cohPullback
  rw [op_comp]
  exact (singularCohomologyFunctor R (ModuleCat.of R R) n).map_comp _ _

/-- Equal maps have equal pullbacks. -/
theorem cohPullback_congr (R : Type) [CommRing R] {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (h : f = g) (n : ℕ) : cohPullback R f n = cohPullback R g n := by rw [h]

/-- **Homotopy invariance.** Homotopic maps induce the same pullback. -/
theorem cohPullback_eq_of_homotopy (R : Type) [CommRing R] {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) (n : ℕ) :
    cohPullback R f n = cohPullback R g n :=
  singularCohomologyMap_eq_of_homotopy R (ModuleCat.of R R) n H

/-- **Homotopy invariance (`Homotopic` form).** -/
theorem cohPullback_eq_of_homotopic (R : Type) [CommRing R] {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (h : ContinuousMap.Homotopic f.hom g.hom) (n : ℕ) :
    cohPullback R f n = cohPullback R g n :=
  singularCohomologyMap_eq_of_homotopic R (ModuleCat.of R R) n h

/-- A homotopy equivalence induces an isomorphism on cohomology in every degree. -/
def cohIsoOfHomotopyEquiv (R : Type) [CommRing R] {X Y : TopCat.{0}}
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    cohomology R Y n ≅ cohomology R X n where
  hom := cohPullback R (TopCat.ofHom e.toFun) n
  inv := cohPullback R (TopCat.ofHom e.invFun) n
  hom_inv_id := by
    rw [← cohPullback_comp]
    rw [cohPullback_congr R (show TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun
      = TopCat.ofHom (e.toFun.comp e.invFun) from rfl) n]
    rw [show cohPullback R (TopCat.ofHom (e.toFun.comp e.invFun)) n
        = cohPullback R (TopCat.ofHom (ContinuousMap.id Y)) n from
      cohPullback_eq_of_homotopic R e.right_inv n]
    exact cohPullback_id R Y n
  inv_hom_id := by
    rw [← cohPullback_comp]
    rw [cohPullback_congr R (show TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun
      = TopCat.ofHom (e.invFun.comp e.toFun) from rfl) n]
    rw [show cohPullback R (TopCat.ofHom (e.invFun.comp e.toFun)) n
        = cohPullback R (TopCat.ofHom (ContinuousMap.id X)) n from
      cohPullback_eq_of_homotopic R e.left_inv n]
    exact cohPullback_id R X n

end

end GroupApproximation.AlgTop
