import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.BootstrapClosureData
import GroupApproximation.KTheory.Suspension
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Analysis.Real.Sqrt

/-!
# Mapping cones and the cone extension

The two-out-of-three property of the Rosenberg--Schochet class for semisplit extensions
(Rosenberg--Schochet, Duke Math. J. 55 (1987), §4; Blackadar, *K-Theory for Operator Algebras*,
19.5.7 and 22.3.5) is proved by rotating a semisplit extension `0 → I → A → B → 0` into the
**cone extension** of its quotient map. This file builds the concrete C⋆-algebraic objects
needed for that. They form part of the UCT input of `thm:fixed-radical-membership` in
`non_mf_group_notes.tex`.

* `coneSubalgebra f ⊆ X × C([0,1], Y)`: the mapping cone
  `C_f = {(x, g) | g 0 = f x, g 1 = 0}` of `f : X →⋆ₙₐ[ℂ] Y`, a closed star subalgebra;
* `coneIncl f : S Y → C_f` and `coneQuot f : C_f → X`, which form the extension
  `0 → S Y → C_f → X → 0`, where `S Y = Suspension Y` is the loop suspension of
  `GroupApproximation.KTheory`;
* `coneSec f x = (x, t ↦ (1 - t) • f x)`: a completely positive contractive linear section. It is
  completely positive because `star (s x) * s y = coneSec f (star x * y)` for
  `s x = (x, t ↦ √(1 - t) • f x)` (see `isCompletelyPositive_of_star_mul`);
* `coneExtension f : SemisplitExtension (suspI Y) (mappingCone f) X`;
* `excisionMap E : I → C_{E.quot}`, `i ↦ (E.incl i, 0)`. This is the comparison map that the
  excision theorem of `KK`-theory (Blackadar 19.5.5) makes invertible.
-/

namespace GroupApproximation.Full.TWWUCT.Bootstrap

open GroupApproximation.KTheory
open TopologicalSpace

noncomputable section

section Separable

variable (Z : Type*) [NonUnitalCStarAlgebra Z]

/-- The loop suspension of a separable C⋆-algebra is separable. -/
instance instSeparableSpaceSuspension [SeparableSpace Z] : SeparableSpace (Suspension Z) :=
  (IsSeparable.of_separableSpace (suspension Z : Set C(unitInterval, Z))).separableSpace

end Separable

section Cone

variable {X Y Z : Type*} [NonUnitalCStarAlgebra X] [NonUnitalCStarAlgebra Y]
  [NonUnitalCStarAlgebra Z]

/-- **The mapping cone** `C_f = {(x, g) ∈ X × C([0,1], Y) | g 0 = f x, g 1 = 0}`. -/
def coneSubalgebra (f : X →⋆ₙₐ[ℂ] Y) :
    NonUnitalStarSubalgebra ℂ (X × C(unitInterval, Y)) where
  carrier := {p | p.2 0 = f p.1 ∧ p.2 1 = 0}
  add_mem' := fun {p q} (hp : p.2 0 = f p.1 ∧ p.2 1 = 0) (hq : q.2 0 = f q.1 ∧ q.2 1 = 0) =>
    show p.2 0 + q.2 0 = f (p.1 + q.1) ∧ p.2 1 + q.2 1 = 0 from
      ⟨by rw [map_add, hp.1, hq.1], by rw [hp.2, hq.2, add_zero]⟩
  zero_mem' := ⟨(map_zero f).symm, rfl⟩
  mul_mem' := fun {p q} (hp : p.2 0 = f p.1 ∧ p.2 1 = 0) (hq : q.2 0 = f q.1 ∧ q.2 1 = 0) =>
    show p.2 0 * q.2 0 = f (p.1 * q.1) ∧ p.2 1 * q.2 1 = 0 from
      ⟨by rw [map_mul, hp.1, hq.1], by rw [hp.2, zero_mul]⟩
  smul_mem' := fun c {p} (hp : p.2 0 = f p.1 ∧ p.2 1 = 0) =>
    show c • p.2 0 = f (c • p.1) ∧ c • p.2 1 = 0 from
      ⟨by rw [map_smul, hp.1], by rw [hp.2, smul_zero]⟩
  star_mem' := fun {p} (hp : p.2 0 = f p.1 ∧ p.2 1 = 0) =>
    show star (p.2 0) = f (star p.1) ∧ star (p.2 1) = 0 from
      ⟨by rw [map_star, hp.1], by rw [hp.2, star_zero]⟩

theorem mem_coneSubalgebra (f : X →⋆ₙₐ[ℂ] Y) {p : X × C(unitInterval, Y)} :
    p ∈ coneSubalgebra f ↔ p.2 0 = f p.1 ∧ p.2 1 = 0 :=
  Iff.rfl

instance isClosed_coneSubalgebra (f : X →⋆ₙₐ[ℂ] Y) :
    IsClosed (coneSubalgebra f : Set (X × C(unitInterval, Y))) := by
  have h0 : Continuous fun p : X × C(unitInterval, Y) => p.2 0 :=
    (continuous_eval_const (0 : unitInterval)).comp continuous_snd
  have h1 : Continuous fun p : X × C(unitInterval, Y) => p.2 1 :=
    (continuous_eval_const (1 : unitInterval)).comp continuous_snd
  have hf : Continuous fun p : X × C(unitInterval, Y) => f p.1 :=
    (continuous_nonUnitalStarAlgHom f).comp continuous_fst
  exact (isClosed_eq h0 hf).inter (isClosed_eq h1 continuous_const)

instance instNonUnitalCStarAlgebraConeSubalgebra (f : X →⋆ₙₐ[ℂ] Y) :
    NonUnitalCStarAlgebra (coneSubalgebra f) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra (coneSubalgebra f)

instance instSeparableSpaceConeSubalgebra [SeparableSpace X] [SeparableSpace Y]
    (f : X →⋆ₙₐ[ℂ] Y) : SeparableSpace (coneSubalgebra f) :=
  (IsSeparable.of_separableSpace
    (coneSubalgebra f : Set (X × C(unitInterval, Y)))).separableSpace

/-- The path `t ↦ h t • y` for a real scalar function `h` on `[0,1]`. -/
def scalarPath (h : C(unitInterval, ℝ)) (y : Y) : C(unitInterval, Y) :=
  ⟨fun t => ((h t : ℝ) : ℂ) • y,
    (Complex.continuous_ofReal.comp h.continuous).smul continuous_const⟩

theorem scalarPath_apply (h : C(unitInterval, ℝ)) (y : Y) (t : unitInterval) :
    scalarPath h y t = ((h t : ℝ) : ℂ) • y :=
  rfl

/-- The ramp `t ↦ 1 - t`. -/
def rampFn : C(unitInterval, ℝ) :=
  ⟨fun t => 1 - (t : ℝ), continuous_const.sub continuous_subtype_val⟩

/-- The square-root ramp `t ↦ √(1 - t)`. -/
def sqrtRampFn : C(unitInterval, ℝ) :=
  ⟨fun t => Real.sqrt (1 - (t : ℝ)),
    Real.continuous_sqrt.comp (continuous_const.sub continuous_subtype_val)⟩

theorem rampFn_zero : rampFn 0 = 1 :=
  show (1 : ℝ) - 0 = 1 from sub_zero 1

theorem rampFn_one : rampFn 1 = 0 :=
  show (1 : ℝ) - 1 = 0 from sub_self 1

theorem sqrtRampFn_zero : sqrtRampFn 0 = 1 :=
  show Real.sqrt (1 - 0) = 1 by rw [sub_zero, Real.sqrt_one]

theorem sqrtRampFn_one : sqrtRampFn 1 = 0 :=
  show Real.sqrt (1 - 1) = 0 by rw [sub_self, Real.sqrt_zero]

theorem rampFn_nonneg (t : unitInterval) : 0 ≤ rampFn t :=
  show (0 : ℝ) ≤ 1 - (t : ℝ) from sub_nonneg.2 (unitInterval.le_one t)

theorem rampFn_le_one (t : unitInterval) : rampFn t ≤ 1 :=
  show (1 : ℝ) - (t : ℝ) ≤ 1 by linarith [unitInterval.nonneg t]

theorem sqrtRampFn_mul_self (t : unitInterval) : sqrtRampFn t * sqrtRampFn t = rampFn t :=
  show Real.sqrt (1 - (t : ℝ)) * Real.sqrt (1 - (t : ℝ)) = 1 - (t : ℝ) from
    Real.mul_self_sqrt (sub_nonneg.2 (unitInterval.le_one t))

/-- The cone element `(x, t ↦ h t • f x)` for a scalar function with `h 0 = 1` and `h 1 = 0`. -/
def coneElt (f : X →⋆ₙₐ[ℂ] Y) (h : C(unitInterval, ℝ)) (h0 : h 0 = 1) (h1 : h 1 = 0)
    (x : X) : coneSubalgebra f :=
  ⟨(x, scalarPath h (f x)), (mem_coneSubalgebra f).2
    ⟨(show ((h 0 : ℝ) : ℂ) • f x = f x by rw [h0, Complex.ofReal_one, one_smul]),
     (show ((h 1 : ℝ) : ℂ) • f x = 0 by rw [h1, Complex.ofReal_zero, zero_smul])⟩⟩

/-- The inclusion `S Y → C_f`, `g ↦ (0, g)`. -/
def coneIncl (f : X →⋆ₙₐ[ℂ] Y) : Suspension Y →⋆ₙₐ[ℂ] coneSubalgebra f where
  toFun g := ⟨((0 : X), (g : C(unitInterval, Y))), (mem_coneSubalgebra f).2
    ⟨(Suspension.apply_zero g).trans (map_zero f).symm, Suspension.apply_one g⟩⟩
  map_smul' c _ :=
    Subtype.ext (Prod.ext (show (0 : X) = c • (0 : X) from (smul_zero c).symm) rfl)
  map_zero' := Subtype.ext (Prod.ext rfl rfl)
  map_add' _ _ := Subtype.ext (Prod.ext (show (0 : X) = 0 + 0 from (add_zero 0).symm) rfl)
  map_mul' _ _ := Subtype.ext (Prod.ext (show (0 : X) = 0 * 0 from (mul_zero 0).symm) rfl)
  map_star' _ := Subtype.ext (Prod.ext (show (0 : X) = star 0 from star_zero.symm) rfl)

/-- The quotient map `C_f → X`, `(x, g) ↦ x`. -/
def coneQuot (f : X →⋆ₙₐ[ℂ] Y) : coneSubalgebra f →⋆ₙₐ[ℂ] X where
  toFun p := (p : X × C(unitInterval, Y)).1
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

/-- The linear section `X → C_f`, `x ↦ (x, t ↦ (1 - t) • f x)`. -/
def coneSec (f : X →⋆ₙₐ[ℂ] Y) : X →ₗ[ℂ] coneSubalgebra f where
  toFun := coneElt f rampFn rampFn_zero rampFn_one
  map_add' x y := Subtype.ext (Prod.ext rfl (ContinuousMap.ext fun t => by
    show ((rampFn t : ℝ) : ℂ) • f (x + y) =
      ((rampFn t : ℝ) : ℂ) • f x + ((rampFn t : ℝ) : ℂ) • f y
    rw [map_add, smul_add]))
  map_smul' c x := Subtype.ext (Prod.ext rfl (ContinuousMap.ext fun t => by
    show ((rampFn t : ℝ) : ℂ) • f (c • x) = c • (((rampFn t : ℝ) : ℂ) • f x)
    rw [map_smul]
    exact smul_comm _ _ _))

/-- The square-root cone element `(x, t ↦ √(1 - t) • f x)`. -/
def coneSqrtElt (f : X →⋆ₙₐ[ℂ] Y) (x : X) : coneSubalgebra f :=
  coneElt f sqrtRampFn sqrtRampFn_zero sqrtRampFn_one x

theorem coneSqrtElt_star_mul (f : X →⋆ₙₐ[ℂ] Y) (x y : X) :
    star (coneSqrtElt f x) * coneSqrtElt f y = coneSec f (star x * y) := by
  refine Subtype.ext (Prod.ext rfl (ContinuousMap.ext fun t => ?_))
  show star (((sqrtRampFn t : ℝ) : ℂ) • f x) * (((sqrtRampFn t : ℝ) : ℂ) • f y) =
    ((rampFn t : ℝ) : ℂ) • f (star x * y)
  have hc : star ((sqrtRampFn t : ℝ) : ℂ) = ((sqrtRampFn t : ℝ) : ℂ) :=
    Complex.conj_ofReal _
  rw [map_mul, map_star, star_smul, hc, smul_mul_assoc, mul_smul_comm, smul_smul,
    ← Complex.ofReal_mul, sqrtRampFn_mul_self]

/-- **Complete positivity from a star-square factorization.** Suppose some map `s` satisfies
`star (s x) * s y = φ (star x * y)`. Then `φ` is completely positive: `φ` applied entrywise to
`star N * N` is `star (s N) * (s N)`. -/
theorem isCompletelyPositive_of_star_mul (φ : X →ₗ[ℂ] Z) (s : X → Z)
    (hs : ∀ x y : X, star (s x) * s y = φ (star x * y)) :
    CStarExactness.IsCompletelyPositive φ := by
  intro n M hM
  obtain ⟨N, rfl⟩ := hM
  refine ⟨N.map s, ?_⟩
  ext i j
  show φ (∑ k, star (N k i) * N k j) = ∑ k, star (s (N k i)) * s (N k j)
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => (hs (N k i) (N k j)).symm

theorem isCompletelyPositive_coneSec (f : X →⋆ₙₐ[ℂ] Y) :
    CStarExactness.IsCompletelyPositive (coneSec f) :=
  isCompletelyPositive_of_star_mul (coneSec f) (coneSqrtElt f) (coneSqrtElt_star_mul f)

theorem norm_coneSec_le (f : X →⋆ₙₐ[ℂ] Y) (x : X) : ‖coneSec f x‖ ≤ ‖x‖ := by
  show max ‖x‖ ‖scalarPath rampFn (f x)‖ ≤ ‖x‖
  refine max_le le_rfl ((ContinuousMap.norm_le _ (norm_nonneg x)).2 fun t => ?_)
  show ‖((rampFn t : ℝ) : ℂ) • f x‖ ≤ ‖x‖
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (rampFn_nonneg t)]
  calc rampFn t * ‖f x‖ ≤ 1 * ‖x‖ :=
        mul_le_mul (rampFn_le_one t) (NonUnitalStarAlgHom.norm_apply_le f x) (norm_nonneg _)
          zero_le_one
    _ = ‖x‖ := one_mul _

theorem coneIncl_injective (f : X →⋆ₙₐ[ℂ] Y) : Function.Injective (coneIncl f) :=
  fun _ _ hgg' =>
    Subtype.ext (congrArg (fun p : coneSubalgebra f => (p : X × C(unitInterval, Y)).2) hgg')

theorem coneQuot_eq_zero_iff (f : X →⋆ₙₐ[ℂ] Y) (a : coneSubalgebra f) :
    coneQuot f a = 0 ↔ ∃ g : Suspension Y, coneIncl f g = a := by
  constructor
  · intro h
    have h1 : (a : X × C(unitInterval, Y)).1 = 0 := h
    have ha := (mem_coneSubalgebra f).1 a.property
    refine ⟨⟨(a : X × C(unitInterval, Y)).2, (mem_suspension Y).2
      ⟨by rw [ha.1, h1, map_zero], ha.2⟩⟩, Subtype.ext (Prod.ext h1.symm rfl)⟩
  · rintro ⟨g, rfl⟩
    rfl

theorem coneQuot_coneSec (f : X →⋆ₙₐ[ℂ] Y) (x : X) : coneQuot f (coneSec f x) = x :=
  rfl

/-- The comparison map `Z → C_f`, `z ↦ (ι z, 0)`, for `ι : Z → X` with `f ∘ ι = 0`. -/
def excisionMap' (ι : Z →⋆ₙₐ[ℂ] X) (f : X →⋆ₙₐ[ℂ] Y)
    (h : ∀ z, f (ι z) = 0) : Z →⋆ₙₐ[ℂ] coneSubalgebra f where
  toFun z := ⟨(ι z, 0), (mem_coneSubalgebra f).2 ⟨(h z).symm, rfl⟩⟩
  map_smul' c z := Subtype.ext (Prod.ext (map_smul ι c z)
    (show (0 : C(unitInterval, Y)) = c • (0 : C(unitInterval, Y)) from (smul_zero c).symm))
  map_zero' := Subtype.ext (Prod.ext (map_zero ι) rfl)
  map_add' z z' := Subtype.ext (Prod.ext (map_add ι z z')
    (show (0 : C(unitInterval, Y)) = 0 + 0 from (add_zero 0).symm))
  map_mul' z z' := Subtype.ext (Prod.ext (map_mul ι z z')
    (show (0 : C(unitInterval, Y)) = 0 * 0 from (mul_zero 0).symm))
  map_star' z := Subtype.ext (Prod.ext (map_star ι z)
    (show (0 : C(unitInterval, Y)) = star 0 from star_zero.symm))

end Cone

/-! ### The bundled objects -/

/-- **The loop suspension** `S B = {g ∈ C([0,1], B) | g 0 = g 1 = 0}` as a bundled algebra. -/
abbrev SepNUCStarAlgebra.suspI (B : SepNUCStarAlgebra) : SepNUCStarAlgebra where
  carrier := Suspension B

/-- **The mapping cone** of a star homomorphism, bundled. -/
abbrev SepNUCStarAlgebra.mappingCone {A B : SepNUCStarAlgebra} (f : A →⋆ₙₐ[ℂ] B) :
    SepNUCStarAlgebra where
  carrier := coneSubalgebra f

/-- **The cone extension** `0 → S B → C_f → A → 0` of `f : A → B`. It is semisplit, with section
`coneSec f`. -/
def coneExtension {A B : SepNUCStarAlgebra} (f : A →⋆ₙₐ[ℂ] B) :
    SemisplitExtension B.suspI (SepNUCStarAlgebra.mappingCone f) A where
  incl := coneIncl f
  quot := coneQuot f
  incl_injective := coneIncl_injective f
  quot_surjective x := ⟨coneSec f x, rfl⟩
  exact := coneQuot_eq_zero_iff f
  sec := coneSec f
  sec_completelyPositive := isCompletelyPositive_coneSec f
  sec_contractive := norm_coneSec_le f
  quot_sec := coneQuot_coneSec f

/-- **The excision map** `I → C_{E.quot}` of a semisplit extension, `i ↦ (E.incl i, 0)`
(Blackadar 19.5.5: its `KK`-class is invertible). -/
def excisionMap {I A B : SepNUCStarAlgebra} (E : SemisplitExtension I A B) :
    I →⋆ₙₐ[ℂ] SepNUCStarAlgebra.mappingCone E.quot :=
  excisionMap' E.incl E.quot fun z => (E.exact (E.incl z)).2 ⟨z, rfl⟩

end

end GroupApproximation.Full.TWWUCT.Bootstrap
