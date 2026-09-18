import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionExt
import GroupApproximation.Analysis.CStarCompactSelfModule
import GroupApproximation.Analysis.CStarUnitary

/-!
# The extension class `extClass X ∈ Ext(S, J)`

Lane `TWWSchafhauser-3d2`, work order `WO-TWWSchafhauser-3d-2(a)`. Source: C. Schafhauser,
*A new proof of the Tikuisis–White–Winter theorem*, J. reine angew. Math. 759 (2020), §4.

An extension `0 → J → E → S → 0` is recorded as a `CStarExtension S J`: a unital C⋆-algebra `E`,
an isometric `⋆`-homomorphism `incl : J → E` and a surjective unital `⋆`-homomorphism
`quot : E → S` with `ker quot = range incl`.

Its Busby map `S → M(J)/J ⊆ Q(J ⊗ 𝒦)` is built from a set-theoretic lift `σ : S → E` of `quot`.
An element `e ∈ E` multiplies the ideal `J`, which gives a multiplier `multOp e ∈ M(J)`. That
multiplier is placed in the `(0,0)` corner of `𝓛(H_J)` by the isometry
`coordZero : J → H_J, b ↦ (b, 0, 0, …)`:

`cornerOp e = V ∘ multOp e ∘ V⋆`.

The operator `cornerOp` is additive, linear, multiplicative and `⋆`-preserving *exactly*. The Busby
axioms hold modulo compacts because `cornerOp (incl j) = V ∘ ofElem j ∘ V⋆` is compact
(`isCompactOp_ofElem`), and `σ` is a homomorphism modulo `incl J`.

* `CStarExtension`, `CStarExtension.Lift`;
* `CStarExtension.cornerOp` with `cornerOp_add/_sub/_smul/_mul/_star`, `isBoundedBy_cornerOp`,
  `isCompactOp_cornerOp_incl`, `compactEq_cornerOp`;
* `CStarExtension.busbyCycleOfLift`, `CStarExtension.busbyCycle`, `extClass`;
* `extClass_eq_mk_busbyCycleOfLift`: the class does not depend on the lift.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule

noncomputable section

section CoordVec

variable {J : Type} [NonUnitalCStarAlgebra J]

/-- The sequence `(b, 0, 0, …)`. -/
def coordVec (b : J) : ℕ → J := fun i => if i = 0 then b else 0

theorem coordVec_zero (b : J) : coordVec b 0 = b := if_pos rfl

theorem coordVec_of_ne (b : J) {i : ℕ} (h : i ≠ 0) : coordVec b i = 0 := if_neg h

theorem summable_coordVec (b : J) : Summable fun i => star (coordVec b i) * coordVec b i :=
  summable_of_ne_finset_zero (s := {0}) fun i hi => by
    show star (coordVec b i) * coordVec b i = 0
    rw [coordVec_of_ne b (Finset.notMem_singleton.mp hi), star_zero, zero_mul]

end CoordVec

section CoordZero

variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

variable (J) in
/-- The isometry `V : J → H_J`, `b ↦ (b, 0, 0, …)`. Its adjoint reads off coordinate `0`. -/
def coordZero : Adjointable (selfModule J) (standardModule ℕ J) where
  toFun b := ⟨coordVec b, summable_coordVec b⟩
  adj f := f.1 0
  inner_adj b f := by
    show (∑' i, star (coordVec b i) * f.1 i) = star b * f.1 0
    rw [tsum_eq_single 0, coordVec_zero]
    intro i hi
    rw [coordVec_of_ne b hi, star_zero, zero_mul]

/-- `V⋆V = 1`. -/
theorem coordZero_adj_toFun (b : J) : (coordZero J).adj ((coordZero J).toFun b) = b :=
  coordVec_zero b

variable (J) in
/-- `V` is an isometry, and in particular bounded by `1`. -/
theorem isBoundedBy_coordZero : (coordZero J).IsBoundedBy 1 := by
  intro b
  have h : (standardModule ℕ J).inner ((coordZero J).toFun b) ((coordZero J).toFun b) =
      star b * b :=
    ((coordZero J).inner_adj b _).trans (congrArg (star b * ·) (coordZero_adj_toFun b))
  exact le_of_eq ((congrArg (fun z : J => Real.sqrt ‖z‖) h).trans (one_mul _).symm)

end CoordZero

/-- **A C⋆-extension** `0 → J → E → S → 0`: `incl` is isometric, `quot` is surjective, and
`ker quot = range incl`. -/
structure CStarExtension (S : Type) [CStarAlgebra S] (J : Type) [NonUnitalCStarAlgebra J] :
    Type 1 where
  /-- The middle algebra. -/
  E : Type
  [instE : CStarAlgebra E]
  /-- The ideal inclusion. -/
  incl : J →⋆ₙₐ[ℂ] E
  /-- The quotient map. -/
  quot : E →⋆ₐ[ℂ] S
  norm_incl : ∀ j : J, ‖incl j‖ = ‖j‖
  quot_surjective : Function.Surjective quot
  /-- Exactness in the middle. -/
  quot_eq_zero_iff : ∀ e : E, quot e = 0 ↔ ∃ j : J, incl j = e

attribute [instance] CStarExtension.instE

namespace CStarExtension

section Mult

variable {S : Type} [CStarAlgebra S] {J : Type} [NonUnitalCStarAlgebra J]
variable (X : CStarExtension S J)

theorem incl_injective : Function.Injective X.incl := by
  intro j j' h
  have h0 : ‖j - j'‖ = 0 := by rw [← X.norm_incl, map_sub, h, sub_self, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

theorem quot_incl (j : J) : X.quot (X.incl j) = 0 := (X.quot_eq_zero_iff _).mpr ⟨j, rfl⟩

/-- `J` is a left ideal in `E`. -/
theorem exists_incl_eq_mul (e : X.E) (j : J) : ∃ j' : J, X.incl j' = e * X.incl j :=
  (X.quot_eq_zero_iff _).mp (by rw [map_mul X.quot, X.quot_incl, mul_zero])

/-- Left multiplication by `e ∈ E` on the ideal `J`. -/
def leftMul (e : X.E) (j : J) : J := Classical.choose (X.exists_incl_eq_mul e j)

theorem incl_leftMul (e : X.E) (j : J) : X.incl (X.leftMul e j) = e * X.incl j :=
  Classical.choose_spec (X.exists_incl_eq_mul e j)

theorem leftMul_eq_iff {e : X.E} {j j' : J} :
    X.leftMul e j = j' ↔ e * X.incl j = X.incl j' := by
  constructor
  · rintro rfl
    exact (X.incl_leftMul e j).symm
  · intro h
    exact X.incl_injective ((X.incl_leftMul e j).trans h)

theorem leftMul_incl (j x : J) : X.leftMul (X.incl j) x = j * x :=
  X.leftMul_eq_iff.mpr (map_mul X.incl j x).symm

theorem leftMul_add_left (e e' : X.E) (j : J) :
    X.leftMul (e + e') j = X.leftMul e j + X.leftMul e' j :=
  X.leftMul_eq_iff.mpr (by rw [map_add X.incl, X.incl_leftMul, X.incl_leftMul, add_mul])

theorem leftMul_sub_left (e e' : X.E) (j : J) :
    X.leftMul (e - e') j = X.leftMul e j - X.leftMul e' j :=
  X.leftMul_eq_iff.mpr (by rw [map_sub X.incl, X.incl_leftMul, X.incl_leftMul, sub_mul])

theorem leftMul_smul_left (c : ℂ) (e : X.E) (j : J) :
    X.leftMul (c • e) j = c • X.leftMul e j :=
  X.leftMul_eq_iff.mpr (by rw [map_smul X.incl, X.incl_leftMul, smul_mul_assoc])

theorem leftMul_mul (e e' : X.E) (j : J) :
    X.leftMul (e * e') j = X.leftMul e (X.leftMul e' j) :=
  X.leftMul_eq_iff.mpr (by rw [X.incl_leftMul, X.incl_leftMul, mul_assoc])

/-- The multiplier of `J` given by `e ∈ E`, with adjoint `star e`. -/
def multOp (e : X.E) : Multiplier J where
  toFun := X.leftMul e
  adj := X.leftMul (star e)
  inner_adj x y := by
    show star (X.leftMul e x) * y = star x * X.leftMul (star e) y
    apply X.incl_injective
    rw [map_mul X.incl, map_star X.incl, X.incl_leftMul, map_mul X.incl, map_star X.incl,
      X.incl_leftMul, star_mul, mul_assoc]

theorem isBoundedBy_multOp (e : X.E) : (X.multOp e).IsBoundedBy ‖e‖ := by
  intro x
  show (selfModule J).norm (X.leftMul e x) ≤ ‖e‖ * (selfModule J).norm x
  rw [selfModule_norm, selfModule_norm, ← X.norm_incl (X.leftMul e x), ← X.norm_incl x,
    X.incl_leftMul]
  exact norm_mul_le e (X.incl x)

/-- A set-theoretic lift of `quot`. A ucp splitting (Choi–Effros) is one, but any section
will do. -/
structure Lift where
  /-- The lift. -/
  toFun : S → X.E
  quot_toFun : ∀ a : S, X.quot (toFun a) = a

theorem quot_lift_add (σ : X.Lift) (a a' : S) :
    X.quot (σ.1 (a + a')) = X.quot (σ.1 a + σ.1 a') := by
  rw [map_add X.quot, σ.2 a, σ.2 a', σ.2 (a + a')]

theorem quot_lift_smul (σ : X.Lift) (c : ℂ) (a : S) :
    X.quot (σ.1 (c • a)) = X.quot (c • σ.1 a) := by
  rw [map_smul X.quot, σ.2 a, σ.2 (c • a)]

theorem quot_lift_mul (σ : X.Lift) (a a' : S) :
    X.quot (σ.1 (a * a')) = X.quot (σ.1 a * σ.1 a') := by
  rw [map_mul X.quot, σ.2 a, σ.2 a', σ.2 (a * a')]

theorem quot_lift_star (σ : X.Lift) (a : S) :
    X.quot (σ.1 (star a)) = X.quot (star (σ.1 a)) := by
  rw [map_star X.quot, σ.2 a, σ.2 (star a)]

end Mult

section Corner

variable {S : Type} [CStarAlgebra S]
variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]
variable (X : CStarExtension S J)

/-- **The corner operator** `V ∘ multOp e ∘ V⋆` on `H_J`: `ξ ↦ (e·ξ₀, 0, 0, …)`. -/
def cornerOp (e : X.E) : StdOp J :=
  Adjointable.comp (coordZero J)
    (Adjointable.comp (X.multOp e) (Adjointable.adjoint (coordZero J)))

theorem cornerOp_toFun (e : X.E) (f : (standardModule ℕ J).carrier) :
    (X.cornerOp e).toFun f = (coordZero J).toFun (X.leftMul e ((coordZero J).adj f)) :=
  rfl

theorem cornerOp_add (e e' : X.E) (f : (standardModule ℕ J).carrier) :
    (Adjointable.add (X.cornerOp e) (X.cornerOp e')).toFun f = (X.cornerOp (e + e')).toFun f :=
  ((congrArg (coordZero J).toFun (X.leftMul_add_left e e' ((coordZero J).adj f))).trans
    ((coordZero J).map_add _ _)).symm

theorem cornerOp_sub (e e' : X.E) (f : (standardModule ℕ J).carrier) :
    (Adjointable.sub (X.cornerOp e) (X.cornerOp e')).toFun f = (X.cornerOp (e - e')).toFun f :=
  ((congrArg (coordZero J).toFun (X.leftMul_sub_left e e' ((coordZero J).adj f))).trans
    ((coordZero J).map_sub _ _)).symm

theorem cornerOp_smul (c : ℂ) (e : X.E) (f : (standardModule ℕ J).carrier) :
    (Adjointable.smul c (X.cornerOp e)).toFun f = (X.cornerOp (c • e)).toFun f :=
  ((congrArg (coordZero J).toFun (X.leftMul_smul_left c e ((coordZero J).adj f))).trans
    ((coordZero J).map_smul c _)).symm

theorem cornerOp_mul (e e' : X.E) (f : (standardModule ℕ J).carrier) :
    (Adjointable.comp (X.cornerOp e) (X.cornerOp e')).toFun f = (X.cornerOp (e * e')).toFun f :=
  (congrArg (fun z : J => (coordZero J).toFun (X.leftMul e z))
    (coordZero_adj_toFun (X.leftMul e' ((coordZero J).adj f)))).trans
    (congrArg (coordZero J).toFun (X.leftMul_mul e e' ((coordZero J).adj f)).symm)

theorem cornerOp_star (e : X.E) (f : (standardModule ℕ J).carrier) :
    (Adjointable.adjoint (X.cornerOp e)).toFun f = (X.cornerOp (star e)).toFun f :=
  rfl

theorem isBoundedBy_cornerOp (e : X.E) : (X.cornerOp e).IsBoundedBy ‖e‖ :=
  ((isBoundedBy_coordZero J).comp ((X.isBoundedBy_multOp e).comp
    ((isBoundedBy_coordZero J).adjoint zero_le_one) (norm_nonneg e)) zero_le_one).mono
    (le_of_eq (by ring))

/-- `cornerOp (incl j) = V ∘ ofElem j ∘ V⋆` is compact. -/
theorem isCompactOp_cornerOp_incl (j : J) : (X.cornerOp (X.incl j)).IsCompactOp := by
  have hV : (coordZero J).IsBounded := ⟨1, zero_le_one, isBoundedBy_coordZero J⟩
  have hK := ((Adjointable.isCompactOp_ofElem j).comp_right hV.adjoint).comp_left hV
  refine Adjointable.IsCompactOp.congr (fun f => ?_) hK
  exact congrArg (coordZero J).toFun (X.leftMul_incl j ((coordZero J).adj f)).symm

/-- Operators that agree pointwise with corner operators of elements with the same image in
`S` are equal modulo compacts. -/
theorem compactEq_cornerOp {T T' : StdOp J} (e e' : X.E)
    (hT : ∀ f, T.toFun f = (X.cornerOp e).toFun f)
    (hT' : ∀ f, T'.toFun f = (X.cornerOp e').toFun f) (h : X.quot e = X.quot e') :
    CompactEq J T T' := by
  obtain ⟨j, hj⟩ := (X.quot_eq_zero_iff (e - e')).mp (by rw [map_sub X.quot, h, sub_self])
  show Adjointable.IsCompactOp (Adjointable.sub T T')
  refine Adjointable.IsCompactOp.congr (fun f => ?_) (X.isCompactOp_cornerOp_incl j)
  show (X.cornerOp (X.incl j)).toFun f = T.toFun f - T'.toFun f
  rw [hT, hT', hj]
  exact (X.cornerOp_sub e e' f).symm

/-- **The Busby cycle of a lift** `σ`: `a ↦ cornerOp (σ a)`. -/
def busbyCycleOfLift (σ : X.Lift) : BusbyCycle S J where
  lift a := X.cornerOp (σ.1 a)
  bounded a := (X.isBoundedBy_cornerOp (σ.1 a)).isBounded (norm_nonneg _)
  map_add a a' := X.compactEq_cornerOp (σ.1 (a + a')) (σ.1 a + σ.1 a') (fun _ => rfl)
    (X.cornerOp_add (σ.1 a) (σ.1 a')) (X.quot_lift_add σ a a')
  map_smul c a := X.compactEq_cornerOp (σ.1 (c • a)) (c • σ.1 a) (fun _ => rfl)
    (X.cornerOp_smul c (σ.1 a)) (X.quot_lift_smul σ c a)
  map_mul a a' := X.compactEq_cornerOp (σ.1 (a * a')) (σ.1 a * σ.1 a') (fun _ => rfl)
    (X.cornerOp_mul (σ.1 a) (σ.1 a')) (X.quot_lift_mul σ a a')
  map_star a := X.compactEq_cornerOp (σ.1 (star a)) (star (σ.1 a)) (fun _ => rfl)
    (X.cornerOp_star (σ.1 a)) (X.quot_lift_star σ a)

/-- The Busby cycle of the extension, for the section `Function.surjInv` of `quot`. -/
def busbyCycle : BusbyCycle S J :=
  X.busbyCycleOfLift ⟨Function.surjInv X.quot_surjective, Function.surjInv_eq X.quot_surjective⟩

end Corner

end CStarExtension

section ExtClass

variable {S : Type} [CStarAlgebra S]
variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- **The extension class** `[X] ∈ Ext(S, J) = KK¹(S, J)`. -/
def extClass (X : CStarExtension S J) : ExtGroup S J :=
  ExtGroup.mk X.busbyCycle

/-- The class is computed by any lift. Two lifts differ by `incl J`, so their cycles agree
modulo compacts, i.e. they are unitarily equivalent via `U = 1`. -/
theorem extClass_eq_mk_busbyCycleOfLift (X : CStarExtension S J) (σ : X.Lift) :
    extClass X = ExtGroup.mk (X.busbyCycleOfLift σ) := by
  refine ExtGroup.mk_eq_of_isUnitarilyEquivalent
    ⟨Adjointable.id (standardModule ℕ J), Adjointable.isUnitaryAdj_id _, fun a => ?_⟩
  exact X.compactEq_cornerOp (Function.surjInv X.quot_surjective a) (σ.1 a) (fun _ => rfl)
    (fun _ => rfl) ((Function.surjInv_eq X.quot_surjective a).trans (σ.2 a).symm)

end ExtClass

end

end GroupApproximation.Full.TWWSchafhauser
