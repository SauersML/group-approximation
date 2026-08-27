import GroupApproximation.Algebra.NoncommutativeFinitePresentation
import GroupApproximation.Leavitt.UniversalLeavittOver
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.CharP.Algebra

/-!
# The finite presentation of the binary Leavitt algebra

This file packages the defining presentation of `L_k(1,2)` as four
noncommuting generators and exactly five equations.  In particular it gives
the noncommutative finite-presentation certificate needed by the
Krstić--McCool finite-presentation theorem for Steinberg groups.
-/

namespace GroupApproximation
namespace BinaryLeavitt

variable (k : Type*) [Field k]

/-- The graph of the five-equation relation defining the binary Leavitt
algebra is a finite set of pairs of free-algebra elements. -/
theorem relationPairs_finite :
    Set.Finite {p : Free k × Free k | Relation k p.1 p.2} := by
  classical
  let q00 : Free k × Free k :=
    (FreeAlgebra.ι k t0 * FreeAlgebra.ι k s0, 1)
  let q01 : Free k × Free k :=
    (FreeAlgebra.ι k t0 * FreeAlgebra.ι k s1, 0)
  let q10 : Free k × Free k :=
    (FreeAlgebra.ι k t1 * FreeAlgebra.ι k s0, 0)
  let q11 : Free k × Free k :=
    (FreeAlgebra.ι k t1 * FreeAlgebra.ι k s1, 1)
  let qsum : Free k × Free k :=
    (FreeAlgebra.ι k s0 * FreeAlgebra.ι k t0 +
      FreeAlgebra.ι k s1 * FreeAlgebra.ι k t1, 1)
  let equations : Finset (Free k × Free k) :=
    {q00, q01, q10, q11, qsum}
  apply equations.finite_toSet.subset
  rintro ⟨x, y⟩ h
  change Relation k x y at h
  cases h <;> simp [equations, q00, q01, q10, q11, qsum]

/-- `L_k(1,2)` is finitely presented as a noncommutative `k`-algebra: it
has the four named generators and the five Leavitt equations. -/
instance : Algebra.IsFinitelyPresentedNC k (BinaryLeavittAlgebra k) where
  out := ⟨4, Relation k, relationPairs_finite k, ⟨AlgEquiv.refl⟩⟩

end BinaryLeavitt

namespace BinaryLeavittAbsolute

/-!
## The absolute six-relation presentation over `ℤ`

The relative presentation over `𝔽₂` is not by itself the ring-theoretic
finite-presentation hypothesis in the Krstić--McCool theorem.  We therefore
adjoin the single scalar equation `2 = 0` and identify the resulting
absolute quotient with the actual binary Leavitt algebra over `𝔽₂`.
-/

/-- The free associative ring on the four Leavitt generators. -/
abbrev Free := FreeAlgebra ℤ BinaryLeavitt.Generator

/-- The characteristic-two relation and the five binary Leavitt
relations, now stated over the initial coefficient ring `ℤ`. -/
inductive Relation : Free → Free → Prop
  | charTwo : Relation (1 + 1) 0
  | t0_s0 : Relation
      (FreeAlgebra.ι ℤ BinaryLeavitt.t0 *
        FreeAlgebra.ι ℤ BinaryLeavitt.s0) 1
  | t0_s1 : Relation
      (FreeAlgebra.ι ℤ BinaryLeavitt.t0 *
        FreeAlgebra.ι ℤ BinaryLeavitt.s1) 0
  | t1_s0 : Relation
      (FreeAlgebra.ι ℤ BinaryLeavitt.t1 *
        FreeAlgebra.ι ℤ BinaryLeavitt.s0) 0
  | t1_s1 : Relation
      (FreeAlgebra.ι ℤ BinaryLeavitt.t1 *
        FreeAlgebra.ι ℤ BinaryLeavitt.s1) 1
  | sum_range : Relation
      (FreeAlgebra.ι ℤ BinaryLeavitt.s0 *
          FreeAlgebra.ι ℤ BinaryLeavitt.t0 +
        FreeAlgebra.ι ℤ BinaryLeavitt.s1 *
          FreeAlgebra.ι ℤ BinaryLeavitt.t1) 1

/-- The absolute presented ring. -/
abbrev Presentation := RingQuot Relation

noncomputable local instance :
    CharP (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) 2 :=
  charP_of_injective_algebraMap
    (RingHom.injective
      (algebraMap (ZMod 2)
        (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))) 2

/-- The graph of the absolute relation consists of exactly six pairs. -/
theorem relationPairs_finite :
    Set.Finite {p : Free × Free | Relation p.1 p.2} := by
  classical
  let qchar : Free × Free := (1 + 1, 0)
  let q00 : Free × Free :=
    (FreeAlgebra.ι ℤ BinaryLeavitt.t0 *
      FreeAlgebra.ι ℤ BinaryLeavitt.s0, 1)
  let q01 : Free × Free :=
    (FreeAlgebra.ι ℤ BinaryLeavitt.t0 *
      FreeAlgebra.ι ℤ BinaryLeavitt.s1, 0)
  let q10 : Free × Free :=
    (FreeAlgebra.ι ℤ BinaryLeavitt.t1 *
      FreeAlgebra.ι ℤ BinaryLeavitt.s0, 0)
  let q11 : Free × Free :=
    (FreeAlgebra.ι ℤ BinaryLeavitt.t1 *
      FreeAlgebra.ι ℤ BinaryLeavitt.s1, 1)
  let qsum : Free × Free :=
    (FreeAlgebra.ι ℤ BinaryLeavitt.s0 *
        FreeAlgebra.ι ℤ BinaryLeavitt.t0 +
      FreeAlgebra.ι ℤ BinaryLeavitt.s1 *
        FreeAlgebra.ι ℤ BinaryLeavitt.t1, 1)
  let equations : Finset (Free × Free) :=
    {qchar, q00, q01, q10, q11, qsum}
  apply equations.finite_toSet.subset
  rintro ⟨x, y⟩ h
  change Relation x y at h
  cases h <;>
    simp [equations, qchar, q00, q01, q10, q11, qsum]

/-- Evaluation of the four absolute generators in the actual binary
Leavitt algebra over `𝔽₂`. -/
noncomputable def evaluation :
    Free →ₐ[ℤ] BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2) :=
  FreeAlgebra.lift ℤ ![
    (BinaryLeavitt.family (ZMod 2)).s0,
    (BinaryLeavitt.family (ZMod 2)).s1,
    (BinaryLeavitt.family (ZMod 2)).t0,
    (BinaryLeavitt.family (ZMod 2)).t1]

private theorem evaluation_respects :
    ∀ {x y : Free}, Relation x y → evaluation x = evaluation y := by
  intro x y h
  cases h with
  | charTwo =>
      rw [map_add, map_one, map_zero, one_add_one_eq_two]
      exact CharP.cast_eq_zero
        (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) 2
  | t0_s0 =>
      simp only [evaluation, map_mul, map_one,
        FreeAlgebra.lift_ι_apply]
      exact (BinaryLeavitt.family (ZMod 2)).t0_s0
  | t0_s1 =>
      simp only [evaluation, map_mul, map_zero,
        FreeAlgebra.lift_ι_apply]
      exact (BinaryLeavitt.family (ZMod 2)).t0_s1
  | t1_s0 =>
      simp only [evaluation, map_mul, map_zero,
        FreeAlgebra.lift_ι_apply]
      exact (BinaryLeavitt.family (ZMod 2)).t1_s0
  | t1_s1 =>
      simp only [evaluation, map_mul, map_one,
        FreeAlgebra.lift_ι_apply]
      exact (BinaryLeavitt.family (ZMod 2)).t1_s1
  | sum_range =>
      simp only [evaluation, map_add, map_mul, map_one,
        FreeAlgebra.lift_ι_apply]
      exact (BinaryLeavitt.family (ZMod 2)).sum_range

/-- The absolute quotient maps to the actual characteristic-two Leavitt
algebra. -/
noncomputable def toBinaryLeavitt :
    Presentation →ₐ[ℤ] BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2) :=
  RingQuot.liftAlgHom ℤ
    ⟨evaluation, fun {_ _} h ↦ evaluation_respects h⟩

noncomputable instance : Nontrivial Presentation := by
  refine ⟨0, 1, ?_⟩
  intro h
  have hm := congrArg toBinaryLeavitt h
  rw [map_zero, map_one] at hm
  exact zero_ne_one hm

noncomputable instance : CharP Presentation 2 := by
  apply (CharP.charP_iff_prime_eq_zero (by decide : Nat.Prime 2)).2
  calc
    (2 : Presentation) = 1 + 1 := one_add_one_eq_two.symm
    _ = RingQuot.mkRingHom Relation (1 + 1 : Free) := by
      simp only [map_add, map_one]
    _ = RingQuot.mkRingHom Relation (0 : Free) :=
      RingQuot.mkRingHom_rel Relation.charTwo
    _ = 0 := by simp only [map_zero]

noncomputable local instance : Algebra (ZMod 2) Presentation :=
  ZMod.algebra Presentation 2

/-- The image of a named generator in the absolute quotient. -/
def generator (g : BinaryLeavitt.Generator) : Presentation :=
  RingQuot.mkAlgHom ℤ Relation (FreeAlgebra.ι ℤ g)

/-- The six absolute relations give a binary Leavitt family in the
absolute quotient. -/
def family : LeavittFamily Presentation where
  s0 := generator BinaryLeavitt.s0
  s1 := generator BinaryLeavitt.s1
  t0 := generator BinaryLeavitt.t0
  t1 := generator BinaryLeavitt.t1
  t0_s0 := by
    simpa [generator] using RingQuot.mkAlgHom_rel ℤ Relation.t0_s0
  t0_s1 := by
    simpa [generator] using RingQuot.mkAlgHom_rel ℤ Relation.t0_s1
  t1_s0 := by
    simpa [generator] using RingQuot.mkAlgHom_rel ℤ Relation.t1_s0
  t1_s1 := by
    simpa [generator] using RingQuot.mkAlgHom_rel ℤ Relation.t1_s1
  sum_range := by
    simpa [generator] using RingQuot.mkAlgHom_rel ℤ Relation.sum_range

/-- Universality of `L_{𝔽₂}(1,2)` gives the inverse map from the relative
presentation to the absolute one. -/
noncomputable def fromBinaryLeavitt :
    BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2) →ₐ[ZMod 2] Presentation :=
  BinaryLeavitt.lift family

/-- The absolute evaluation, regarded as an `𝔽₂`-algebra map. -/
noncomputable def toBinaryLeavittZMod :
    Presentation →ₐ[ZMod 2]
      BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2) where
  toRingHom := toBinaryLeavitt.toRingHom
  commutes' z := by
    fin_cases z
    · change toBinaryLeavitt 0 = 0
      exact map_zero toBinaryLeavitt
    · change toBinaryLeavitt 1 = 1
      exact map_one toBinaryLeavitt

@[simp] theorem toBinaryLeavittZMod_apply (x : Presentation) :
    toBinaryLeavittZMod x = toBinaryLeavitt x := rfl

@[simp] theorem toBinaryLeavitt_generator
    (g : BinaryLeavitt.Generator) :
    toBinaryLeavitt (generator g) = BinaryLeavitt.generator (ZMod 2) g := by
  rw [generator, toBinaryLeavitt,
    RingQuot.liftAlgHom_mkAlgHom_apply]
  rw [evaluation, FreeAlgebra.lift_ι_apply]
  fin_cases g <;> rfl

@[simp] theorem fromBinaryLeavitt_generator
    (g : BinaryLeavitt.Generator) :
    fromBinaryLeavitt (BinaryLeavitt.generator (ZMod 2) g) = generator g := by
  fin_cases g <;>
    simp [fromBinaryLeavitt, family, generator, BinaryLeavitt.s0,
      BinaryLeavitt.s1, BinaryLeavitt.t0, BinaryLeavitt.t1]

theorem to_from :
    toBinaryLeavittZMod.comp fromBinaryLeavitt =
      AlgHom.id (ZMod 2) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext g
  change toBinaryLeavitt
      (fromBinaryLeavitt (BinaryLeavitt.generator (ZMod 2) g)) =
    BinaryLeavitt.generator (ZMod 2) g
  rw [fromBinaryLeavitt_generator, toBinaryLeavitt_generator]

/-- The inverse map, restricted to scalars from `ℤ`. -/
noncomputable def fromBinaryLeavittInt :
    BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2) →ₐ[ℤ] Presentation where
  toRingHom := fromBinaryLeavitt.toRingHom
  commutes' z := by simp

@[simp] theorem fromBinaryLeavittInt_apply
    (x : BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) :
    fromBinaryLeavittInt x = fromBinaryLeavitt x := rfl

theorem from_to :
    fromBinaryLeavittInt.comp toBinaryLeavitt = AlgHom.id ℤ Presentation := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext g
  change fromBinaryLeavitt (toBinaryLeavitt (generator g)) = generator g
  rw [toBinaryLeavitt_generator, fromBinaryLeavitt_generator]

/-- The characteristic-two Leavitt algebra is exactly the associative ring
on four generators with the six displayed relations. -/
noncomputable def ringEquiv :
    BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2) ≃+* Presentation :=
  RingEquiv.ofRingHom fromBinaryLeavitt.toRingHom toBinaryLeavitt.toRingHom
    (by exact congrArg AlgHom.toRingHom from_to)
    (by exact congrArg AlgHom.toRingHom to_from)

/-- `L_{𝔽₂}(1,2)` is finitely presented as an associative unital ring,
not merely as an algebra relative to `𝔽₂`. -/
instance : Ring.IsFinitelyPresentedNC
    (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) where
  out := ⟨4, Relation, relationPairs_finite, ⟨ringEquiv⟩⟩

end BinaryLeavittAbsolute
end GroupApproximation
