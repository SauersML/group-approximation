import GroupApproximation.Analysis.SequentialGroupColimit
import GroupApproximation.Analysis.CStarUnitaryComponent
import GroupApproximation.Analysis.CStarMatrixBlockInclusion

/-!
# Topological `K_1` of a unital C-star algebra

For a unital C-star algebra `A` this file defines

    K_1(A) = colim_n U(M_n(A)) / U_0(M_n(A))

along the block inclusions `u ↦ diag (u, 1)`, the canonical map

    kappa : U(A)/U_0(A) → K_1(A),

and the property `K1Injective A`, which says that `kappa` is injective.

The colimit is the one built in `Analysis/SequentialGroupColimit`; the tower maps are the ones
built in `Analysis/CStarMatrixBlockInclusion`, pushed to the quotients by `unitaryClassMap` (a
continuous group homomorphism carries the identity path component into the identity path
component).

Nothing here computes `K_1` of anything.  What it is for is
`Analysis/CStarKOneInjectivityCriterion`, which shows that a single unitary `u` with
`u ∉ U_0(A)` and `diag (u, 1) ∈ U_0(M_2(A))` already refutes `K1Injective A` — no Bott
periodicity, no Morita invariance, no continuity of `K`-theory.
-/

namespace GroupApproximation

universe u

noncomputable section

section OneByOne

variable (A : Type u) [CStarAlgebra A]

/-- The star monoid homomorphism `A →⋆* M_1(A)` sending `a` to the 1×1 matrix `(a)`.

Mathlib has this as a star algebra equivalence, `CStarMatrix.toOneByOne`; only the monoid and
star structure are needed here, and writing it out keeps the coercion definitional. -/
def toOneByOneHom : A →⋆* CStarMat 1 A where
  toFun a := fun _ _ => a
  map_one' := by
    ext i j
    rw [CStarMatrix.one_apply, if_pos (Subsingleton.elim i j)]
  map_mul' a b := by
    ext i j
    rw [CStarMatrix.mul_apply, Fin.sum_univ_one]
  map_star' a := by
    ext i j
    rw [CStarMatrix.star_apply]

@[simp] theorem toOneByOneHom_apply (a : A) (i j : Fin 1) : toOneByOneHom A a i j = a := rfl

theorem continuous_toOneByOneHom : Continuous (toOneByOneHom A) :=
  continuous_matrix fun _ _ => continuous_id

/-- `U(A) →* U(M_1(A))`, the unitary group of the 1×1 matrix identification. -/
def unitaryOneByOne : unitary A →* unitary (CStarMat 1 A) :=
  (Unitary.map (toOneByOneHom A)).toMonoidHom

@[simp] theorem coe_unitaryOneByOne (v : unitary A) :
    ((unitaryOneByOne A v : unitary (CStarMat 1 A)) : CStarMat 1 A)
      = toOneByOneHom A (v : A) := rfl

theorem continuous_unitaryOneByOne : Continuous (unitaryOneByOne A) :=
  continuous_induced_rng.mpr ((continuous_toOneByOneHom A).comp continuous_subtype_val)

end OneByOne

section Tower

variable (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Level `n` of the `K_1` tower: `U(M_n(A)) / U_0(M_n(A))`. -/
abbrev KOneLevel (n : ℕ) : Type u := UnitaryClass (CStarMat n A)

/-- The transition map of the `K_1` tower, induced by `u ↦ diag (u, 1)`. -/
def kOneMap {n m : ℕ} (h : n ≤ m) : KOneLevel A n →* KOneLevel A m :=
  unitaryClassMap (blockOneUnitary h) (continuous_blockOneUnitary h)

@[simp] theorem kOneMap_mk {n m : ℕ} (h : n ≤ m) (v : unitary (CStarMat n A)) :
    kOneMap A h (QuotientGroup.mk v) = QuotientGroup.mk (blockOneUnitary h v) := rfl

/-- The tower `n ↦ U(M_n(A))/U_0(M_n(A))` with the block inclusions as transition maps. -/
def kOneTower : GroupTower (KOneLevel A) where
  map h := kOneMap A h
  map_self := by
    intro n h x
    refine QuotientGroup.induction_on x fun v => ?_
    show (QuotientGroup.mk (blockOneUnitary h v) : KOneLevel A n) = QuotientGroup.mk v
    rw [blockOneUnitary_self]
  map_trans := by
    intro n m k h₁ h₂ x
    refine QuotientGroup.induction_on x fun v => ?_
    show (QuotientGroup.mk (blockOneUnitary h₂ (blockOneUnitary h₁ v)) : KOneLevel A k)
      = QuotientGroup.mk (blockOneUnitary (h₁.trans h₂) v)
    rw [blockOneUnitary_trans]

/-- Topological `K_1` of a unital C-star algebra: the colimit of the groups
`U(M_n(A))/U_0(M_n(A))` along the block inclusions `u ↦ diag (u, 1)`. -/
abbrev KOne : Type u := (kOneTower A).Colim

/-- The canonical homomorphism from level `n` of the tower into `K_1(A)`. -/
abbrev kOneIota (n : ℕ) : KOneLevel A n →* KOne A := (kOneTower A).iota n

theorem kOneIota_kOneMap {n m : ℕ} (h : n ≤ m) (x : KOneLevel A n) :
    kOneIota A m (kOneMap A h x) = kOneIota A n x :=
  GroupTower.iota_map (kOneTower A) h x

/-- The induced map `U(A)/U_0(A) → U(M_1(A))/U_0(M_1(A))`. -/
def unitaryClassOneByOne : UnitaryClass A →* KOneLevel A 1 :=
  unitaryClassMap (unitaryOneByOne A) (continuous_unitaryOneByOne A)

/-- The canonical map `kappa : U(A)/U_0(A) → K_1(A)`. -/
def kappa : UnitaryClass A →* KOne A := (kOneIota A 1).comp (unitaryClassOneByOne A)

@[simp] theorem kappa_mk (v : unitary A) :
    kappa A (QuotientGroup.mk v) = kOneIota A 1 (QuotientGroup.mk (unitaryOneByOne A v)) := rfl

/-- A unital C-star algebra is `K_1`-injective when the canonical map
`U(A)/U_0(A) → K_1(A)` is injective. -/
def K1Injective : Prop := Function.Injective (kappa A)

theorem k1Injective_def : K1Injective A ↔ Function.Injective (kappa A) := Iff.rfl

end Tower

end

end GroupApproximation
