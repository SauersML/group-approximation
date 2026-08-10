import Mathlib.Data.Finsupp.SMul
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Group.Action.Pretransitive
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Abel

/-!
# Reduced permutation lattices and their semidirect products

For a transitive action `G ↷ X`, the reduced integral permutation module is

`ker (augmentation : (X →₀ ℤ) →+ ℤ)`.

This file develops the algebraic core of the augmentation-quotient construction
used for the Kun--Thom pair.  It is independent of soficity and of the
operator-algebraic input: the augmentation map is invariant, the edge
differences form a cocycle, and a finitely generated transitive action gives a
finitely generated semidirect product.
-/

namespace NonsoficGroupsExist

open scoped Pointwise

noncomputable section

universe u

variable (X : Type u)

/-- The coefficient sum on the integral permutation lattice. -/
def permutationAugmentation : (X →₀ ℤ) →+ ℤ where
  toFun f := f.sum fun _ z ↦ z
  map_zero' := by simp
  map_add' f h := by
    classical
    exact Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)

@[simp] theorem permutationAugmentation_apply (f : X →₀ ℤ) :
    permutationAugmentation X f = f.sum fun _ z ↦ z := rfl

@[simp] theorem permutationAugmentation_single (x : X) (z : ℤ) :
    permutationAugmentation X (Finsupp.single x z) = z := by
  simp [permutationAugmentation]

/-- The reduced integral permutation module. -/
abbrev ReducedPermutationLattice (X : Type u) : Type u :=
  ↑(permutationAugmentation X).ker

variable {X}

/-- The difference of two vertices, regarded as an element of the reduced
permutation lattice. -/
def reducedDifference (x y : X) : ReducedPermutationLattice X :=
  ⟨Finsupp.single x (1 : ℤ) - Finsupp.single y (1 : ℤ), by
    rw [AddMonoidHom.mem_ker, map_sub]
    simp⟩

@[simp] theorem reducedDifference_coe (x y : X) :
    (reducedDifference x y : X →₀ ℤ) =
      Finsupp.single x 1 - Finsupp.single y 1 := rfl

theorem reducedDifference_ne_zero {x y : X} (hxy : x ≠ y) :
    reducedDifference x y ≠ 0 := by
  intro h
  have hx := DFunLike.congr_fun (congrArg Subtype.val h) x
  simp [reducedDifference, hxy] at hx

private theorem finsupp_sum_smul_difference (o : X) (q : X →₀ ℤ) :
    q.sum (fun x z ↦ z •
      (Finsupp.single x (1 : ℤ) - Finsupp.single o (1 : ℤ))) =
      q - Finsupp.single o (q.sum fun _ z ↦ z) := by
  simp_rw [smul_sub]
  rw [show q.sum (fun x z ↦ z • Finsupp.single x (1 : ℤ) -
      z • Finsupp.single o (1 : ℤ)) =
      q.sum (fun x z ↦ z • Finsupp.single x (1 : ℤ)) -
        q.sum (fun _ z ↦ z • Finsupp.single o (1 : ℤ)) by
    simp only [Finsupp.sum, Finset.sum_sub_distrib]]
  rw [show q.sum (fun x z ↦ z • Finsupp.single x (1 : ℤ)) = q by
    simpa only [Finsupp.smul_single_one] using Finsupp.sum_single q]
  congr 1
  simp only [Finsupp.sum, Finsupp.smul_single_one]
  exact (map_sum (Finsupp.singleAddHom o) (fun x ↦ q x) q.support).symm

/-- Every reduced vector is the finite sum of its coefficients times the
based differences. -/
theorem reduced_eq_sum_smul_difference (o : X)
    (f : ReducedPermutationLattice X) :
    f = (f : X →₀ ℤ).sum fun x z ↦ z • reducedDifference x o := by
  have h : (f : X →₀ ℤ) = (f : X →₀ ℤ).sum (fun x z ↦ z •
      (Finsupp.single x (1 : ℤ) - Finsupp.single o (1 : ℤ))) := by
    rw [finsupp_sum_smul_difference]
    rw [show (f : X →₀ ℤ).sum (fun _ z ↦ z) = 0 from f.property]
    simp
  apply Subtype.ext
  simpa [Finsupp.sum, reducedDifference] using h

section Action

variable (G : Type*) [Group G] [MulAction G X]

local instance permutationSMul : SMul G (X →₀ ℤ) := Finsupp.comapSMul
local instance permutationMulAction : MulAction G (X →₀ ℤ) :=
  Finsupp.comapMulAction
local instance permutationDistribMulAction : DistribMulAction G (X →₀ ℤ) :=
  Finsupp.comapDistribMulAction

theorem permutationAugmentation_smul (g : G) (f : X →₀ ℤ) :
    permutationAugmentation X (g • f) = permutationAugmentation X f := by
  classical
  simp only [permutationAugmentation_apply, Finsupp.comapSMul_def]
  exact Finsupp.sum_mapDomain_index (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)

/-- The restricted additive action on the reduced permutation lattice. -/
def reducedPermutationAddEquiv (g : G) :
    ReducedPermutationLattice X ≃+ ReducedPermutationLattice X where
  toFun f := ⟨g • (f : X →₀ ℤ), by
    rw [AddMonoidHom.mem_ker, permutationAugmentation_smul]
    exact f.property⟩
  invFun f := ⟨g⁻¹ • (f : X →₀ ℤ), by
    rw [AddMonoidHom.mem_ker, permutationAugmentation_smul]
    exact f.property⟩
  left_inv f := by ext; simp
  right_inv f := by ext; simp
  map_add' f h := by ext; simp

@[simp] theorem reducedPermutationAddEquiv_coe (g : G)
    (f : ReducedPermutationLattice X) :
    ((reducedPermutationAddEquiv G g f : ReducedPermutationLattice X) : X →₀ ℤ) =
      g • (f : X →₀ ℤ) := rfl

/-- The action on the multiplicative copy used by `SemidirectProduct`. -/
def reducedPermutationAction :
    G →* MulAut (Multiplicative (ReducedPermutationLattice X)) where
  toFun g := (reducedPermutationAddEquiv G g).toMultiplicative
  map_one' := by
    ext f
    simp [reducedPermutationAddEquiv]
  map_mul' g h := by
    ext f
    simp [reducedPermutationAddEquiv, mul_smul]

/-- The reduced permutation extension associated to `G ↷ X`. -/
abbrev ReducedPermutationExtension :=
  Multiplicative (ReducedPermutationLattice X) ⋊[reducedPermutationAction G] G

/-- The based edge difference. -/
def orbitDifference (o : X) (g : G) : ReducedPermutationLattice X :=
  reducedDifference (g • o) o

@[simp] theorem reducedPermutationAddEquiv_difference (g : G) (x y : X) :
    reducedPermutationAddEquiv G g (reducedDifference x y) =
      reducedDifference (g • x) (g • y) := by
  apply Subtype.ext
  change Finsupp.mapDomain (g • ·)
      (Finsupp.single x (1 : ℤ) - Finsupp.single y (1 : ℤ)) =
    Finsupp.single (g • x) 1 - Finsupp.single (g • y) 1
  rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_single,
    Finsupp.mapDomain_single]

@[simp] theorem orbitDifference_one (o : X) : orbitDifference G o 1 = 0 := by
  apply Subtype.ext
  simp [orbitDifference, reducedDifference]

/-- The edge differences form the canonical crossed homomorphism. -/
theorem orbitDifference_mul (o : X) (g h : G) :
    orbitDifference G o (g * h) =
      reducedPermutationAddEquiv G g (orbitDifference G o h) + orbitDifference G o g := by
  change reducedDifference ((g * h) • o) o =
    reducedPermutationAddEquiv G g (reducedDifference (h • o) o) +
      reducedDifference (g • o) o
  rw [reducedPermutationAddEquiv_difference, mul_smul]
  apply Subtype.ext
  change Finsupp.single (g • h • o) 1 - Finsupp.single o 1 =
    (Finsupp.single (g • h • o) 1 - Finsupp.single (g • o) 1) +
      (Finsupp.single (g • o) 1 - Finsupp.single o 1)
  abel

/-- For a transitive action, the canonical orbit differences generate the
entire reduced permutation lattice as an additive group. -/
theorem closure_range_orbitDifference [MulAction.IsPretransitive G X] (o : X) :
    AddSubgroup.closure (Set.range (orbitDifference G o)) = ⊤ := by
  apply top_unique
  intro f _
  rw [reduced_eq_sum_smul_difference o f, Finsupp.sum]
  apply sum_mem
  intro x _
  apply AddSubgroup.zsmul_mem
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G o x
  rw [← hg]
  exact AddSubgroup.subset_closure ⟨g, rfl⟩

end Action

end

end NonsoficGroupsExist
