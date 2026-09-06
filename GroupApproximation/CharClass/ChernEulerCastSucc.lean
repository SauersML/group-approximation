import GroupApproximation.CharClass.ChernEulerEmbed
import GroupApproximation.CharClass.ProjectiveSpacePerm
import GroupApproximation.CharClass.BundleOneStep

/-!
# The first-block coordinate inclusion fixes the degree-two generator

Comparing two line bundles carried at different index sizes pushes both into a
common larger index, and the injection that lands in the *right* index type by
construction is `Fin.castSucc`, the first-block inclusion: `Fin.castSucc` maps
`Fin (d+1) → Fin (d+1+1)`, whereas `iterMat 1 d` would land in `Fin (1+d+1)` and
`1 + d` does not reduce for a variable `d`.

`ProjectiveSpaceStable` computed the generator for the *shift*, the last-block
inclusion, so the two have to be compared.  `cc-bundle` supplied the comparison at
the matrix level in `coordIncl_finRotate_mul_castSucc`: the two differ by
`finRotate`, a permutation, and that is the whole content.  So the topological
half is not a computation but the argument that has worked all day: a unitary
conjugation is a homeomorphism of `ℂP^d`, pullback along it is bijective, and
`H^2(ℂP^d; F₂)` is a line, so the generator has nowhere else to go.

`ProjectiveSpacePerm` already ran that argument for a *permutation of coordinates*,
written as a submatrix.  `coordIncl` of a bijection is the same map, but proving
that entrywise means summing over the permutation, so the unitary form is proved
directly here instead: it needs only the two products, and `cc-bundle` has both
for `finRotate` already.

## Main declarations

* `cpEmbed_conjTranspose_comp`, `cpEmbed_comp_conjTranspose` — a unitary
  conjugation of `ℂP^d` is invertible, with inverse the adjoint conjugation.
* `unitaryCP`, `unitaryIso` — so it is a homeomorphism.
* `pull_cpEmbed_unitary_cpGen` — and it fixes the degree-two generator.
* `pull_cpEmbed_castSucc_cpGen` — **so does the first-block inclusion**, which is
  what comparing bundles across index sizes needs.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace CPn

open CategoryTheory
open scoped Matrix
open GroupApproximation.STW59
open GroupApproximation.CharClass.Bundle

noncomputable section

/-! ## 1. `cpEmbed` respects an equality of matrices -/

/-- Transport `cpEmbed` along an equality of the underlying matrices.  The
isometry proofs are irrelevant, so this is `subst` and `rfl`; it exists because a
dependent `congr` on `cpEmbed` is fragile. -/
theorem cpEmbed_congr {d N : ℕ} {A B : Matrix (Fin (N + 1)) (Fin (d + 1)) ℂ}
    (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1) (h : A = B) : cpEmbed A hA = cpEmbed B hB := by
  subst h
  rfl

/-! ## 2. A unitary conjugation is a homeomorphism -/

section Unitary

variable {d : ℕ} {A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}

/-- The adjoint of a square isometry is an isometry. -/
theorem conjTranspose_isometry (hA' : A * Aᴴ = 1) : (Aᴴ)ᴴ * Aᴴ = 1 := by
  rw [Matrix.conjTranspose_conjTranspose]
  exact hA'

/-- Conjugating by `Aᴴ` undoes conjugating by `A`. -/
theorem cpEmbed_conjTranspose_comp (hA : Aᴴ * A = 1) (hA' : A * Aᴴ = 1) :
    (cpEmbed Aᴴ (conjTranspose_isometry hA')).comp (cpEmbed A hA)
      = ContinuousMap.id (CP d) := by
  refine ContinuousMap.ext fun z => Subtype.ext ?_
  show Aᴴ * (A * (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * Aᴴ) * (Aᴴ)ᴴ
      = (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
  rw [Matrix.conjTranspose_conjTranspose]
  calc Aᴴ * (A * (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * Aᴴ) * A
      = Aᴴ * A * (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * (Aᴴ * A) := by
        simp only [Matrix.mul_assoc]
    _ = (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := by
        rw [hA, Matrix.one_mul, Matrix.mul_one]

/-- And conversely. -/
theorem cpEmbed_comp_conjTranspose (hA : Aᴴ * A = 1) (hA' : A * Aᴴ = 1) :
    (cpEmbed A hA).comp (cpEmbed Aᴴ (conjTranspose_isometry hA'))
      = ContinuousMap.id (CP d) := by
  refine ContinuousMap.ext fun z => Subtype.ext ?_
  show A * (Aᴴ * (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * (Aᴴ)ᴴ) * Aᴴ
      = (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
  rw [Matrix.conjTranspose_conjTranspose]
  calc A * (Aᴴ * (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * A) * Aᴴ
      = A * Aᴴ * (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * (A * Aᴴ) := by
        simp only [Matrix.mul_assoc]
    _ = (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := by
        rw [hA', Matrix.one_mul, Matrix.mul_one]

/-- **A unitary conjugation is a homeomorphism of `ℂP^d`.** -/
def unitaryCP (hA : Aᴴ * A = 1) (hA' : A * Aᴴ = 1) : CP d ≃ₜ CP d where
  toFun := cpEmbed A hA
  invFun := cpEmbed Aᴴ (conjTranspose_isometry hA')
  left_inv z := DFunLike.congr_fun (cpEmbed_conjTranspose_comp hA hA') z
  right_inv z := DFunLike.congr_fun (cpEmbed_comp_conjTranspose hA hA') z
  continuous_toFun := (cpEmbed A hA).continuous
  continuous_invFun := (cpEmbed Aᴴ (conjTranspose_isometry hA')).continuous

/-- The same, as an isomorphism of spaces. -/
def unitaryIso (hA : Aᴴ * A = 1) (hA' : A * Aᴴ = 1) : CPtop d ≅ CPtop d :=
  TopCat.isoOfHomeo (unitaryCP hA hA')

theorem unitaryIso_hom (hA : Aᴴ * A = 1) (hA' : A * Aᴴ = 1) :
    (unitaryIso hA hA').hom = cmap (cpEmbed A hA) := rfl

/-- **A unitary conjugation fixes the degree-two generator.**  It is a
homeomorphism, so pullback along it is bijective, and the degree-two group is a
line, so the generator has nowhere else to go. -/
theorem pull_cpEmbed_unitary_cpGen (hd : 1 ≤ d) (hA : Aᴴ * A = 1) (hA' : A * Aᴴ = 1) :
    pull (cmap (cpEmbed A hA)) 2 (cpGen d hd) = cpGen d hd := by
  refine eq_cpGen_of_ne_zero hd ?_
  intro hzero
  refine cpGen_ne_zero d hd ?_
  refine (LH.bijective_pull_iso (unitaryIso hA hA') 2).1 ?_
  rw [unitaryIso_hom, hzero, pull_zero]

end Unitary

/-! ## 3. The first-block inclusion -/

/-- **The first-block coordinate inclusion fixes the degree-two generator.**

The last-block inclusion is `ProjectiveSpaceStable.pull_cpIncl_cpGen`, and
`cc-bundle`'s `coordIncl_finRotate_mul_castSucc` says the two differ by the
rotation `finRotate`, which is unitary.  So this follows from §2 and costs no new
geometry.  It is the form that comparing bundles across index sizes needs,
because `Fin.castSucc` lands in `Fin (d+1+1)` on the nose. -/
theorem pull_cpEmbed_castSucc_cpGen (d : ℕ) (hd : 1 ≤ d)
    (hcs : (coordIncl (Fin.castSucc : Fin (d + 1) → Fin (d + 1 + 1)))ᴴ
        * coordIncl (Fin.castSucc : Fin (d + 1) → Fin (d + 1 + 1)) = 1) :
    pull (cmap (cpEmbed (coordIncl (Fin.castSucc : Fin (d + 1) → Fin (d + 1 + 1))) hcs)) 2
        (cpGen (d + 1) (by omega))
      = cpGen d hd := by
  have hd1 : 1 ≤ d + 1 := by omega
  have hrot := coordIncl_finRotate_isometry d
  have hrot' := coordIncl_finRotate_mul_conjTranspose d
  have hcomp : (cpEmbed (coordIncl (⇑(finRotate (d + 1 + 1)))) hrot).comp
        (cpEmbed (coordIncl (Fin.castSucc : Fin (d + 1) → Fin (d + 1 + 1))) hcs)
      = cpEmbed (shiftMat d) (shiftMat_isometry d) :=
    (cpEmbed_comp hcs hrot).trans
      (cpEmbed_congr _ _ (coordIncl_finRotate_mul_castSucc d))
  have hcat : cmap (cpEmbed (coordIncl (Fin.castSucc : Fin (d + 1) → Fin (d + 1 + 1))) hcs)
        ≫ cmap (cpEmbed (coordIncl (⇑(finRotate (d + 1 + 1)))) hrot)
      = cpIncl d := by
    rw [cpIncl_eq_cmap, ← cpEmbed_shiftMat, ← hcomp]
    rfl
  have key : pull (cpIncl d) 2 (cpGen (d + 1) hd1)
      = pull (cmap (cpEmbed (coordIncl (Fin.castSucc : Fin (d + 1) → Fin (d + 1 + 1))) hcs)) 2
          (cpGen (d + 1) hd1) := by
    rw [← hcat, pull_comp, pull_cpEmbed_unitary_cpGen hd1 hrot hrot']
  rw [← key]
  exact pull_cpIncl_cpGen d hd

end

end CPn
end CharClass
end GroupApproximation
