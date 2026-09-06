import GroupApproximation.CharClass.ProjectiveSpaceIterate
import GroupApproximation.CharClass.LerayHirschTransport

/-!
# Permuting homogeneous coordinates fixes the generator

`ProjectiveSpaceCharts` permutes two coordinates to move one standard chart onto
another.  Comparing two coordinate embeddings of `ℂP^d` into a larger projective
space needs the same for an arbitrary permutation, because two injections of
coordinates differ exactly by a permutation of the target.

Everything is the submatrix construction again, with a transposition replaced by
an arbitrary permutation, so entries stay definitional and no matrix arithmetic
appears.  The consequence for cohomology is immediate rather than computed: a
permutation is a homeomorphism, pullback along it is bijective, and the
degree-two group is a line, so the generator has nowhere to go but itself.

## Main declarations

* `permMat`, `permCP` — permuting coordinates, on matrices and on `ℂP^d`.
* `pull_permCP_cpGen` — **a permutation fixes the degree-two generator**.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace CPn

open CategoryTheory Matrix
open GroupApproximation.STW59

noncomputable section

variable {d : ℕ}

/-- Permute the coordinates of a matrix. -/
def permMat (σ : Equiv.Perm (Fin (d + 1)))
    (q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  q.submatrix σ σ

@[simp] theorem permMat_apply (σ : Equiv.Perm (Fin (d + 1)))
    (q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) (a b : Fin (d + 1)) :
    permMat σ q a b = q (σ a) (σ b) := rfl

theorem permMat_symm_permMat (σ : Equiv.Perm (Fin (d + 1)))
    (q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) : permMat σ.symm (permMat σ q) = q := by
  ext a b
  show q (σ (σ.symm a)) (σ (σ.symm b)) = q a b
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem permMat_permMat_symm (σ : Equiv.Perm (Fin (d + 1)))
    (q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) : permMat σ (permMat σ.symm q) = q := by
  ext a b
  show q (σ.symm (σ a)) (σ.symm (σ b)) = q a b
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem permMat_mem_cpSet (σ : Equiv.Perm (Fin (d + 1)))
    {q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ} (hq : q ∈ cpSet d) :
    permMat σ q ∈ cpSet d := by
  obtain ⟨hH, hI, hT⟩ := hq
  refine ⟨?_, ?_, ?_⟩
  · ext a b
    show star (q (σ b) (σ a)) = q (σ a) (σ b)
    exact congrFun (congrFun hH (σ a)) (σ b)
  · show q.submatrix σ σ * q.submatrix σ σ = q.submatrix σ σ
    rw [Matrix.submatrix_mul_equiv, hI]
  · show (q.submatrix σ σ).trace = 1
    rw [← hT]
    exact Equiv.sum_comp σ (fun b => q b b)

/-- **Permuting homogeneous coordinates is a homeomorphism of `ℂP^d`.** -/
def permCP (σ : Equiv.Perm (Fin (d + 1))) : CP d ≃ₜ CP d where
  toFun z := ⟨permMat σ z, permMat_mem_cpSet σ z.2⟩
  invFun z := ⟨permMat σ.symm z, permMat_mem_cpSet σ.symm z.2⟩
  left_inv _ := Subtype.ext (permMat_symm_permMat σ _)
  right_inv _ := Subtype.ext (permMat_permMat_symm σ _)
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_matrix fun a b => ?_) _
    exact continuous_entry (d := d) (σ a) (σ b)
  continuous_invFun := by
    refine Continuous.subtype_mk (continuous_matrix fun a b => ?_) _
    exact continuous_entry (d := d) (σ.symm a) (σ.symm b)

@[simp] theorem entry_permCP (σ : Equiv.Perm (Fin (d + 1))) (z : CP d) (a b : Fin (d + 1)) :
    entry (permCP σ z) a b = entry z (σ a) (σ b) := rfl

/-- Permuting coordinates, as an isomorphism of spaces. -/
def permIso (σ : Equiv.Perm (Fin (d + 1))) : CPtop d ≅ CPtop d :=
  TopCat.isoOfHomeo (permCP σ)

/-- **A permutation of homogeneous coordinates fixes the degree-two generator.**
It is a homeomorphism, so pullback along it is bijective, and the degree-two group
is a line, so the generator has nowhere else to go. -/
theorem pull_permCP_cpGen (hd : 1 ≤ d) (σ : Equiv.Perm (Fin (d + 1))) :
    pull (permIso σ).hom 2 (cpGen d hd) = cpGen d hd := by
  refine eq_cpGen_of_ne_zero hd ?_
  intro hzero
  refine cpGen_ne_zero d hd ?_
  refine (LH.bijective_pull_iso (permIso σ) 2).1 ?_
  rw [hzero, pull_zero]

end

end CPn
end CharClass
end GroupApproximation
