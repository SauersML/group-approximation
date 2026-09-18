import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.KTheoryNonUnitalHomotopyZero
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.MatrixCorner
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.Stab

/-!
# Matrix corners and the finite-matrix embedding into the stabilization

This file is part of the proof of stability of non-unital K-theory: `K_*(𝒦 ⊗ J) ≅ K_*(J)`
(Rørdam--Larsen--Laustsen, *An introduction to K-theory for C⋆-algebras*, Prop. 4.3.2, 6.4.1,
Ch. 8 and 10). It sets up the two ⋆-homomorphisms that the argument factors through.

* `matCorner J N : J →⋆ₙₐ[ℂ] M_{N+1}(J)` is the corner `b ↦ e₀₀ ⊗ b`.
* `matEmbed J k : M_k(J) →⋆ₙₐ[ℂ] 𝒦 ⊗ J` embeds `k × k` matrices as finitely
  supported matrices, `M ↦ ∑ᵢⱼ e_{ij} ⊗ M_{ij}`.
* `matEmbed_comp_matCorner`: the corner of `𝒦 ⊗ J` factors as
  `J → M_{N+1}(J) → 𝒦 ⊗ J`.

Manuscript: `non_mf_group_notes.tex`, `thm:fixed-radical-membership`: the K-theory
input of the UCT argument of Tikuisis--White--Winter.
-/

namespace GroupApproximation
namespace Full
namespace TWWSchafhauser

open TWWKK TWWKK.Stab

noncomputable section

variable {J : Type} [NonUnitalCStarAlgebra J]

theorem matOfMatrix_congr {k : ℕ} {M M' : Matrix (Fin k) (Fin k) J} (h : M = M') :
    (CStarMatrix.ofMatrix M : CStarMatrix (Fin k) (Fin k) J) = CStarMatrix.ofMatrix M' := by
  rw [h]

variable (J) in
/-- **The matrix corner** `J → M_{N+1}(J)`, `b ↦ e₀₀ ⊗ b` (RLL Prop. 4.3.2;
`thm:fixed-radical-membership`). -/
def matCorner (N : ℕ) : J →⋆ₙₐ[ℂ] CStarMatrix (Fin (N + 1)) (Fin (N + 1)) J where
  toFun b := CStarMatrix.ofMatrix (Matrix.single 0 0 b)
  map_smul' r b := matOfMatrix_congr (Matrix.smul_single r 0 0 b).symm
  map_zero' := matOfMatrix_congr (Matrix.single_zero 0 0)
  map_add' a b := matOfMatrix_congr (Matrix.single_add 0 0 a b)
  map_mul' a b := matOfMatrix_congr (Matrix.single_mul_single_same a 0 0 0 b).symm
  map_star' b := matOfMatrix_congr (Matrix.conjTranspose_single 0 0 b).symm

theorem matCorner_apply (N : ℕ) (b : J) :
    matCorner J N b = CStarMatrix.ofMatrix (Matrix.single 0 0 b) :=
  rfl

/-! ## The finite-matrix embedding -/

theorem matUnit_sum (i j : ℕ) {ι : Type*} (s : Finset ι)
    (T : ι → RepSpace J →L[ℂ] RepSpace J) :
    matUnit J i j (∑ x ∈ s, T x) = ∑ x ∈ s, matUnit J i j (T x) :=
  let F : (RepSpace J →L[ℂ] RepSpace J) →+ Ambient J :=
    { toFun := matUnit J i j
      map_zero' := matUnit_zero i j
      map_add' := matUnit_add i j }
  map_sum F T s

variable (J) in
/-- The operator `∑ᵢⱼ e_{ij} ⊗ π(M_{ij})` of a `k × k` matrix over `J`. -/
def matEmbedFun (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) J) : Ambient J :=
  ∑ i : Fin k, ∑ j : Fin k, matUnit J i j (rep J (M i j))

variable {k : ℕ}

theorem matEmbedFun_mem (M : CStarMatrix (Fin k) (Fin k) J) :
    matEmbedFun J k M ∈ closedSubalgebra J := by
  unfold matEmbedFun
  exact sum_mem fun i _ => sum_mem fun j _ => matUnit_rep_mem (i : ℕ) (j : ℕ) (M i j)

theorem matUnit_mul_matEmbedFun (i : ℕ) (j : Fin k) (S : RepSpace J →L[ℂ] RepSpace J)
    (N : CStarMatrix (Fin k) (Fin k) J) :
    matUnit J i j S * matEmbedFun J k N = ∑ l : Fin k, matUnit J i l (S * rep J (N j l)) := by
  unfold matEmbedFun
  rw [Finset.mul_sum]
  have h0 : ∀ k' ∈ (Finset.univ : Finset (Fin k)), k' ≠ j →
      matUnit J i j S * ∑ l : Fin k, matUnit J k' l (rep J (N k' l)) = 0 := by
    intro k' _ hk'
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun l _ => matUnit_mul_of_ne (fun h => hk' (Fin.ext h).symm) _ _
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j) h0, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => matUnit_mul_self _ _ _ _ _

theorem matEmbedFun_mul (M N : CStarMatrix (Fin k) (Fin k) J) :
    matEmbedFun J k (M * N) = matEmbedFun J k M * matEmbedFun J k N := by
  have hL : matEmbedFun J k (M * N) =
      ∑ i : Fin k, ∑ l : Fin k, ∑ j : Fin k,
        matUnit J i l (rep J (M i j) * rep J (N j l)) := by
    show ∑ i : Fin k, ∑ l : Fin k, matUnit J i l (rep J ((M * N) i l)) = _
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    show matUnit J i l (rep J (∑ j, M i j * N j l)) = _
    rw [map_sum, matUnit_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul]
  have hR : matEmbedFun J k M * matEmbedFun J k N =
      ∑ i : Fin k, ∑ j : Fin k, ∑ l : Fin k,
        matUnit J i l (rep J (M i j) * rep J (N j l)) := by
    show (∑ i : Fin k, ∑ j : Fin k, matUnit J i j (rep J (M i j))) * matEmbedFun J k N = _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => matUnit_mul_matEmbedFun _ _ _ _
  rw [hL, hR]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem matEmbedFun_star (M : CStarMatrix (Fin k) (Fin k) J) :
    matEmbedFun J k (star M) = star (matEmbedFun J k M) := by
  have hs : star (matEmbedFun J k M) =
      ∑ i : Fin k, ∑ j : Fin k, matUnit J j i (rep J (star (M i j))) := by
    show star (∑ i : Fin k, ∑ j : Fin k, matUnit J i j (rep J (M i j))) = _
    rw [star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [star_sum]
    exact Finset.sum_congr rfl fun j _ => (star_matUnit _ _ (rep J (M i j))).trans
      (congrArg (matUnit J j i) (map_star (rep J) (M i j)).symm)
  rw [hs, Finset.sum_comm]
  show ∑ i : Fin k, ∑ j : Fin k, matUnit J i j (rep J ((star M) i j)) = _
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    congrArg (fun x => matUnit J i j (rep J x)) CStarMatrix.star_apply

theorem matEmbedFun_smul (c : ℂ) (M : CStarMatrix (Fin k) (Fin k) J) :
    matEmbedFun J k (c • M) = c • matEmbedFun J k M := by
  show ∑ i : Fin k, ∑ j : Fin k, matUnit J i j (rep J (c • M i j)) =
    c • ∑ i : Fin k, ∑ j : Fin k, matUnit J i j (rep J (M i j))
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, matUnit_smul]

theorem matEmbedFun_add (M N : CStarMatrix (Fin k) (Fin k) J) :
    matEmbedFun J k (M + N) = matEmbedFun J k M + matEmbedFun J k N := by
  show ∑ i : Fin k, ∑ j : Fin k, matUnit J i j (rep J (M i j + N i j)) =
    ∑ i : Fin k, ∑ j : Fin k, matUnit J i j (rep J (M i j)) +
      ∑ i : Fin k, ∑ j : Fin k, matUnit J i j (rep J (N i j))
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_add, matUnit_add]

theorem matEmbedFun_zero : matEmbedFun J k 0 = 0 := by
  show ∑ i : Fin k, ∑ j : Fin k, matUnit J i j (rep J 0) = 0
  exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
    rw [map_zero, matUnit_zero]

variable (J) in
/-- **The finite-matrix embedding** `M_k(J) → 𝒦 ⊗ J`, `M ↦ ∑ᵢⱼ e_{ij} ⊗ M_{ij}`
(RLL Ch. 6; `thm:fixed-radical-membership`). -/
def matEmbed (k : ℕ) : CStarMatrix (Fin k) (Fin k) J →⋆ₙₐ[ℂ] Stab J where
  toFun M := ⟨matEmbedFun J k M, matEmbedFun_mem M⟩
  map_smul' c M := Subtype.ext (matEmbedFun_smul c M)
  map_zero' := Subtype.ext matEmbedFun_zero
  map_add' M N := Subtype.ext (matEmbedFun_add M N)
  map_mul' M N := Subtype.ext (matEmbedFun_mul M N)
  map_star' M := Subtype.ext (matEmbedFun_star M)

theorem coe_matEmbed (M : CStarMatrix (Fin k) (Fin k) J) :
    (matEmbed J k M : Ambient J) = matEmbedFun J k M :=
  rfl

variable (J) in
/-- **The corner of `𝒦 ⊗ J` factors through `M_{N+1}(J)`**: `e₀₀ ⊗ b` is the image of the
matrix `e₀₀ ⊗ b` (`thm:fixed-radical-membership`). -/
theorem matEmbed_comp_matCorner (N : ℕ) :
    (matEmbed J (N + 1)).comp (matCorner J N) = Stab.corner J := by
  refine NonUnitalStarAlgHom.ext fun b => Subtype.ext ?_
  show ∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
      matUnit J i j (rep J (Matrix.single (0 : Fin (N + 1)) 0 b i j)) =
    matUnit J ((0 : Fin (N + 1)) : ℕ) ((0 : Fin (N + 1)) : ℕ) (rep J b)
  have h0 : ∀ i ∈ (Finset.univ : Finset (Fin (N + 1))), i ≠ 0 →
      ∑ j : Fin (N + 1), matUnit J i j (rep J (Matrix.single (0 : Fin (N + 1)) 0 b i j)) = 0 :=
    fun i _ hi => Finset.sum_eq_zero fun j _ => by
      rw [Matrix.single_apply_of_ne (0 : Fin (N + 1)) 0 b i j (fun h => hi h.1.symm), map_zero,
        matUnit_zero]
  have h1 : ∀ j ∈ (Finset.univ : Finset (Fin (N + 1))), j ≠ 0 →
      matUnit J ((0 : Fin (N + 1)) : ℕ) j
        (rep J (Matrix.single (0 : Fin (N + 1)) 0 b 0 j)) = 0 :=
    fun j _ hj => by
      rw [Matrix.single_apply_of_ne (0 : Fin (N + 1)) 0 b 0 j (fun h => hj h.2.symm), map_zero,
        matUnit_zero]
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_univ _) h0,
    Finset.sum_eq_single_of_mem 0 (Finset.mem_univ _) h1, Matrix.single_apply_same]

theorem matEmbed_matCorner (N : ℕ) (b : J) :
    matEmbed J (N + 1) (matCorner J N b) = Stab.corner J b :=
  DFunLike.congr_fun (matEmbed_comp_matCorner J N) b

end

end TWWSchafhauser
end Full
end GroupApproximation
