import GroupApproximation.Higman.OmegaTowerLowStableProjection

/-!
# Retractions of the low-row/free-code projection

The quotient target is a free group on a disjoint alphabet.  Its two evident
retractions recover the low row word and the complete rank-three code word.
On a window block the row retraction loses nothing.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq

/-- Forget the code factor and restore a low row index as an integer row
letter. -/
def lowStableRowRetraction (m : ℕ) :
    LowStableFree m →* FreeGroup ℤ :=
  FreeGroup.lift (Sum.elim
    (fun i : LowIndex m => FreeGroup.of (i : ℤ))
    (fun _ : Fin 3 => 1))

/-- Forget the row factor and restore the complete rank-three code. -/
def lowStableCodeRetraction (m : ℕ) :
    LowStableFree m →* F₃ :=
  FreeGroup.lift (Sum.elim
    (fun _ : LowIndex m => 1)
    (fun i : Fin 3 => FreeGroup.of i))

@[simp] theorem lowStableRowRetraction_of_low
    (m : ℕ) (i : LowIndex m) :
    lowStableRowRetraction m (FreeGroup.of (Sum.inl i)) =
      FreeGroup.of (i : ℤ) := by
  simp [lowStableRowRetraction]

@[simp] theorem lowStableRowRetraction_of_code
    (m : ℕ) (i : Fin 3) :
    lowStableRowRetraction m (FreeGroup.of (Sum.inr i)) = 1 := by
  simp [lowStableRowRetraction]

@[simp] theorem lowStableCodeRetraction_of_low
    (m : ℕ) (i : LowIndex m) :
    lowStableCodeRetraction m (FreeGroup.of (Sum.inl i)) = 1 := by
  simp [lowStableCodeRetraction]

@[simp] theorem lowStableCodeRetraction_of_code
    (m : ℕ) (i : Fin 3) :
    lowStableCodeRetraction m (FreeGroup.of (Sum.inr i)) =
      FreeGroup.of i := by
  simp [lowStableCodeRetraction]

/-- The row retraction after the combined projection is exactly deletion of
all indices at or beyond the cutoff. -/
theorem lowStableRowRetraction_comp_lowRowProjection (m : ℕ) :
    (lowStableRowRetraction m).comp (lowRowProjection m) =
      Split.killOn (fun i : ℤ => i < (m : ℤ)) := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  by_cases hi : i < (m : ℤ)
  · simp [lowRowProjection, Split.killOn_of, hi]
  · simp [lowRowProjection, Split.killOn_of, hi]

/-- The code inclusion is split by the code retraction. -/
theorem lowStableCodeRetraction_comp_stableFreeHom (m : ℕ) :
    (lowStableCodeRetraction m).comp (stableFreeHom m) =
      MonoidHom.id F₃ := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  simp [stableFreeHom]

/-- A block word uses only indices retained by the low-row projection. -/
theorem elt_mem_lowIndexSub {m : ℕ} {beta : E}
    (hbeta : beta ∈ blockSet m) :
    elt beta ∈ RowDeletionGraph.indexSub (fun i : ℤ => i < (m : ℤ)) := by
  unfold RowDeletionGraph.indexSub
  apply Split.elt_mem_closure
  intro i hi
  have hibeta : beta i ≠ 0 := Finsupp.mem_support_iff.mp hi
  by_contra him
  exact hibeta (hbeta i (fun hiWindow => him (Finset.mem_Ico.mp hiWindow).2))

/-- No row information is lost on a legal window block. -/
theorem lowStableRowRetraction_lowRowProjection_elt
    {m : ℕ} {beta : E} (hbeta : beta ∈ blockSet m) :
    lowStableRowRetraction m (lowRowProjection m (elt beta)) = elt beta := by
  rw [← MonoidHom.comp_apply, lowStableRowRetraction_comp_lowRowProjection]
  exact RowDeletionGraph.killOn_eq_self_of_mem_indexSub _
    (elt_mem_lowIndexSub hbeta)

/-- The low-row projection separates legal window blocks. -/
theorem lowRowProjection_elt_injective_on_blockSet (m : ℕ) :
    Set.InjOn (fun beta : E => lowRowProjection m (elt beta)) (blockSet m) := by
  intro beta hbeta gamma hgamma hEq
  apply elt_injective
  change lowRowProjection m (elt beta) =
    lowRowProjection m (elt gamma) at hEq
  calc
    elt beta = lowStableRowRetraction m
        (lowRowProjection m (elt beta)) :=
      (lowStableRowRetraction_lowRowProjection_elt hbeta).symm
    _ = lowStableRowRetraction m
        (lowRowProjection m (elt gamma)) := congrArg _ hEq
    _ = elt gamma := lowStableRowRetraction_lowRowProjection_elt hgamma

end Omega
end Higman
end GroupApproximation
