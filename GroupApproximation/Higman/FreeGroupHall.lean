import GroupApproximation.Sofic.FreeGroupResiduallyFinite
import GroupApproximation.Sofic.ProfiniteClosure

/-!
# Marshall Hall separation for finitely generated free subgroups

The finite action below is the coset-graph proof of Hall's theorem.  For a
finitely generated subgroup `H ≤ FreeGroup α` and `w ∉ H`, retain only the
finitely many right cosets visited while reading chosen generators of `H`
and `w`.  Right multiplication by each free generator is then a partial
bijection of this finite set.  Completing the complements arbitrarily gives
a finite permutation action.  Every chosen generator fixes the base coset,
whereas `w` moves it.

Using actual cosets as vertices means all Stallings folds are already built
into the construction.  No finiteness assumption on the alphabet is needed.
-/

namespace GroupApproximation
namespace FreeGroupHall

open scoped Classical

variable {α : Type*}

abbrev Coset (H : Subgroup (FreeGroup α)) :=
  Quotient (QuotientGroup.rightRel H)

/-- Right multiplication by `g⁻¹` on right cosets.  The inverse is chosen so
that `g ↦ cosetStep g` is a left action, hence a homomorphism to
permutations. -/
noncomputable def cosetStep (H : Subgroup (FreeGroup α))
    (g : FreeGroup α) : Coset H → Coset H :=
  Quotient.map (fun x ↦ x * g⁻¹) (by
    intro x y hxy
    apply QuotientGroup.rightRel_apply.mpr
    have hxy' := QuotientGroup.rightRel_apply.mp hxy
    have heq : (y * g⁻¹) * (x * g⁻¹)⁻¹ = y * x⁻¹ := by group
    rw [heq]
    exact hxy')

@[simp] theorem cosetStep_mk (H : Subgroup (FreeGroup α))
    (g x : FreeGroup α) :
    cosetStep H g (Quotient.mk _ x) = Quotient.mk _ (x * g⁻¹) := rfl

theorem cosetStep_mul (H : Subgroup (FreeGroup α))
    (g h : FreeGroup α) (x : Coset H) :
    cosetStep H (g * h) x = cosetStep H g (cosetStep H h x) := by
  induction x using Quotient.inductionOn with
  | _ x =>
      apply congrArg (Quotient.mk (QuotientGroup.rightRel H))
      group

@[simp] theorem cosetStep_one (H : Subgroup (FreeGroup α))
    (x : Coset H) : cosetStep H 1 x = x := by
  induction x using Quotient.inductionOn with
  | _ x =>
      apply congrArg (Quotient.mk (QuotientGroup.rightRel H))
      group

@[simp] theorem cosetStep_inv_cosetStep (H : Subgroup (FreeGroup α))
    (g : FreeGroup α) (x : Coset H) :
    cosetStep H g⁻¹ (cosetStep H g x) = x := by
  rw [← cosetStep_mul H g⁻¹ g x]
  simp

@[simp] theorem cosetStep_cosetStep_inv (H : Subgroup (FreeGroup α))
    (g : FreeGroup α) (x : Coset H) :
    cosetStep H g (cosetStep H g⁻¹ x) = x := by
  rw [← cosetStep_mul H g g⁻¹ x]
  simp

/-- The coset reached after the suffix beginning at `k` has been read. -/
noncomputable def suffixCoset (H : Subgroup (FreeGroup α))
    (L : List (α × Bool)) (k : ℕ) : Coset H :=
  Quotient.mk _ ((FreeGroup.mk (L.drop k))⁻¹)

/-- The finite set of cosets visited while reading a word from right to left. -/
noncomputable def wordVertices (H : Subgroup (FreeGroup α))
    (L : List (α × Bool)) : Finset (Coset H) :=
  (Finset.range (L.length + 1)).image (suffixCoset H L)

/-- Vertices retained for a finite family of words. -/
noncomputable def vertices (H : Subgroup (FreeGroup α))
    (W : Finset (FreeGroup α)) : Finset (Coset H) :=
  W.biUnion (fun w ↦ wordVertices H w.toWord)

theorem suffixCoset_mem_vertices (H : Subgroup (FreeGroup α))
    {W : Finset (FreeGroup α)} {w : FreeGroup α} (hw : w ∈ W)
    {k : ℕ} (hk : k ≤ w.toWord.length) :
    suffixCoset H w.toWord k ∈ vertices H W := by
  rw [vertices, Finset.mem_biUnion]
  refine ⟨w, hw, ?_⟩
  rw [wordVertices, Finset.mem_image]
  exact ⟨k, Finset.mem_range.mpr (by omega), rfl⟩

section PartialAction

variable (H : Subgroup (FreeGroup α)) (W : Finset (FreeGroup α))

abbrev Vertex := {x : Coset H // x ∈ vertices H W}

def IsSource (a : α) (x : Vertex H W) : Prop :=
  cosetStep H (FreeGroup.of a) x.1 ∈ vertices H W

def IsTarget (a : α) (y : Vertex H W) : Prop :=
  cosetStep H (FreeGroup.of a)⁻¹ y.1 ∈ vertices H W

noncomputable def fwd (a : α) (x : Vertex H W) (hx : IsSource H W a x) :
    Vertex H W := ⟨cosetStep H (FreeGroup.of a) x.1, hx⟩

noncomputable def bwd (a : α) (y : Vertex H W) (hy : IsTarget H W a y) :
    Vertex H W := ⟨cosetStep H (FreeGroup.of a)⁻¹ y.1, hy⟩

noncomputable def sourceTargetEquiv (a : α) :
    {x : Vertex H W // IsSource H W a x} ≃
      {y : Vertex H W // IsTarget H W a y} where
  toFun x := ⟨fwd H W a x.1 x.2, by
    exact (show cosetStep H (FreeGroup.of a)⁻¹
        (cosetStep H (FreeGroup.of a) x.1.1) ∈ vertices H W by
      rw [cosetStep_inv_cosetStep]
      exact x.1.2)⟩
  invFun y := ⟨bwd H W a y.1 y.2, by
    exact (show cosetStep H (FreeGroup.of a)
        (cosetStep H (FreeGroup.of a)⁻¹ y.1.1) ∈ vertices H W by
      rw [cosetStep_cosetStep_inv]
      exact y.1.2)⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    simp [fwd, bwd]
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    simp [fwd, bwd]

theorem card_compl_eq (a : α) :
    Fintype.card {x : Vertex H W // ¬ IsSource H W a x} =
      Fintype.card {y : Vertex H W // ¬ IsTarget H W a y} := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl,
    Fintype.card_congr (sourceTargetEquiv H W a)]

/-- Completion of the restricted coset action to a permutation of the finite
vertex set. -/
noncomputable def letterPerm (a : α) : Equiv.Perm (Vertex H W) :=
  (Equiv.sumCompl (IsSource H W a)).symm.trans
    (((sourceTargetEquiv H W a).sumCongr
        (Fintype.equivOfCardEq (card_compl_eq H W a))).trans
      (Equiv.sumCompl (IsTarget H W a)))

theorem letterPerm_apply_of_source (a : α) (x : Vertex H W)
    (hx : IsSource H W a x) :
    letterPerm H W a x = fwd H W a x hx := by
  rw [letterPerm, Equiv.trans_apply, Equiv.trans_apply,
    Equiv.sumCompl_symm_apply_of_pos hx]
  rfl

theorem letterPerm_symm_apply_of_target (a : α) (y : Vertex H W)
    (hy : IsTarget H W a y) :
    (letterPerm H W a).symm y = bwd H W a y hy := by
  rw [letterPerm, Equiv.symm_trans_apply, Equiv.symm_trans_apply,
    Equiv.sumCompl_symm_apply_of_pos hy]
  rfl

end PartialAction

end FreeGroupHall
end GroupApproximation
