import GroupApproximation.Higman.OmegaTowerStages

/-!
# The low-row/free-code projection of the restricted Omega first stage

The one-letter projection to the first central HNN stage forgets which
selected block produced a code letter.  That loss is fatal for the static
seam normal form.  This file retains the full rank-three code: it builds the
three centralizing stages directly over the free row basis and maps them to
the free group on the disjoint union of

* row indices strictly below the cutoff, and
* the three code generators.

Rows at or beyond the cutoff die, so all three HNN relations are respected.
The resulting target is the free-product normal-form carrier needed by the
selected-orbit argument.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq
open HNNExtension

/-- The associated subgroup in the free row basis. -/
def tailIndexSub (m : ℕ) : Subgroup (FreeGroup ℤ) :=
  RowDeletionGraph.indexSub (fun i : ℤ => (m : ℤ) ≤ i)

/-- The row letters retained by the low-row quotient. -/
abbrev LowIndex (m : ℕ) := {i : ℤ // i < (m : ℤ)}

/-- The free product of the low row and the full rank-three code, written as
one free group on a disjoint alphabet. -/
abbrev LowStableFree (m : ℕ) := FreeGroup (LowIndex m ⊕ Fin 3)

/-- Inclusion of the full rank-three code as the right free factor. -/
def stableFreeHom (m : ℕ) : F₃ →* LowStableFree m :=
  FreeGroup.map Sum.inr

/-- Kill the tail rows and retain every row below the cutoff as a distinct
left-factor generator. -/
noncomputable def lowRowProjection (m : ℕ) :
    FreeGroup ℤ →* LowStableFree m :=
  FreeGroup.lift fun i =>
    if hi : i < (m : ℤ) then FreeGroup.of (Sum.inl ⟨i, hi⟩) else 1

@[simp] theorem lowRowProjection_of_lt (m : ℕ) {i : ℤ}
    (hi : i < (m : ℤ)) :
    lowRowProjection m (FreeGroup.of i) =
      FreeGroup.of (Sum.inl (⟨i, hi⟩ : LowIndex m)) := by
  simp [lowRowProjection, hi]

@[simp] theorem lowRowProjection_of_ge (m : ℕ) {i : ℤ}
    (hi : (m : ℤ) ≤ i) :
    lowRowProjection m (FreeGroup.of i) = 1 := by
  simp [lowRowProjection, not_lt.mpr hi]

/-- The low-row projection kills the whole associated tail subgroup. -/
theorem lowRowProjection_eq_one_of_mem_tailIndexSub
    {m : ℕ} {w : FreeGroup ℤ} (hw : w ∈ tailIndexSub m) :
    lowRowProjection m w = 1 := by
  unfold tailIndexSub RowDeletionGraph.indexSub at hw
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      exact lowRowProjection_of_ge m hi
  | one => exact map_one _
  | mul x y _ _ hx hy => rw [map_mul, hx, hy, one_mul]
  | inv x _ hx => rw [map_inv, hx, inv_one]

/-! ## The restricted three-stage tower and its quotient -/

abbrev IndexCent1 (m : ℕ) := CentHNN (tailIndexSub m)

def indexEmb1 (m : ℕ) : FreeGroup ℤ →* IndexCent1 m := of

def indexPush1 (m : ℕ) : Subgroup (IndexCent1 m) :=
  (tailIndexSub m).map (indexEmb1 m)

abbrev IndexCent2 (m : ℕ) := CentHNN (indexPush1 m)

def indexEmb2 (m : ℕ) : FreeGroup ℤ →* IndexCent2 m :=
  (of : IndexCent1 m →* IndexCent2 m).comp (indexEmb1 m)

def indexPush2 (m : ℕ) : Subgroup (IndexCent2 m) :=
  (indexPush1 m).map (of : IndexCent1 m →* IndexCent2 m)

abbrev IndexCent3 (m : ℕ) := CentHNN (indexPush2 m)

def indexEmb3 (m : ℕ) : FreeGroup ℤ →* IndexCent3 m :=
  (of : IndexCent2 m →* IndexCent3 m).comp (indexEmb2 m)

def indexGen1 (m : ℕ) : IndexCent3 m :=
  (of : IndexCent2 m →* IndexCent3 m)
    ((of : IndexCent1 m →* IndexCent2 m) (t : IndexCent1 m))

def indexGen2 (m : ℕ) : IndexCent3 m :=
  (of : IndexCent2 m →* IndexCent3 m) (t : IndexCent2 m)

def indexGen3 (m : ℕ) : IndexCent3 m :=
  (t : IndexCent3 m)

def indexGenHom (m : ℕ) : F₃ →* IndexCent3 m :=
  FreeGroup.lift fun i : Fin 3 =>
    if i = 0 then indexGen1 m else if i = 1 then indexGen2 m else indexGen3 m

@[simp] theorem indexGenHom_a (m : ℕ) :
    indexGenHom m a = indexGen1 m := by
  unfold indexGenHom a
  rw [FreeGroup.lift_apply_of]
  simp

@[simp] theorem indexGenHom_b (m : ℕ) :
    indexGenHom m b = indexGen2 m := by
  unfold indexGenHom b
  rw [FreeGroup.lift_apply_of]
  simp

@[simp] theorem indexGenHom_c (m : ℕ) :
    indexGenHom m c = indexGen3 m := by
  unfold indexGenHom c
  rw [FreeGroup.lift_apply_of]
  simp

noncomputable def lowStableProjection1 (m : ℕ) :
    IndexCent1 m →* LowStableFree m :=
  HNNExtension.lift (lowRowProjection m) (stableFreeHom m a) (by
    intro z
    have hz := lowRowProjection_eq_one_of_mem_tailIndexSub z.property
    change stableFreeHom m a * lowRowProjection m z =
      lowRowProjection m z * stableFreeHom m a
    rw [hz, mul_one, one_mul])

@[simp] theorem lowStableProjection1_of (m : ℕ) (w : FreeGroup ℤ) :
    lowStableProjection1 m (of w) = lowRowProjection m w := by
  simp [lowStableProjection1, HNNExtension.lift_of]

@[simp] theorem lowStableProjection1_t (m : ℕ) :
    lowStableProjection1 m (t : IndexCent1 m) = stableFreeHom m a := by
  simp [lowStableProjection1, HNNExtension.lift_t]

theorem lowStableProjection1_eq_one_of_mem_push1
    {m : ℕ} {z : IndexCent1 m} (hz : z ∈ indexPush1 m) :
    lowStableProjection1 m z = 1 := by
  obtain ⟨w, hw, rfl⟩ := hz
  change lowStableProjection1 m (of w) = 1
  rw [lowStableProjection1_of,
    lowRowProjection_eq_one_of_mem_tailIndexSub hw]

noncomputable def lowStableProjection2 (m : ℕ) :
    IndexCent2 m →* LowStableFree m :=
  HNNExtension.lift (lowStableProjection1 m) (stableFreeHom m b) (by
    intro z
    have hz := lowStableProjection1_eq_one_of_mem_push1 z.property
    change stableFreeHom m b * lowStableProjection1 m z =
      lowStableProjection1 m z * stableFreeHom m b
    rw [hz, mul_one, one_mul])

@[simp] theorem lowStableProjection2_of (m : ℕ) (z : IndexCent1 m) :
    lowStableProjection2 m (of z) = lowStableProjection1 m z := by
  simp [lowStableProjection2, HNNExtension.lift_of]

@[simp] theorem lowStableProjection2_t (m : ℕ) :
    lowStableProjection2 m (t : IndexCent2 m) = stableFreeHom m b := by
  simp [lowStableProjection2, HNNExtension.lift_t]

theorem lowStableProjection2_eq_one_of_mem_push2
    {m : ℕ} {z : IndexCent2 m} (hz : z ∈ indexPush2 m) :
    lowStableProjection2 m z = 1 := by
  obtain ⟨w, hw, rfl⟩ := hz
  rw [lowStableProjection2_of,
    lowStableProjection1_eq_one_of_mem_push1 hw]

noncomputable def lowStableProjection3 (m : ℕ) :
    IndexCent3 m →* LowStableFree m :=
  HNNExtension.lift (lowStableProjection2 m) (stableFreeHom m c) (by
    intro z
    have hz := lowStableProjection2_eq_one_of_mem_push2 z.property
    change stableFreeHom m c * lowStableProjection2 m z =
      lowStableProjection2 m z * stableFreeHom m c
    rw [hz, mul_one, one_mul])

@[simp] theorem lowStableProjection3_of (m : ℕ) (z : IndexCent2 m) :
    lowStableProjection3 m (of z) = lowStableProjection2 m z := by
  simp [lowStableProjection3, HNNExtension.lift_of]

@[simp] theorem lowStableProjection3_t (m : ℕ) :
    lowStableProjection3 m (t : IndexCent3 m) = stableFreeHom m c := by
  simp [lowStableProjection3, HNNExtension.lift_t]

/-! ## Exact generator formulas -/

@[simp] theorem lowStableProjection3_emb3 (m : ℕ) (w : FreeGroup ℤ) :
    lowStableProjection3 m (indexEmb3 m w) =
      lowRowProjection m w := by
  simp [indexEmb3, indexEmb2, indexEmb1]

@[simp] theorem lowStableProjection3_gen1 (m : ℕ) :
    lowStableProjection3 m (indexGen1 m) = stableFreeHom m a := by
  simp [indexGen1]

@[simp] theorem lowStableProjection3_gen2 (m : ℕ) :
    lowStableProjection3 m (indexGen2 m) = stableFreeHom m b := by
  simp [indexGen2]

@[simp] theorem lowStableProjection3_gen3 (m : ℕ) :
    lowStableProjection3 m (indexGen3 m) = stableFreeHom m c := by
  simp [indexGen3]

/-- The quotient retains the entire rank-three code, not merely its first
stable-letter exponent. -/
theorem lowStableProjection3_comp_genHom (m : ℕ) :
    (lowStableProjection3 m).comp (indexGenHom m) =
      stableFreeHom m := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  fin_cases i
  · change lowStableProjection3 m (indexGenHom m a) = stableFreeHom m a
    rw [indexGenHom_a, lowStableProjection3_gen1]
  · change lowStableProjection3 m (indexGenHom m b) = stableFreeHom m b
    rw [indexGenHom_b, lowStableProjection3_gen2]
  · change lowStableProjection3 m (indexGenHom m c) = stableFreeHom m c
    rw [indexGenHom_c, lowStableProjection3_gen3]

noncomputable def indexBaseCode (m : ℕ) (beta : E) : IndexCent3 m :=
  indexEmb3 m (elt beta)

noncomputable def indexGenCode (m : ℕ) (beta : E) : IndexCent3 m :=
  indexGenHom m (aElt beta)

noncomputable def indexLinkElem (m : ℕ) (beta : E) : IndexCent3 m :=
  indexGenCode m beta * (indexBaseCode m beta)⁻¹

@[simp] theorem lowStableProjection3_indexBaseCode (m : ℕ) (beta : E) :
    lowStableProjection3 m (indexBaseCode m beta) =
      lowRowProjection m (elt beta) := by
  simp [indexBaseCode]

@[simp] theorem lowStableProjection3_indexGenCode (m : ℕ) (beta : E) :
    lowStableProjection3 m (indexGenCode m beta) =
      stableFreeHom m (aElt beta) := by
  rw [indexGenCode, ← MonoidHom.comp_apply,
    lowStableProjection3_comp_genHom]

@[simp] theorem lowStableProjection3_indexLinkElem (m : ℕ) (beta : E) :
    lowStableProjection3 m (indexLinkElem m beta) =
      stableFreeHom m (aElt beta) *
        (lowRowProjection m (elt beta))⁻¹ := by
  simp [indexLinkElem]

end Omega
end Higman
end GroupApproximation
