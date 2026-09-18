import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.EmbeddingConnesLayerModel
import GroupApproximation.Sofic.NormTraceGap

/-!
# Connes' trick, layer rounding (part 1): entries, trace and products of the layered model

Lane TWWSch3b1 (WO-TWWSch-3b-1), toward `isAmenableTrace_of_isNuclearCStarAlgebra`
(`non_mf_group_notes.tex`, Tikuisis--White--Winter input to Schafhauser's argument). Source:
Brown--Ozawa, *C⋆-algebras and finite-dimensional approximations*, Thm 6.2.7 (Connes' trick),
the rounding of the eigenvalue multiplicities. Adapted, after review, from the never-wired
foreign `TWWLanes/ConnesTrick` rounding module of the same content.

This file supplies the exact formulas for the layered model `layer c M` of
`ConnesTrick/LayerModel.lean` that the rounding estimate uses.

* Sums over `layerModel Y c = Σ i, Fin (c i)` are iterated sums
  `∑ᵢ ∑_{a < cᵢ}` (`sum_layerModel_eq`). In particular the model has `∑ᵢ cᵢ` points
  (`card_layerModel`).
* `tr(layer c M) = ∑ᵢ cᵢ Mᵢᵢ`, so `normTrace(layer c M) = (∑ᵢ cᵢ Mᵢᵢ) / ∑ᵢ cᵢ`
  (`trace_layer`, `normTrace_layer`).
* `(layer c X * layer c W)⟨i,a⟩⟨j,b⟩ = [a = b] ∑_{k : a < cₖ} Xᵢₖ Wₖⱼ`
  (`layer_mul_apply`).
* Hence the multiplicative defect of the layered model is, on the diagonal layers,
  `(V - X W)ᵢⱼ + ∑_{k : cₖ ≤ a} Xᵢₖ Wₖⱼ` (`layer_defect_apply`). The second summand is the
  entry of `E_a X (1 - E_a) W E_a` from the proof sketch in `EmbeddingConnesRoundingEndpoint`.

Everything here is proved.
-/

namespace GroupApproximation.Full.TWWSchafhauser.Connes

open Matrix Quasidiagonal Finset

noncomputable section

variable {Y : FiniteModel}

/-- Sums over the layered model are iterated sums over the layers of each base point. -/
theorem sum_layerModel_eq {M : Type*} [AddCommMonoid M] (c : Y → ℕ) (f : Y → ℕ → M) :
    ∑ p : layerModel Y c, f p.1 (p.2 : ℕ) = ∑ i, ∑ a ∈ range (c i), f i a := by
  calc ∑ p : layerModel Y c, f p.1 (p.2 : ℕ) = ∑ i, ∑ b : Fin (c i), f i (b : ℕ) :=
        Fintype.sum_sigma (fun p : (Σ i : Y, Fin (c i)) ↦ f p.1 (p.2 : ℕ))
    _ = ∑ i, ∑ a ∈ range (c i), f i a :=
        Finset.sum_congr rfl fun i _ ↦ Fin.sum_univ_eq_sum_range (f i) (c i)

/-- The layered model has `∑ᵢ cᵢ` points. -/
theorem card_layerModel (c : Y → ℕ) : Fintype.card (layerModel Y c) = ∑ i, c i := by
  first
    | (show Fintype.card (Σ i : Y, Fin (c i)) = _
       simp only [Fintype.card_sigma, Fintype.card_fin]
       done)
    | (have h := sum_layerModel_eq (M := ℕ) c (fun _ _ ↦ 1)
       simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one,
         Finset.card_univ] at h
       exact h)

/-- The trace of a layered matrix. -/
theorem trace_layer (c : Y → ℕ) (M : Matrix Y Y ℂ) :
    trace (layer c M) = ∑ i, (c i : ℂ) * M i i := by
  have h1 : ∀ p : layerModel Y c, layer c M p p = M p.1 p.1 := fun p ↦ by
    rw [layer_apply, if_pos rfl]
  have h2 : trace (layer c M) = ∑ p : layerModel Y c, M p.1 p.1 :=
    Finset.sum_congr rfl fun p _ ↦ h1 p
  calc trace (layer c M) = ∑ p : layerModel Y c, M p.1 p.1 := h2
    _ = ∑ i, ∑ _a ∈ range (c i), M i i := sum_layerModel_eq c (fun i (_ : ℕ) ↦ M i i)
    _ = ∑ i, (c i : ℂ) * M i i := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The normalised trace of a layered matrix. -/
theorem normTrace_layer (c : Y → ℕ) (M : Matrix Y Y ℂ) :
    normTrace (layerModel Y c) (layer c M)
      = (∑ i, (c i : ℂ) * M i i) / ((∑ i, c i : ℕ) : ℂ) := by
  show trace (layer c M) / ((Fintype.card (layerModel Y c) : ℕ) : ℂ) = _
  rw [trace_layer, card_layerModel]

/-- Entries of a product of layered matrices. -/
theorem layer_mul_apply (c : Y → ℕ) (X W : Matrix Y Y ℂ) (p q : layerModel Y c) :
    (layer c X * layer c W) p q
      = if (p.2 : ℕ) = (q.2 : ℕ) then
          ∑ k, (if (p.2 : ℕ) < c k then X p.1 k * W k q.1 else 0) else 0 := by
  have h1 : (layer c X * layer c W) p q = ∑ k, ∑ n ∈ range (c k),
      (if (p.2 : ℕ) = n then X p.1 k else 0) * (if n = (q.2 : ℕ) then W k q.1 else 0) := by
    rw [Matrix.mul_apply]
    exact sum_layerModel_eq c (fun (k : Y) (n : ℕ) ↦
      (if (p.2 : ℕ) = n then X p.1 k else 0) * (if n = (q.2 : ℕ) then W k q.1 else 0))
  rw [h1]
  by_cases h : (p.2 : ℕ) = (q.2 : ℕ)
  · rw [if_pos h]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have e : ∀ n ∈ range (c k), (if (p.2 : ℕ) = n then X p.1 k else 0) *
        (if n = (q.2 : ℕ) then W k q.1 else 0)
        = if (p.2 : ℕ) = n then X p.1 k * W k q.1 else 0 := by
      intro n _
      by_cases hn : (p.2 : ℕ) = n
      · rw [if_pos hn, if_pos (hn.symm.trans h), if_pos hn]
      · rw [if_neg hn, if_neg hn, zero_mul]
    rw [Finset.sum_congr rfl e]
    simp only [Finset.sum_ite_eq, Finset.mem_range]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun k _ ↦ Finset.sum_eq_zero fun n _ ↦ ?_
    by_cases hn : (p.2 : ℕ) = n
    · have hq : ¬ (n = (q.2 : ℕ)) := fun h' ↦ h (hn.trans h')
      rw [if_neg hq, mul_zero]
    · rw [if_neg hn, zero_mul]

/-- The tail sum `∑_{k : cₖ ≤ a} Xᵢₖ Wₖⱼ`: the entry of `E_a X (1 - E_a) W` on layer `a`. -/
def layerTail (c : Y → ℕ) (a : ℕ) (X W : Matrix Y Y ℂ) (i j : Y) : ℂ :=
  ∑ k, if c k ≤ a then X i k * W k j else 0

/-- Entries of the multiplicative defect of the layered model. -/
theorem layer_defect_apply (c : Y → ℕ) (V X W : Matrix Y Y ℂ) (p q : layerModel Y c) :
    (layer c V - layer c X * layer c W) p q
      = if (p.2 : ℕ) = (q.2 : ℕ) then
          (V - X * W) p.1 q.1 + layerTail c (p.2 : ℕ) X W p.1 q.1 else 0 := by
  simp only [Matrix.sub_apply]
  rw [layer_mul_apply, layer_apply]
  by_cases h : (p.2 : ℕ) = (q.2 : ℕ)
  · rw [if_pos h, if_pos h, if_pos h]
    simp only [Matrix.sub_apply, Matrix.mul_apply, layerTail]
    have e : ∀ k, X p.1 k * W k q.1
        = (if (p.2 : ℕ) < c k then X p.1 k * W k q.1 else 0)
          + (if c k ≤ (p.2 : ℕ) then X p.1 k * W k q.1 else 0) := fun k ↦ by
      by_cases hk : (p.2 : ℕ) < c k
      · rw [if_pos hk, if_neg (not_le.mpr hk), add_zero]
      · rw [if_neg hk, if_pos (not_lt.mp hk), zero_add]
    have hsum : ∑ k, X p.1 k * W k q.1
        = ∑ k, (if (p.2 : ℕ) < c k then X p.1 k * W k q.1 else 0)
          + ∑ k, (if c k ≤ (p.2 : ℕ) then X p.1 k * W k q.1 else 0) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ ↦ e k
    rw [hsum]
    ring
  · rw [if_neg h, if_neg h, if_neg h, sub_zero]

end

end GroupApproximation.Full.TWWSchafhauser.Connes
