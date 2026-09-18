import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.EmbeddingConnesRoundingCount

/-!
# Connes' trick, layer rounding (part 3): the Hilbert–Schmidt mass of the layered defect

Lane TWWSch3b1 (WO-TWWSch-3b-1), toward `isAmenableTrace_of_isNuclearCStarAlgebra`
(`non_mf_group_notes.tex`, Tikuisis--White--Winter input to Schafhauser's argument). Source:
Brown--Ozawa, *C⋆-algebras and finite-dimensional approximations*, Thm 6.2.7 (Connes' trick),
the rounding of the eigenvalue multiplicities. Adapted, after review, from the never-wired
foreign `TWWLanes/ConnesTrick` rounding module of the same content.

Write `Δ = V - X W` and `T_a = layerTail c a X W`. On the layered model:

* the row of `⟨i, a⟩` in `layer c V - layer c X * layer c W` has mass
  `∑ⱼ [a < cⱼ] |Δᵢⱼ + T_a(i, j)|²` (`sum_normSq_layer_defect_row`);
* summing over the rows gives `∑ᵢ ∑_{a < cᵢ} ∑ⱼ [a < cⱼ] |Δᵢⱼ + T_a(i, j)|²`
  (`sum_normSq_layer_defect_eq`);
* the parallelogram estimate splits this into a `Δ` part and a `T` part
  (`sum_normSq_layer_defect_split`);
* the `Δ` part is at most `∑ᵢ ∑ⱼ cⱼ · 2|Δᵢⱼ|²` (`sum_layer_count_le`).

Everything here is proved.
-/

namespace GroupApproximation.Full.TWWSchafhauser.Connes

open Matrix Quasidiagonal Finset

noncomputable section

variable {Y : FiniteModel}

/-- The Hilbert–Schmidt mass of one row of the layered defect. -/
theorem sum_normSq_layer_defect_row (c : Y → ℕ) (V X W : Matrix Y Y ℂ) (p : layerModel Y c) :
    ∑ q : layerModel Y c, Complex.normSq ((layer c V - layer c X * layer c W) p q)
      = ∑ j, (if (p.2 : ℕ) < c j then
          Complex.normSq ((V - X * W) p.1 j + layerTail c (p.2 : ℕ) X W p.1 j) else 0) := by
  have e1 : ∀ q : layerModel Y c, Complex.normSq ((layer c V - layer c X * layer c W) p q)
      = Complex.normSq (if (p.2 : ℕ) = (q.2 : ℕ) then
          (V - X * W) p.1 q.1 + layerTail c (p.2 : ℕ) X W p.1 q.1 else 0) := fun q ↦ by
    rw [layer_defect_apply]
  have e2 : ∀ (j : Y) (b : ℕ), Complex.normSq (if (p.2 : ℕ) = b then
          (V - X * W) p.1 j + layerTail c (p.2 : ℕ) X W p.1 j else 0)
      = if (p.2 : ℕ) = b then
          Complex.normSq ((V - X * W) p.1 j + layerTail c (p.2 : ℕ) X W p.1 j) else 0 := by
    intro j b
    by_cases hb : (p.2 : ℕ) = b
    · rw [if_pos hb, if_pos hb]
    · rw [if_neg hb, if_neg hb, Complex.normSq_zero]
  calc ∑ q : layerModel Y c, Complex.normSq ((layer c V - layer c X * layer c W) p q)
      = ∑ q : layerModel Y c, Complex.normSq (if (p.2 : ℕ) = (q.2 : ℕ) then
          (V - X * W) p.1 q.1 + layerTail c (p.2 : ℕ) X W p.1 q.1 else 0) :=
        Finset.sum_congr rfl fun q _ ↦ e1 q
    _ = ∑ j, ∑ b ∈ range (c j), Complex.normSq (if (p.2 : ℕ) = b then
          (V - X * W) p.1 j + layerTail c (p.2 : ℕ) X W p.1 j else 0) :=
        sum_layerModel_eq c (fun j b ↦ Complex.normSq (if (p.2 : ℕ) = b then
          (V - X * W) p.1 j + layerTail c (p.2 : ℕ) X W p.1 j else 0))
    _ = ∑ j, ∑ b ∈ range (c j), (if (p.2 : ℕ) = b then
          Complex.normSq ((V - X * W) p.1 j + layerTail c (p.2 : ℕ) X W p.1 j) else 0) :=
        Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun b _ ↦ e2 j b
    _ = ∑ j, (if (p.2 : ℕ) < c j then
          Complex.normSq ((V - X * W) p.1 j + layerTail c (p.2 : ℕ) X W p.1 j) else 0) := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        simp only [Finset.sum_ite_eq, Finset.mem_range]

/-- The unnormalised Hilbert–Schmidt mass of the layered defect as a layer sum. -/
theorem sum_normSq_layer_defect_eq (c : Y → ℕ) (V X W : Matrix Y Y ℂ) :
    ∑ p : layerModel Y c, ∑ q : layerModel Y c,
        Complex.normSq ((layer c V - layer c X * layer c W) p q)
      = ∑ i, ∑ a ∈ range (c i), ∑ j, (if a < c j then
          Complex.normSq ((V - X * W) i j + layerTail c a X W i j) else 0) := by
  calc ∑ p : layerModel Y c, ∑ q : layerModel Y c,
        Complex.normSq ((layer c V - layer c X * layer c W) p q)
      = ∑ p : layerModel Y c, ∑ j, (if (p.2 : ℕ) < c j then
          Complex.normSq ((V - X * W) p.1 j + layerTail c (p.2 : ℕ) X W p.1 j) else 0) :=
        Finset.sum_congr rfl fun p _ ↦ sum_normSq_layer_defect_row c V X W p
    _ = ∑ i, ∑ a ∈ range (c i), ∑ j, (if a < c j then
          Complex.normSq ((V - X * W) i j + layerTail c a X W i j) else 0) :=
        sum_layerModel_eq c (fun i a ↦ ∑ j, (if a < c j then
          Complex.normSq ((V - X * W) i j + layerTail c a X W i j) else 0))

/-- Splitting the layer sum into the defect part and the tail part. -/
theorem sum_normSq_layer_defect_split (c : Y → ℕ) (D T : ℕ → Y → Y → ℂ) :
    ∑ i, ∑ a ∈ range (c i), ∑ j, (if a < c j then Complex.normSq (D a i j + T a i j) else 0)
      ≤ ∑ i, ∑ a ∈ range (c i), ∑ j, (if a < c j then 2 * Complex.normSq (D a i j) else 0)
        + ∑ i, ∑ a ∈ range (c i), ∑ j,
            (if a < c j then 2 * Complex.normSq (T a i j) else 0) := by
  have hpt : ∀ (i : Y) (a : ℕ) (j : Y),
      (if a < c j then Complex.normSq (D a i j + T a i j) else 0)
        ≤ (if a < c j then 2 * Complex.normSq (D a i j) else 0)
          + (if a < c j then 2 * Complex.normSq (T a i j) else 0) := by
    intro i a j
    by_cases h : a < c j
    · rw [if_pos h, if_pos h, if_pos h]
      exact normSq_add_le_two _ _
    · exact le_of_eq (by rw [if_neg h, if_neg h, if_neg h, add_zero])
  calc ∑ i, ∑ a ∈ range (c i), ∑ j,
        (if a < c j then Complex.normSq (D a i j + T a i j) else 0)
      ≤ ∑ i, ∑ a ∈ range (c i), ∑ j,
          ((if a < c j then 2 * Complex.normSq (D a i j) else 0)
            + (if a < c j then 2 * Complex.normSq (T a i j) else 0)) :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun a _ ↦
          Finset.sum_le_sum fun j _ ↦ hpt i a j
    _ = ∑ i, ∑ a ∈ range (c i), ∑ j, (if a < c j then 2 * Complex.normSq (D a i j) else 0)
        + ∑ i, ∑ a ∈ range (c i), ∑ j,
            (if a < c j then 2 * Complex.normSq (T a i j) else 0) := by
        simp only [Finset.sum_add_distrib]

/-- Counting the layers of a row that see the column `j`. -/
theorem sum_layer_count_le (c : Y → ℕ) (f : Y → Y → ℝ) (hf : ∀ i j, 0 ≤ f i j) :
    ∑ i, ∑ a ∈ range (c i), ∑ j, (if a < c j then f i j else 0)
      ≤ ∑ i, ∑ j, (c j : ℝ) * f i j := by
  calc ∑ i, ∑ a ∈ range (c i), ∑ j, (if a < c j then f i j else 0)
      = ∑ i, ∑ j, ∑ a ∈ range (c i), (if a < c j then f i j else 0) :=
        Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ ≤ ∑ i, ∑ j, (c j : ℝ) * f i j :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
          sum_range_ite_lt_le (c i) (c j) (f i j) (hf i j)

end

end GroupApproximation.Full.TWWSchafhauser.Connes
