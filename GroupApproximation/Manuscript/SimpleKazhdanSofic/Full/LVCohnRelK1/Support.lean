import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnRelK1.Ideal
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnRelK1.Corner

/-!
# Matrices over the kernel ideal as matrices over `𝔽₂`

Finitely many elements of the kernel `(p) ≅ M_∞(𝔽₂)` of `C₂(𝔽₂) → L_{𝔽₂}(1,2)` live in a common
finite corner spanned by `e_{μν}` with `μ, ν ∈ W`.  An `N × N` matrix `P` with `P - 1` over the
kernel is therefore `1 + ∑ B_{ab} E_{ab}` for the matrix units `E_{(i,μ),(j,ν)} = e_{ij} ⊗ e_{μν}`
indexed by `Fin N × W`.  This is step W1 of `simple_kazhdan_sofic_group.tex` l.733-735
(Ara-Brustenga-Cortiñas 2009, excision for `(p) ≅ M_∞(𝔽₂)`).
-/

namespace GroupApproximation.Full.LVCohnRelK1

noncomputable section

/-- Finitely many kernel elements have a common finite support of words
(`simple_kazhdan_sofic_group.tex` l.733-735). -/
theorem exists_common_support {ι : Type*} [Fintype ι] (z : ι → CohnTwoF2)
    (hz : ∀ i, z i ∈ cohnIdeal) :
    ∃ (W : Finset (List Bool)) (f : ι → W → W → ZMod 2),
      ∀ i, z i = ∑ μ : W, ∑ ν : W, f i μ ν • unitE μ.1 ν.1 := by
  choose c hc using fun i => exists_finsupp_of_mem (hz i)
  obtain ⟨W, hW⟩ : ∃ W : Finset (List Bool), ∀ i, (c i).support ⊆ W ×ˢ W :=
    ⟨Finset.univ.biUnion fun i => (c i).support.image Prod.fst ∪ (c i).support.image Prod.snd,
      fun i q hq => Finset.mem_product.mpr
        ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
            Finset.mem_union_left _ (Finset.mem_image_of_mem Prod.fst hq)⟩,
          Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
            Finset.mem_union_right _ (Finset.mem_image_of_mem Prod.snd hq)⟩⟩⟩
  refine ⟨W, fun i μ ν => c i (μ.1, ν.1), fun i => ?_⟩
  have h1 : ((c i).sum fun q a => a • unitE q.1 q.2) = ∑ q ∈ W ×ˢ W, c i q • unitE q.1 q.2 :=
    Finsupp.sum_of_support_subset (c i) (hW i) (fun q a => a • unitE q.1 q.2)
      fun q _ => zero_smul (ZMod 2) (unitE q.1 q.2)
  calc z i = (c i).sum fun q a => a • unitE q.1 q.2 := (hc i).symm
    _ = ∑ q ∈ W ×ˢ W, c i q • unitE q.1 q.2 := h1
    _ = ∑ μ ∈ W, ∑ ν ∈ W, c i (μ, ν) • unitE μ ν := Finset.sum_product W W _
    _ = ∑ μ : W, ∑ ν ∈ W, c i (μ.1, ν) • unitE μ.1 ν :=
      (Finset.sum_coe_sort (s := W) (f := fun μ => ∑ ν ∈ W, c i (μ, ν) • unitE μ ν)).symm
    _ = ∑ μ : W, ∑ ν : W, c i (μ.1, ν.1) • unitE μ.1 ν.1 :=
      Finset.sum_congr rfl fun μ _ =>
        (Finset.sum_coe_sort (s := W) (f := fun ν => c i (μ.1, ν) • unitE μ.1 ν)).symm

/-- The matrix units `E_{(i,μ),(j,ν)} = e_{ij} ⊗ e_{μν}` of `M_N(C₂(𝔽₂))`
(`simple_kazhdan_sofic_group.tex` l.733-735). -/
def cornerE (W : Finset (List Bool)) (N : ℕ) (a b : Fin N × W) :
    Matrix (Fin N) (Fin N) CohnTwoF2 :=
  Matrix.single a.1 b.1 (unitE a.2.1 b.2.1)

theorem cornerE_def (W : Finset (List Bool)) (N : ℕ) (a b : Fin N × W) :
    cornerE W N a b = Matrix.single a.1 b.1 (unitE a.2.1 b.2.1) := rfl

/-- The matrix unit law for `cornerE` (`simple_kazhdan_sofic_group.tex` l.733-735). -/
theorem cornerE_mul (W : Finset (List Bool)) (N : ℕ) (a b c d : Fin N × W) :
    cornerE W N a b * cornerE W N c d = if b = c then cornerE W N a d else 0 := by
  simp only [cornerE_def]
  by_cases hbc : b = c
  · subst hbc
    rw [if_pos rfl, Matrix.single_mul_single_same, unitE_mul_unitE, if_pos rfl]
  · rw [if_neg hbc]
    by_cases h1 : b.1 = c.1
    · have h2 : b.2.1 ≠ c.2.1 := fun h => hbc (Prod.ext h1 (Subtype.ext h))
      rw [← h1, Matrix.single_mul_single_same, unitE_mul_unitE, if_neg h2, Matrix.single_zero]
    · exact Matrix.single_mul_single_of_ne (c := unitE a.2.1 b.2.1) a.1 b.1 c.1 h1 _

theorem single_finset_sum {N : ℕ} {α : Type*} (s : Finset α) (i j : Fin N)
    (g : α → CohnTwoF2) :
    Matrix.single i j (∑ x ∈ s, g x) = ∑ x ∈ s, Matrix.single i j (g x) :=
  map_sum (Matrix.singleAddMonoidHom i j) g s

/-- A matrix with kernel entries is a sum of the matrix units `cornerE`
(`simple_kazhdan_sofic_group.tex` l.733-735). -/
theorem unitSum_cornerE {N : ℕ} (W : Finset (List Bool)) (M : Matrix (Fin N) (Fin N) CohnTwoF2)
    (B : Matrix (Fin N × W) (Fin N × W) (ZMod 2))
    (hM : ∀ i j, M i j = ∑ μ : W, ∑ ν : W, B (i, μ) (j, ν) • unitE μ.1 ν.1) :
    unitSum (cornerE W N) B = M := by
  have hsingle : ∀ i j, ∑ μ : W, ∑ ν : W, B (i, μ) (j, ν) • Matrix.single i j (unitE μ.1 ν.1) =
      Matrix.single i j (M i j) := fun i j => by
    rw [hM i j, single_finset_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [single_finset_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Matrix.smul_single]
  calc unitSum (cornerE W N) B = ∑ a : Fin N × W, ∑ b : Fin N × W, B a b • cornerE W N a b := rfl
    _ = ∑ i : Fin N, ∑ μ : W, ∑ b : Fin N × W, B (i, μ) b • cornerE W N (i, μ) b :=
      Fintype.sum_prod_type _
    _ = ∑ i : Fin N, ∑ μ : W, ∑ j : Fin N, ∑ ν : W,
          B (i, μ) (j, ν) • Matrix.single i j (unitE μ.1 ν.1) :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Fintype.sum_prod_type _
    _ = ∑ i : Fin N, ∑ j : Fin N, ∑ μ : W, ∑ ν : W,
          B (i, μ) (j, ν) • Matrix.single i j (unitE μ.1 ν.1) :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i : Fin N, ∑ j : Fin N, Matrix.single i j (M i j) :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsingle i j
    _ = M := (Matrix.matrix_eq_sum_single M).symm

end

end GroupApproximation.Full.LVCohnRelK1
