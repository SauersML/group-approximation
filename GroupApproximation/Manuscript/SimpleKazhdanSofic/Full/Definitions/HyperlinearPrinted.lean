import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Definitions.SoficPrinted
import GroupApproximation.Sofic.HyperlinearWeakBridge
import GroupApproximation.Sofic.MarkedCompressionSequentialKill
import GroupApproximation.Meta.AxiomGuard

/-!
# The printed hyperlinear definition is the corpus notion (`thm:main`, tex l.105–109)

`simple_kazhdan_sofic_group.tex`, the paragraph after Theorem `thm:main` (gap report, Lane 1, item
D1):

> Sofic and hyperlinear groups are defined by approximately multiplicative maps into finite
> symmetric groups with the normalized Hamming distance, and into unitary groups with the
> normalized Hilbert--Schmidt distance, that keep nontrivial elements uniformly far from~$1$.

`PrintedIsHyperlinear` (in `SoficPrinted`) records the printed definition with the normalized
Hilbert–Schmidt distance `√(hsDistSq Y A B)`.  The corpus notion `IsHyperlinear` asks for squared
separation `2 - ε` between distinct elements of `F`.

* `printedIsHyperlinear_of_isHyperlinear`: a corpus model on `F ∪ {1}` at accuracy
  `min (ε²) (1/8)` keeps nontrivial elements at distance `1/2` from `1`.
* `isHyperlinear_of_printedIsHyperlinear`: a printed model on `F ∪ F⁻¹ ∪ F⁻¹F ∪ {1}` at accuracy
  `η ≤ min 1 (min ε (δ/6))` separates distinct `g, h ∈ F` by squared distance `δ²/8`, through
  left invariance under the unitary `ψ(h⁻¹)` and `h⁻¹ g ≠ 1`; `isHyperlinear_of_isHyperlinearWeak`
  amplifies the separation.
* `printedIsHyperlinear_iff`.
-/

namespace GroupApproximation.Full.SK01

variable {G : Type*} [Group G]

/-- Left multiplication by a unitary preserves the squared normalized Hilbert–Schmidt distance. -/
theorem hsDistSq_mul_left_unitary (Y : FiniteModel) {V : Matrix Y Y ℂ}
    (hV : V ∈ Matrix.unitaryGroup Y ℂ) (hY : 0 < Fintype.card Y) (A B : Matrix Y Y ℂ) :
    hsDistSq Y (V * A) (V * B) = hsDistSq Y A B := by
  change hsNormSq Y (V * A - V * B) = hsNormSq Y (A - B)
  rw [← Matrix.mul_sub, hsNormSq_mul_left Y hV hY]

/-- The corpus hyperlinear notion gives the printed one, with uniform separation `1/2` from `1`. -/
theorem printedIsHyperlinear_of_isHyperlinear (hG : IsHyperlinear G) :
    PrintedIsHyperlinear G := by
  classical
  refine ⟨1 / 2, by norm_num, fun F ε hε => ?_⟩
  have hη : 0 < min (ε ^ 2) (1 / 8) := lt_min (pow_pos hε 2) (by norm_num)
  have hη1 : min (ε ^ 2) (1 / 8) ≤ ε ^ 2 := min_le_left _ _
  have hη2 : min (ε ^ 2) (1 / 8) ≤ 1 / 8 := min_le_right _ _
  obtain ⟨M⟩ := hG (insert 1 F) (min (ε ^ 2) (1 / 8)) hη
  have hmul : ∀ g ∈ F, ∀ h ∈ F,
      Real.sqrt (hsDistSq M.carrier (M.map (g * h)) (M.map g * M.map h)) ≤ ε := by
    intro g hg h hh
    refine (Real.sqrt_le_left hε.le).mpr ?_
    exact (M.multiplicative g (Finset.mem_insert_of_mem hg) h
      (Finset.mem_insert_of_mem hh)).trans hη1
  have hone : hsDistSq M.carrier 1 (M.map 1) ≤ min (ε ^ 2) (1 / 8) := by
    have h1 := M.multiplicative 1 (Finset.mem_insert_self 1 F) 1 (Finset.mem_insert_self 1 F)
    have hinv := hsDistSq_mul_left_unitary M.carrier (M.isUnitary 1) M.nonempty 1 (M.map 1)
    rw [mul_one] at h1
    rw [mul_one] at hinv
    rw [hinv] at h1
    exact h1
  refine ⟨M.carrier, M.map, M.nonempty, M.isUnitary, hmul, fun g hg hg1 => ?_⟩
  refine (Real.le_sqrt' (by norm_num)).mpr ?_
  have hsep := M.separated g (Finset.mem_insert_of_mem hg) 1 (Finset.mem_insert_self 1 F) hg1
  have htri := GroupApproximation.KazhdanCompressorCorner.hsDistSq_le_two_add_two M.carrier
    (M.map g) (M.map 1) 1
  have hq : ((1 : ℝ) / 2) ^ 2 = 1 / 4 := by norm_num
  linarith [hq]

/-- The printed hyperlinear notion gives the corpus one: printed models on
`F ∪ F⁻¹ ∪ F⁻¹F ∪ {1}` separate distinct elements of `F` by squared distance `δ² / 8`, and
`isHyperlinear_of_isHyperlinearWeak` amplifies. -/
theorem isHyperlinear_of_printedIsHyperlinear (hG : PrintedIsHyperlinear G) :
    IsHyperlinear G := by
  classical
  obtain ⟨δ, hδ, hmodels⟩ := hG
  refine isHyperlinear_of_isHyperlinearWeak (delta := δ ^ 2 / 8)
    (div_pos (pow_pos hδ 2) (by norm_num)) ?_
  intro F ε hε
  have hF' : ∃ F' : Finset G, (1 : G) ∈ F' ∧ (∀ g ∈ F, g ∈ F') ∧ (∀ h ∈ F, h⁻¹ ∈ F') ∧
      ∀ g ∈ F, ∀ h ∈ F, h⁻¹ * g ∈ F' :=
    ⟨insert 1 (F ∪ F.image (fun a : G => a⁻¹) ∪ Finset.image₂ (fun a b : G => a⁻¹ * b) F F),
      Finset.mem_insert_self _ _,
      fun g hg => Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _ hg)),
      fun h hh => Finset.mem_insert_of_mem (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_image_of_mem (fun a : G => a⁻¹) hh))),
      fun g hg h hh => Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Finset.mem_image₂_of_mem (f := fun a b : G => a⁻¹ * b) hh hg))⟩
  obtain ⟨F', h1F, hFF, hinvF, hdivF⟩ := hF'
  obtain ⟨η, hη0, hη1, hηε, hηδ⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ η ≤ ε ∧ η ≤ δ / 6 :=
    ⟨min 1 (min ε (δ / 6)), lt_min one_pos (lt_min hε (div_pos hδ (by norm_num))),
      min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans (min_le_right _ _)⟩
  obtain ⟨Y, ψ, hY, hunit, hmul, hsep⟩ := hmodels F' η hη0
  have hmulSq : ∀ g ∈ F', ∀ h ∈ F', hsDistSq Y (ψ (g * h)) (ψ g * ψ h) ≤ η ^ 2 :=
    fun g hg h hh => (Real.sqrt_le_left hη0.le).mp (hmul g hg h hh)
  have hsepSq : ∀ g ∈ F', g ≠ 1 → δ ^ 2 ≤ hsDistSq Y (ψ g) 1 :=
    fun g hg hg1 => (Real.le_sqrt' hδ).mp (hsep g hg hg1)
  have hηsq : η ^ 2 ≤ η := by nlinarith
  have hmulW : ∀ g ∈ F, ∀ h ∈ F, hsDistSq Y (ψ (g * h)) (ψ g * ψ h) ≤ ε :=
    fun g hg h hh => (hmulSq g (hFF g hg) h (hFF h hh)).trans (hηsq.trans hηε)
  -- `ψ 1` is close to `1`.
  have hone : hsDistSq Y (ψ 1) 1 ≤ η ^ 2 := by
    have m3 := hmulSq 1 h1F 1 h1F
    rw [mul_one] at m3
    have e1 := hsDistSq_mul_left_unitary Y (hunit 1) hY 1 (ψ 1)
    rw [mul_one] at e1
    have c1 := GroupApproximation.KazhdanCompressorCorner.hsDistSq_comm Y (ψ 1) 1
    linarith
  have hsepW : ∀ g ∈ F, ∀ h ∈ F, g ≠ h → δ ^ 2 / 8 ≤ hsDistSq Y (ψ g) (ψ h) := by
    intro g hg h hh hne
    have hne' : h⁻¹ * g ≠ 1 := fun heq => hne (inv_mul_eq_one.mp heq).symm
    have s1 := hsepSq (h⁻¹ * g) (hdivF g hg h hh) hne'
    have m1 := hmulSq h⁻¹ (hinvF h hh) g (hFF g hg)
    have m2 := hmulSq h⁻¹ (hinvF h hh) h (hFF h hh)
    rw [inv_mul_cancel] at m2
    have t1 := GroupApproximation.KazhdanCompressorCorner.hsDistSq_le_two_add_two Y
      (ψ (h⁻¹ * g)) 1 (ψ h⁻¹ * ψ g)
    have t2 := GroupApproximation.KazhdanCompressorCorner.hsDistSq_le_two_add_two Y
      (ψ h⁻¹ * ψ g) 1 (ψ h⁻¹ * ψ h)
    have t3 := GroupApproximation.KazhdanCompressorCorner.hsDistSq_le_two_add_two Y
      (ψ h⁻¹ * ψ h) 1 (ψ 1)
    have c2 := GroupApproximation.KazhdanCompressorCorner.hsDistSq_comm Y (ψ 1) (ψ h⁻¹ * ψ h)
    have e2 := hsDistSq_mul_left_unitary Y (hunit h⁻¹) hY (ψ g) (ψ h)
    have hsq : η ^ 2 ≤ (δ / 6) ^ 2 := pow_le_pow_left₀ hη0.le hηδ 2
    have hsq' : (δ / 6) ^ 2 = δ ^ 2 / 36 := by ring
    linarith
  exact ⟨{ carrier := Y, nonempty := hY, map := ψ, isUnitary := hunit, multiplicative := hmulW,
    separated := hsepW }⟩

/-- **tex l.105–109, hyperlinear.** The printed definition of hyperlinear groups is the corpus
notion. -/
theorem printedIsHyperlinear_iff : PrintedIsHyperlinear G ↔ IsHyperlinear G :=
  ⟨isHyperlinear_of_printedIsHyperlinear, printedIsHyperlinear_of_isHyperlinear⟩

end GroupApproximation.Full.SK01

#audit_axioms GroupApproximation.Full.SK01.printedIsHyperlinear_iff
