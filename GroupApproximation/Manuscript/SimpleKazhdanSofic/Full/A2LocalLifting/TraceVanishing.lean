import GroupApproximation.Sofic.HyperlinearUltraproduct
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2LocalLifting.OneSum
import Mathlib.Analysis.SpecificLimits.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Countable hyperlinear groups have trace-preserving matrix models (table row A2)

`simple_kazhdan_sofic_group.tex`, Introduction, tex l.54–59 (table row A2): Ozawa's remark that the
full C⋆-algebra of an infinite simple hyperlinear Kazhdan group has no local lifting property
starts from unitary matrix models whose normalized traces converge to the canonical trace
(Ozawa, *About the QWEP conjecture*, Internat. J. Math. **15** (2004), Proposition 7.1, first step).

* `TracePreservingMatrixModel G`: exact unitaries, asymptotically multiplicative in normalized
  Hilbert–Schmidt distance, with `τ(map n 1) → 1` and `τ(map n g) → 0` for `g ≠ 1`.
* `hasTracePreservingMatrixModel_of_isHyperlinear`: every countable hyperlinear group has one.

For an enumeration `e` of `G`, stage `n` takes a hyperlinear model `u` on
`F_n = {1} ∪ e({0, …, n})` at accuracy `1/(n+1)²` and amplifies it to
`W_g = ((1 ⊕ u_g) ⊗ conj (1 ⊕ u_g))^{⊗n}` (`OneSum.lean`):
* defects are multiplied by at most `n`, so they are at most `1/(n+1)`;
* `τ(W_g) = |(1 + τ(u_g))/2|^{2n}`;
* for `g ≠ 1`, separation gives `τ(W_g) ≤ (7/8)^n`;
* `‖u_1 − 1‖₂² ≤ 1/(n+1)²` gives `τ(W_1) ≥ 1 − 1/(n+1)`.

This is a fork, into lane `A2LocalLifting`, of the never-wired modules
`Analysis/HyperlinearTraceVanishingModels.lean` and `Analysis/HyperlinearTraceVanishingProof.lean`
(left untouched).
-/

namespace GroupApproximation
namespace Full
namespace A2LocalLifting

open Filter
open scoped Matrix

noncomputable section

universe u

/-- **A trace-preserving unitary matrix model** of `G` (Ozawa, Proposition 7.1, first step; row A2,
tex l.54–59): exact unitaries in finite models, asymptotically multiplicative in normalized
Hilbert–Schmidt distance, whose normalized traces converge to the canonical trace `δ_{g,1}`. -/
structure TracePreservingMatrixModel (G : Type u) [Group G] extends
    AsymptoticUnitaryRepresentation G where
  /-- The normalized traces of the models of `1` tend to `1`. -/
  trace_tendsto_one :
    Tendsto (fun n ↦ normTrace (model n) (map n 1 : Matrix (model n) (model n) ℂ)) atTop (nhds 1)
  /-- The normalized traces of the models of `g ≠ 1` tend to `0`. -/
  trace_tendsto_ne : ∀ g : G, g ≠ 1 →
    Tendsto (fun n ↦ normTrace (model n) (map n g : Matrix (model n) (model n) ℂ)) atTop (nhds 0)

/-- `G` has a trace-preserving unitary matrix model. -/
def HasTracePreservingMatrixModel (G : Type u) [Group G] : Prop :=
  Nonempty (TracePreservingMatrixModel G)

/-! ## Hilbert–Schmidt facts -/

theorem hsDistSq_mul_left_of_unitary {Y : FiniteModel} {V : Matrix Y Y ℂ}
    (hV : V ∈ Matrix.unitaryGroup Y ℂ) (hY : 0 < Fintype.card Y) (A B : Matrix Y Y ℂ) :
    hsDistSq Y (V * A) (V * B) = hsDistSq Y A B := by
  change hsNormSq Y (V * A - V * B) = hsNormSq Y (A - B)
  rw [← Matrix.mul_sub, hsNormSq_mul_left Y hV hY]

theorem hsDistSq_le_two_mul_add (Y : FiniteModel) (A C M : Matrix Y Y ℂ) :
    hsDistSq Y A C ≤ 2 * hsDistSq Y A M + 2 * hsDistSq Y M C := by
  change hsNormSq Y (A - C) ≤ 2 * hsNormSq Y (A - M) + 2 * hsNormSq Y (M - C)
  rw [show A - C = (A - M) + (M - C) by abel]
  exact hsNormSq_add_le Y _ _

theorem hsDistSq_symm (Y : FiniteModel) (A C : Matrix Y Y ℂ) :
    hsDistSq Y A C = hsDistSq Y C A := by
  unfold hsDistSq
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [show A i j - C i j = -(C i j - A i j) by ring, Complex.normSq_neg]

theorem re_normTrace_eq_of_unitary {Y : FiniteModel} (hY : 0 < Fintype.card Y)
    {A : Matrix Y Y ℂ} (hA : A ∈ Matrix.unitaryGroup Y ℂ) :
    (normTrace Y A).re = 1 - hsDistSq Y A 1 / 2 := by
  have h := hsDistSq_of_unitary Y hA (one_mem (Matrix.unitaryGroup Y ℂ)) hY
  rw [Matrix.conjTranspose_one, Matrix.mul_one] at h
  linarith

/-- In a model multiplicative at `(1, 1)`, the model of `1` is close to `1`. -/
theorem hsDistSq_map_one_le {G : Type u} [Group G] {F : Finset G} {ε : ℝ}
    (M : HyperlinearModel G F ε) (h1 : (1 : G) ∈ F) :
    hsDistSq M.carrier (M.map 1) 1 ≤ ε := by
  have hm : hsDistSq M.carrier (M.map (1 * 1)) (M.map 1 * M.map 1) ≤ ε :=
    M.multiplicative 1 h1 1 h1
  rw [_root_.mul_one] at hm
  have hinv : hsDistSq M.carrier (M.map 1 * M.map 1) (M.map 1 * 1) =
      hsDistSq M.carrier (M.map 1) 1 :=
    hsDistSq_mul_left_of_unitary (M.isUnitary 1) M.nonempty (M.map 1) 1
  rw [Matrix.mul_one] at hinv
  rw [← hinv, hsDistSq_symm]
  exact hm

/-! ## The accuracies -/

/-- The accuracy `1/(n+1)²` of the `n`-th stage. -/
def accuracy (n : ℕ) : ℝ := (1 / ((n : ℝ) + 1)) ^ 2

theorem accuracy_pos (n : ℕ) : 0 < accuracy n := by
  unfold accuracy
  positivity

theorem one_div_succ_le_one (n : ℕ) : 1 / ((n : ℝ) + 1) ≤ 1 := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [div_le_one hpos]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem accuracy_le_one (n : ℕ) : accuracy n ≤ 1 := by
  unfold accuracy
  exact pow_le_one₀ (by positivity) (one_div_succ_le_one n)

theorem accuracy_le_quarter {n : ℕ} (hn : 1 ≤ n) : accuracy n ≤ 1 / 4 := by
  unfold accuracy
  have hn' : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn
  have h : 1 / ((n : ℝ) + 1) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  calc (1 / ((n : ℝ) + 1)) ^ 2 ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ (by positivity) h 2
    _ = 1 / 4 := by norm_num

theorem natCast_mul_accuracy_le (n : ℕ) : (n : ℝ) * accuracy n ≤ 1 / ((n : ℝ) + 1) := by
  unfold accuracy
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hpos' : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
  have h1 : (n : ℝ) * (1 / ((n : ℝ) + 1)) ≤ 1 := by
    rw [mul_one_div, div_le_one hpos]
    linarith
  calc (n : ℝ) * (1 / ((n : ℝ) + 1)) ^ 2
      = ((n : ℝ) * (1 / ((n : ℝ) + 1))) * (1 / ((n : ℝ) + 1)) := by ring
    _ ≤ 1 * (1 / ((n : ℝ) + 1)) := mul_le_mul_of_nonneg_right h1 hpos'
    _ = 1 / ((n : ℝ) + 1) := one_mul _

theorem one_div_succ_le_of_lt {δ : ℝ} (hδ : 0 < δ) {N n : ℕ} (hN : 1 / δ < N) (hn : N ≤ n) :
    1 / ((n : ℝ) + 1) ≤ δ := by
  have hNn : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h : 1 / δ < (n : ℝ) + 1 := by linarith
  rw [div_le_iff₀ hpos]
  rw [div_lt_iff₀ hδ] at h
  linarith

/-! ## The construction -/

/-- **Every countable hyperlinear group has a trace-preserving unitary matrix model** (Ozawa,
Proposition 7.1, first step; row A2, tex l.54–59). -/
theorem hasTracePreservingMatrixModel_of_isHyperlinear (G : Type u) [Group G] [Countable G]
    (hG : IsHyperlinear G) : HasTracePreservingMatrixModel G := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat G
  let F : ℕ → Finset G := fun n ↦ insert 1 ((Finset.range (n + 1)).image e)
  have hFmono : ∀ {m n : ℕ}, m ≤ n → F m ⊆ F n := by
    intro m n hmn
    refine Finset.insert_subset_insert _ (Finset.image_subset_image ?_)
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  have hFmem : ∀ g : G, ∃ N, ∀ n ≥ N, g ∈ F n := by
    intro g
    obtain ⟨i, hi⟩ := he g
    refine ⟨i, fun n hn ↦ hFmono hn ?_⟩
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.self_mem_range_succ i, hi⟩)
  have h1F : ∀ n, (1 : G) ∈ F n := fun n ↦ Finset.mem_insert_self _ _
  let M : ∀ n : ℕ, HyperlinearModel G (F n) (accuracy n) :=
    fun n ↦ Classical.choice (hG (F n) (accuracy n) (accuracy_pos n))
  have hY : ∀ n, 0 < Fintype.card (M n).carrier := fun n ↦ (M n).nonempty
  refine ⟨{
    model := fun n ↦ ampModel (M n).carrier n
    modelNonempty := fun n ↦ card_ampModel_pos (hY n) n
    map := fun n g ↦
      ⟨ampMatrix ((M n).map g) n, ampMatrix_mem_unitaryGroup ((M n).isUnitary g) n⟩
    asymptoticallyMultiplicative := ?_
    trace_tendsto_one := ?_
    trace_tendsto_ne := ?_ }⟩
  · intro g g' δ hδ
    obtain ⟨Ng, hNg⟩ := hFmem g
    obtain ⟨Nh, hNh⟩ := hFmem g'
    obtain ⟨Nδ, hNδ⟩ := exists_nat_gt (1 / δ)
    refine ⟨max (max Ng Nh) Nδ, fun n hn ↦ ?_⟩
    have hg : g ∈ F n := hNg n (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn)
    have hg' : g' ∈ F n := hNh n (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn)
    have hd : hsDistSq (M n).carrier ((M n).map (g * g')) ((M n).map g * (M n).map g') ≤
        accuracy n := (M n).multiplicative g hg g' hg'
    have hprod : (M n).map g * (M n).map g' ∈ Matrix.unitaryGroup (M n).carrier ℂ :=
      mul_mem ((M n).isUnitary g) ((M n).isUnitary g')
    have hacc := accuracy_le_one n
    have hd8 : hsDistSq (M n).carrier ((M n).map (g * g')) ((M n).map g * (M n).map g') ≤ 8 := by
      linarith
    have hle := hsDistSq_ampMatrix_le (hY n) ((M n).isUnitary (g * g')) hprod n hd8
    change hsDistSq (ampModel (M n).carrier n) (ampMatrix ((M n).map (g * g')) n)
      (ampMatrix ((M n).map g) n * ampMatrix ((M n).map g') n) ≤ δ
    rw [ampMatrix_mul]
    calc hsDistSq (ampModel (M n).carrier n) (ampMatrix ((M n).map (g * g')) n)
          (ampMatrix ((M n).map g * (M n).map g') n)
        ≤ (n : ℝ) * hsDistSq (M n).carrier ((M n).map (g * g')) ((M n).map g * (M n).map g') :=
          hle
      _ ≤ (n : ℝ) * accuracy n := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg n)
      _ ≤ 1 / ((n : ℝ) + 1) := natCast_mul_accuracy_le n
      _ ≤ δ := one_div_succ_le_of_lt hδ hNδ (le_trans (le_max_right _ _) hn)
  · change Tendsto (fun n ↦ normTrace (ampModel (M n).carrier n) (ampMatrix ((M n).map 1) n))
      atTop (nhds 1)
    have hform : (fun n ↦ normTrace (ampModel (M n).carrier n) (ampMatrix ((M n).map 1) n)) =
        fun n ↦ ((Complex.normSq ((1 + normTrace (M n).carrier ((M n).map 1)) / 2) ^ n : ℝ) : ℂ) :=
      funext fun n ↦ normTrace_ampMatrix (hY n) _ n
    have hreal : Tendsto
        (fun n ↦ Complex.normSq ((1 + normTrace (M n).carrier ((M n).map 1)) / 2) ^ n)
        atTop (nhds 1) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le
        (g := fun n : ℕ ↦ 1 - 1 / ((n : ℝ) + 1)) (h := fun _ : ℕ ↦ (1 : ℝ)) ?_
        tendsto_const_nhds ?_ ?_
      · have h0 : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have h1 : Tendsto (fun n : ℕ ↦ 1 - 1 / ((n : ℝ) + 1)) atTop (nhds (1 - 0)) :=
          (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).sub h0
        rw [sub_zero] at h1
        exact h1
      · intro n
        show 1 - 1 / ((n : ℝ) + 1) ≤
          Complex.normSq ((1 + normTrace (M n).carrier ((M n).map 1)) / 2) ^ n
        have hre := re_normTrace_eq_of_unitary (hY n) ((M n).isUnitary 1)
        have hclose := hsDistSq_map_one_le (M n) (h1F n)
        have hacc := accuracy_le_one n
        have hq := natCast_mul_accuracy_le n
        have hpos : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
        have hlow := sq_le_normSq_half_one_add (normTrace (M n).carrier ((M n).map 1))
        rw [hre] at hlow
        have hnn : (0 : ℝ) ≤ 1 - accuracy n / 4 := by linarith
        have hmid : 1 - accuracy n / 4 ≤
            (1 + (1 - hsDistSq (M n).carrier ((M n).map 1) 1 / 2)) / 2 := by linarith
        have hbase : (1 - accuracy n / 4) ^ 2 ≤
            Complex.normSq ((1 + normTrace (M n).carrier ((M n).map 1)) / 2) :=
          le_trans (pow_le_pow_left₀ hnn hmid 2) hlow
        have hpow : (1 - accuracy n / 4) ^ (2 * n) ≤
            Complex.normSq ((1 + normTrace (M n).carrier ((M n).map 1)) / 2) ^ n := by
          rw [pow_mul]
          exact pow_le_pow_left₀ (sq_nonneg _) hbase n
        have hbern : 1 + ((2 * n : ℕ) : ℝ) * (-(accuracy n / 4)) ≤
            (1 + -(accuracy n / 4)) ^ (2 * n) :=
          one_add_mul_le_pow (by linarith) (2 * n)
        rw [show (1 + -(accuracy n / 4)) = 1 - accuracy n / 4 by ring, Nat.cast_mul,
          Nat.cast_ofNat] at hbern
        linarith
      · intro n
        show Complex.normSq ((1 + normTrace (M n).carrier ((M n).map 1)) / 2) ^ n ≤ 1
        have hz1 := normSq_normTrace_le_one (M n).carrier ((M n).isUnitary 1) (hY n)
        have hup := normSq_half_one_add_le hz1
        have hre1 := re_le_one_of_normSq_le_one hz1
        have hle1 : Complex.normSq ((1 + normTrace (M n).carrier ((M n).map 1)) / 2) ≤ 1 := by
          linarith
        exact pow_le_one₀ (Complex.normSq_nonneg _) hle1
    rw [hform]
    have hc : Tendsto
        (fun n ↦ ((Complex.normSq ((1 + normTrace (M n).carrier ((M n).map 1)) / 2) ^ n : ℝ) : ℂ))
        atTop (nhds ((1 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 1).comp hreal
    rw [Complex.ofReal_one] at hc
    exact hc
  · intro g hg1
    change Tendsto (fun n ↦ normTrace (ampModel (M n).carrier n) (ampMatrix ((M n).map g) n))
      atTop (nhds 0)
    have hform : (fun n ↦ normTrace (ampModel (M n).carrier n) (ampMatrix ((M n).map g) n)) =
        fun n ↦ ((Complex.normSq ((1 + normTrace (M n).carrier ((M n).map g)) / 2) ^ n : ℝ) : ℂ) :=
      funext fun n ↦ normTrace_ampMatrix (hY n) _ n
    obtain ⟨Ng, hNg⟩ := hFmem g
    have hreal : Tendsto
        (fun n ↦ Complex.normSq ((1 + normTrace (M n).carrier ((M n).map g)) / 2) ^ n)
        atTop (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℕ ↦ (0 : ℝ))
        (h := fun n : ℕ ↦ (7 / 8 : ℝ) ^ n) tendsto_const_nhds
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)) ?_ ?_
      · exact Filter.Eventually.of_forall fun n ↦ pow_nonneg (Complex.normSq_nonneg _) n
      · refine Filter.eventually_atTop.mpr ⟨max Ng 1, fun n hn ↦ ?_⟩
        show Complex.normSq ((1 + normTrace (M n).carrier ((M n).map g)) / 2) ^ n ≤ (7 / 8) ^ n
        have hg : g ∈ F n := hNg n (le_trans (le_max_left _ _) hn)
        have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
        have hsep : 2 - accuracy n ≤ hsDistSq (M n).carrier ((M n).map g) ((M n).map 1) :=
          (M n).separated g hg 1 (h1F n) hg1
        have hclose := hsDistSq_map_one_le (M n) (h1F n)
        have htri := hsDistSq_le_two_mul_add (M n).carrier ((M n).map g) ((M n).map 1) 1
        rw [hsDistSq_symm (M n).carrier 1 ((M n).map 1)] at htri
        have hre := re_normTrace_eq_of_unitary (hY n) ((M n).isUnitary g)
        have hz1 := normSq_normTrace_le_one (M n).carrier ((M n).isUnitary g) (hY n)
        have hup := normSq_half_one_add_le hz1
        have hacc := accuracy_le_quarter hn1
        have hr : Complex.normSq ((1 + normTrace (M n).carrier ((M n).map g)) / 2) ≤ 7 / 8 := by
          linarith
        exact pow_le_pow_left₀ (Complex.normSq_nonneg _) hr n
    rw [hform]
    have hc : Tendsto
        (fun n ↦ ((Complex.normSq ((1 + normTrace (M n).carrier ((M n).map g)) / 2) ^ n : ℝ) : ℂ))
        atTop (nhds ((0 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp hreal
    rw [Complex.ofReal_zero] at hc
    exact hc

end

end A2LocalLifting
end Full
end GroupApproximation

open GroupApproximation.Full.A2LocalLifting

#audit_closed_axioms hasTracePreservingMatrixModel_of_isHyperlinear
