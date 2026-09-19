import GroupApproximation.Sofic.HyperlinearUltraproduct
import GroupApproximation.Sofic.HyperlinearAmplification
import GroupApproximation.Meta.AxiomGuard

/-!
# Trace-preserving unitary matrix models of hyperlinear groups

Statement module of lane `oa-mcduff` (absorbed from oa-ozawa71) for `simple_kazhdan_sofic_group.tex`
at origin/main 37551fd93, "Brown's formulation", tex 276–278 (census row `fc6e6384121b`): "So `L(G)`
embeds in `𝓡^ω` [Kirchberg, Radulescu], [Ozawa, Proposition 7.1]".  The first step of that proposition
turns separated unitary models into models whose normalized traces converge to the canonical trace
`δ_{g,1}`.  Lane oa-llp consumes the same models for "`C*(G)` does not have the local lifting property".

* `TracePreservingMatrixModel G`: exact unitaries `map n g ∈ U(model n)`, asymptotically multiplicative
  in normalized Hilbert–Schmidt distance (`AsymptoticUnitaryRepresentation`), with
  `normTrace (map n 1) → 1` and `normTrace (map n g) → 0` for `g ≠ 1`.
* `HasTracePreservingMatrixModel G`: such a model exists.
* `HyperlinearTracePreservingModelStatement`: every countable hyperlinear group has one.  The proof,
  by amplifying separated models `V = (1 ⊕ u)^{⊗a} ⊗ (1 ⊕ ū)^{⊗a}`, is the next module's work.
-/

namespace GroupApproximation

open Filter Matrix

universe u

/-- **A trace-preserving unitary matrix model** of `G`: exact unitaries in finite models, asymptotically
multiplicative in normalized Hilbert–Schmidt distance, whose normalized traces converge to the
canonical trace `δ_{g,1}`. -/
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

/-- **Countable hyperlinear groups have trace-preserving unitary matrix models**: the matrix half of
Ozawa's Proposition 7.1.  Stated here; the amplification proof is the next module's work. -/
def HyperlinearTracePreservingModelStatement : Prop :=
  ∀ (G : Type u) [Group G] [Countable G], IsHyperlinear G → HasTracePreservingMatrixModel G

end GroupApproximation
import GroupApproximation.Analysis.HyperlinearTraceVanishingModels
import GroupApproximation.Analysis.HyperlinearOneSumModels
import Mathlib.Analysis.SpecificLimits.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Countable hyperlinear groups have trace-preserving unitary matrix models

Lane `oa-mcduff` (absorbed from oa-ozawa71) for `simple_kazhdan_sofic_group.tex` at origin/main 37551fd93,
"Brown's formulation", tex 276–278 (census row `fc6e6384121b`): "So `L(G)` embeds in `𝓡^ω`
[Kirchberg, Radulescu], [Ozawa, Proposition 7.1]".  This module proves the matrix half of that
proposition, `HyperlinearTracePreservingModelStatement` (`Analysis/HyperlinearTraceVanishingModels`),
which lane oa-llp also consumes.

For an enumeration `e` of `G`, the `n`-th stage takes a hyperlinear model `u` of `G` on
`F_n = {1} ∪ e({0, …, n})` at accuracy `1/(n+1)²` and amplifies it to
`W_g = ((1 ⊕ u_g) ⊗ conj (1 ⊕ u_g))^{⊗n}` (`Analysis/HyperlinearOneSumModels`):
* the defects are multiplied by at most `n`, so they are at most `n/(n+1)² ≤ 1/(n+1)`;
* `τ(W_g) = |(1 + τ(u_g))/2|^{2n}`;
* separation `2 − ε ≤ ‖u_g − u_1‖₂²` and `‖u_1 − 1‖₂² ≤ ε` give `Re τ(u_g) ≤ (2 + 3ε)/4`, so for
  `g ≠ 1`, `τ(W_g) ≤ (7/8)^n → 0`;
* `‖u_1 − 1‖₂² ≤ ε` gives `τ(W_1) ≥ (1 − ε/4)^{2n} ≥ 1 − 1/(n+1) → 1`.
-/

namespace GroupApproximation
namespace HyperlinearTraceVanishing

open Filter Matrix

noncomputable section

universe u

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
  rw [hsDistSq, hsDistSq]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [show A i j - C i j = -(C i j - A i j) by ring, Complex.normSq_neg]

theorem re_normTrace_eq_of_unitary {Y : FiniteModel} (hY : 0 < Fintype.card Y)
    {A : Matrix Y Y ℂ} (hA : A ∈ Matrix.unitaryGroup Y ℂ) :
    (normTrace Y A).re = 1 - hsDistSq Y A 1 / 2 := by
  have h := hsDistSq_of_unitary Y hA (one_mem (Matrix.unitaryGroup Y ℂ)) hY
  rw [Matrix.conjTranspose_one, mul_one] at h
  linarith

/-- In a model multiplicative at `(1,1)`, the model of `1` is close to `1`. -/
theorem hsDistSq_map_one_le {G : Type u} [Group G] {F : Finset G} {ε : ℝ}
    (M : HyperlinearModel G F ε) (h1 : (1 : G) ∈ F) :
    hsDistSq M.carrier (M.map 1) 1 ≤ ε := by
  have hm := M.multiplicative 1 h1 1 h1
  rw [mul_one] at hm
  have hinv := hsDistSq_mul_left_of_unitary (M.isUnitary 1) M.nonempty (M.map 1) 1
  rw [mul_one] at hinv
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
  have h := one_div_succ_le_one n
  calc (1 / ((n : ℝ) + 1)) ^ 2 ≤ 1 ^ 2 := by gcongr
    _ = 1 := one_pow 2

theorem accuracy_le_quarter {n : ℕ} (hn : 1 ≤ n) : accuracy n ≤ 1 / 4 := by
  unfold accuracy
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h : 1 / ((n : ℝ) + 1) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  calc (1 / ((n : ℝ) + 1)) ^ 2 ≤ (1 / 2) ^ 2 := by gcongr
    _ = 1 / 4 := by norm_num

theorem natCast_mul_accuracy_le (n : ℕ) : (n : ℝ) * accuracy n ≤ 1 / ((n : ℝ) + 1) := by
  unfold accuracy
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 : (n : ℝ) * (1 / ((n : ℝ) + 1)) ≤ 1 := by
    rw [mul_one_div, div_le_one hpos]
    linarith
  calc (n : ℝ) * (1 / ((n : ℝ) + 1)) ^ 2
      = ((n : ℝ) * (1 / ((n : ℝ) + 1))) * (1 / ((n : ℝ) + 1)) := by ring
    _ ≤ 1 * (1 / ((n : ℝ) + 1)) := by gcongr
    _ = 1 / ((n : ℝ) + 1) := one_mul _

theorem one_div_succ_le_of_lt {δ : ℝ} (hδ : 0 < δ) {N n : ℕ} (hN : 1 / δ < N) (hn : N ≤ n) :
    1 / ((n : ℝ) + 1) ≤ δ := by
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h : 1 / δ < (n : ℝ) + 1 := by linarith
  rw [div_le_iff₀ (by positivity)]
  rw [div_lt_iff₀ hδ] at h
  linarith

/-! ## The construction -/

/-- **Every countable hyperlinear group has a trace-preserving unitary matrix model.** -/
theorem hyperlinearTracePreservingModelStatement_holds :
    HyperlinearTracePreservingModelStatement.{u} := by
  intro G _ _ hG
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat G
  set F : ℕ → Finset G := fun n ↦ insert 1 ((Finset.range (n + 1)).image e)
  have hFmono : ∀ {m n : ℕ}, m ≤ n → F m ⊆ F n := by
    intro m n hmn
    refine Finset.insert_subset_insert _ (Finset.image_subset_image ?_)
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have hFmem : ∀ g : G, ∃ N, ∀ n ≥ N, g ∈ F n := by
    intro g
    obtain ⟨i, hi⟩ := he g
    refine ⟨i, fun n hn ↦ hFmono hn ?_⟩
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.self_mem_range_succ i, hi⟩)
  have h1F : ∀ n, (1 : G) ∈ F n := fun n ↦ Finset.mem_insert_self _ _
  set M : ∀ n : ℕ, HyperlinearModel G (F n) (accuracy n) :=
    fun n ↦ (hG (F n) (accuracy n) (accuracy_pos n)).some
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
    obtain ⟨Ne, hNe⟩ := exists_nat_gt (1 / δ)
    refine ⟨max (max Ng Nh) Ne, fun n hn ↦ ?_⟩
    have hg : g ∈ F n := hNg n (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn)
    have hg' : g' ∈ F n := hNh n (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn)
    have hd := (M n).multiplicative g hg g' hg'
    have hprod : (M n).map g * (M n).map g' ∈ Matrix.unitaryGroup (M n).carrier ℂ :=
      mul_mem ((M n).isUnitary g) ((M n).isUnitary g')
    have hacc := accuracy_le_one n
    have hle := hsDistSq_ampMatrix_le (hY n) ((M n).isUnitary (g * g')) hprod n (by linarith)
    change hsDistSq (ampModel (M n).carrier n) (ampMatrix ((M n).map (g * g')) n)
      (ampMatrix ((M n).map g) n * ampMatrix ((M n).map g') n) ≤ δ
    rw [ampMatrix_mul]
    calc hsDistSq (ampModel (M n).carrier n) (ampMatrix ((M n).map (g * g')) n)
          (ampMatrix ((M n).map g * (M n).map g') n)
        ≤ (n : ℝ) * hsDistSq (M n).carrier ((M n).map (g * g')) ((M n).map g * (M n).map g') :=
          hle
      _ ≤ (n : ℝ) * accuracy n := by gcongr
      _ ≤ 1 / ((n : ℝ) + 1) := natCast_mul_accuracy_le n
      _ ≤ δ := one_div_succ_le_of_lt hδ hNe (le_trans (le_max_right _ _) hn)
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
      · have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        have h1 := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).sub h0
        simpa using h1
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
        have hbase : (1 - accuracy n / 4) ^ 2 ≤
            Complex.normSq ((1 + normTrace (M n).carrier ((M n).map 1)) / 2) :=
          le_trans (pow_le_pow_left₀ (by linarith) (by linarith) 2) hlow
        have hpow : (1 - accuracy n / 4) ^ (2 * n) ≤
            Complex.normSq ((1 + normTrace (M n).carrier ((M n).map 1)) / 2) ^ n := by
          rw [pow_mul]
          exact pow_le_pow_left₀ (sq_nonneg _) hbase n
        have hbern : 1 + ((2 * n : ℕ) : ℝ) * (-(accuracy n / 4)) ≤
            (1 + -(accuracy n / 4)) ^ (2 * n) :=
          one_add_mul_le_pow (by linarith) (2 * n)
        rw [show (1 + -(accuracy n / 4)) = 1 - accuracy n / 4 by ring] at hbern
        push_cast at hbern
        linarith
      · intro n
        show Complex.normSq ((1 + normTrace (M n).carrier ((M n).map 1)) / 2) ^ n ≤ 1
        have hz1 := normSq_normTrace_le_one (M n).carrier ((M n).isUnitary 1) (hY n)
        have hup := normSq_half_one_add_le hz1
        have hre1 := re_le_one_of_normSq_le_one hz1
        exact pow_le_one₀ (Complex.normSq_nonneg _) (by linarith)
    rw [hform]
    have hc := (Complex.continuous_ofReal.tendsto 1).comp hreal
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
        have hsep := (M n).separated g hg 1 (h1F n) hg1
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
    have hc := (Complex.continuous_ofReal.tendsto 0).comp hreal
    rw [Complex.ofReal_zero] at hc
    exact hc

end

end HyperlinearTraceVanishing
end GroupApproximation

#audit_closed_axioms GroupApproximation.HyperlinearTraceVanishing.hyperlinearTracePreservingModelStatement_holds
