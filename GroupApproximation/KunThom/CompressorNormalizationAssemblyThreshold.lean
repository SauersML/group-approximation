import GroupApproximation.KunThom.CompressorNormalizationAssemblyFrame

/-!
# The joint scale choice

Kun--Thom (arXiv:2608.06222v3, proof of Lemma 4.2) choose the cluster threshold
`ε_n` so slowly that a prescribed finite family of error sequences is
`o(ε_n)`.  `exists_joint_pairRepair` supplies a vanishing threshold `h` with
`ρ' ≤ h` eventually, for any prescribed vanishing `ρ'`.  Prescribing
`ρ' = √ρ` turns this into `ρ = o(h)`.

* `vanishing_of_tendsto`, `tendsto_of_vanishing`: `Vanishing` is convergence to
  `0` along `atTop`.
* `vanishing_sqrt`: the square root of a nonnegative vanishing sequence
  vanishes.
* `vanishing_div_of_sqrt_le`: if `√ρ ≤ h` eventually, then `ρ / h` vanishes.
* `exists_clusterFrame`: for retained components with a Kazhdan pair inside the
  generators, and any nonnegative vanishing `ρ`, there is a cluster frame whose
  threshold is positive, vanishes, and dominates `ρ` in the form
  `Vanishing (ρ / threshold)`.  This discharges `hframe` of
  `seqNormalizes_of_compressor_of_steps`.
-/

namespace GroupApproximation
namespace CompressorNormalizationAssembly

open Filter
open scoped Topology
open CentralizerNormalizationImprove

theorem vanishing_of_tendsto {a : ℕ → ℝ} (h : Tendsto a atTop (𝓝 0)) :
    Vanishing a := by
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  have hd := hN n hn
  rwa [Real.dist_eq, sub_zero] at hd

theorem tendsto_of_vanishing {a : ℕ → ℝ} (h : Vanishing a) : Tendsto a atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [Real.dist_eq, sub_zero]
  exact hN n hn

/-- The square root of a nonnegative vanishing sequence vanishes. -/
theorem vanishing_sqrt {a : ℕ → ℝ} (ha0 : ∀ n, 0 ≤ a n) (ha : Vanishing a) :
    Vanishing fun n ↦ Real.sqrt (a n) := by
  intro ε hε
  obtain ⟨N, hN⟩ := ha ((ε / 2) ^ 2) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  have h₁ := hN n hn
  rw [abs_of_nonneg (ha0 n)] at h₁
  have h₂ : Real.sqrt (a n) ≤ ε / 2 := by
    calc Real.sqrt (a n) ≤ Real.sqrt ((ε / 2) ^ 2) := Real.sqrt_le_sqrt h₁.le
      _ = ε / 2 := Real.sqrt_sq (by positivity)
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  linarith

/-- If `√ρ ≤ h` from some index on, then `ρ = o(h)`. -/
theorem vanishing_div_of_sqrt_le {ρ h : ℕ → ℝ} (hρ0 : ∀ n, 0 ≤ ρ n) (hρ : Vanishing ρ)
    (hpos : ∀ n, 0 < h n) (N : ℕ) (hle : ∀ n, N ≤ n → Real.sqrt (ρ n) ≤ h n) :
    Vanishing fun n ↦ ρ n / h n := by
  refine Vanishing.squeeze_eventually (vanishing_sqrt hρ0 hρ) N fun n hn ↦
    ⟨div_nonneg (hρ0 n) (hpos n).le, ?_⟩
  show ρ n / h n ≤ Real.sqrt (ρ n)
  rw [div_le_iff₀ (hpos n)]
  calc ρ n = Real.sqrt (ρ n) * Real.sqrt (ρ n) := (Real.mul_self_sqrt (hρ0 n)).symm
    _ ≤ Real.sqrt (ρ n) * h n := mul_le_mul_of_nonneg_left (hle n hn) (Real.sqrt_nonneg _)

/-- **The joint scale choice.**  For retained components whose generators
contain a Kazhdan pair, a repair factor `K₀ ≥ 4` and a nonnegative vanishing
sequence `ρ`, some cluster frame with repair factor `K₀` has a positive
vanishing threshold `h` with `ρ = o(h)`. -/
theorem exists_clusterFrame {G : Type} [Group G] {A : SoficApproximation G} {K : Type}
    [Group K] {ι : K →* G} (R : RetainedComponents A K ι) {Q : Finset K} {κ : ℝ}
    (hQ : IsKazhdanPair.{0, 0} K Q κ) (hQT : Q ⊆ R.data.generators) (hκone : κ ≤ 1)
    (K₀ : ℝ) (hK₀ : 4 ≤ K₀) (ρ : ℕ → ℝ) (hρ0 : ∀ n, 0 ≤ ρ n) (hρ : Vanishing ρ) :
    ∃ F : ClusterFrame R, F.repairFactor = K₀ ∧ (∀ n, 0 < F.threshold n) ∧
      Vanishing F.threshold ∧ Vanishing fun n ↦ ρ n / F.threshold n := by
  obtain ⟨h, d, hpos, htend, hdtend, hev, N₀, hN₀⟩ :=
    R.data.family.exists_joint_pairRepair K₀ hK₀ hQ hQT R.data.one_mem hκone
      (fun n ↦ Real.sqrt (ρ n)) (tendsto_of_vanishing (vanishing_sqrt hρ0 hρ))
  obtain ⟨N₁, hN₁⟩ := R.data.family.size_tendsTo 360
  have hcap : 0 < min (1 / 100000 : ℝ) R.data.family.cheeger :=
    lt_min (by norm_num) R.data.family.cheeger_pos
  obtain ⟨N₂, hN₂⟩ := vanishing_of_tendsto htend _ hcap
  obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.1 hev
  have heq : ∀ n, N₂ ≤ n → min (h n) (min (1 / 100000) R.data.family.cheeger) = h n :=
    fun n hn ↦ min_eq_left ((le_abs_self _).trans (hN₂ n hn).le)
  have hthrpos : ∀ n, 0 < min (h n) (min (1 / 100000) R.data.family.cheeger) :=
    fun n ↦ lt_min (hpos n) hcap
  obtain ⟨N₄, hN₄⟩ := vanishing_of_tendsto hdtend (1 / 5000) (by norm_num)
  have hdsmall : ∀ n, N₄ ≤ n → d n ≤ 1 / 5000 :=
    fun n hn ↦ (le_abs_self _).trans (hN₄ n hn).le
  have hdvan : Vanishing fun n ↦ min (max (d n) 0) (1 / 5000) := by
    intro ε hε
    obtain ⟨N, hN⟩ := vanishing_of_tendsto hdtend ε hε
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [abs_of_nonneg (le_min (le_max_right _ _) (by norm_num))]
    exact lt_of_le_of_lt ((min_le_left _ _).trans (max_le (le_abs_self _) (abs_nonneg _)))
      (hN n hn)
  refine ⟨{ threshold := fun n ↦ min (h n) (min (1 / 100000) R.data.family.cheeger)
            repairFactor := K₀
            distance := fun n ↦ min (max (d n) 0) (1 / 5000)
            start := max N₀ (max N₁ (max N₂ N₄))
            threshold_pos := hthrpos
            threshold_small := fun n ↦ (min_le_right _ _).trans (min_le_left _ _)
            threshold_cheeger := fun n ↦ (min_le_right _ _).trans (min_le_right _ _)
            distance_nonneg := fun n ↦ le_min (le_max_right _ _) (by norm_num)
            distance_small := fun n ↦ min_le_right _ _
            distance_vanishing := hdvan
            scale_large := ?_
            repair := ?_
            improve := ?_ }, rfl, hthrpos, ?_, ?_⟩
  · intro n hn i
    have hcard := hN₁ n ((le_max_left N₁ _).trans ((le_max_right N₀ _).trans hn)) i
    show 20 ≤ Fintype.card (R.data.family.model n i) / 18
    omega
  · intro n hn
    have hn₂ : N₂ ≤ n := (le_max_left N₂ N₄).trans ((le_max_right N₁ _).trans
      ((le_max_right N₀ _).trans hn))
    have hn₄ : N₄ ≤ n := (le_max_right N₂ N₄).trans ((le_max_right N₁ _).trans
      ((le_max_right N₀ _).trans hn))
    show R.data.family.PairRepairAt K₀ (min (h n) (min (1 / 100000) R.data.family.cheeger))
      (min (max (d n) 0) (1 / 5000)) n
    rw [heq n hn₂]
    exact pairRepairAt_mono_distance (le_min (le_max_left _ _) (hdsmall n hn₄))
      (hN₀ n ((le_max_left N₀ _).trans hn)).1
  · intro n hn
    have hn₂ : N₂ ≤ n := (le_max_left N₂ N₄).trans ((le_max_right N₁ _).trans
      ((le_max_right N₀ _).trans hn))
    have hn₄ : N₄ ≤ n := (le_max_right N₂ N₄).trans ((le_max_right N₁ _).trans
      ((le_max_right N₀ _).trans hn))
    show R.data.family.PairImproveCloseAt
      (min (h n) (min (1 / 100000) R.data.family.cheeger)) (min (max (d n) 0) (1 / 5000)) n
    rw [heq n hn₂]
    exact pairImproveCloseAt_mono_distance (le_min (le_max_left _ _) (hdsmall n hn₄))
      (hN₀ n ((le_max_left N₀ _).trans hn)).2
  · exact Vanishing.squeeze (fun n ↦ (hthrpos n).le) (fun n ↦ min_le_left _ _)
      (vanishing_of_tendsto htend)
  · refine vanishing_div_of_sqrt_le hρ0 hρ hthrpos (max N₂ N₃) fun n hn ↦ ?_
    show Real.sqrt (ρ n) ≤ min (h n) (min (1 / 100000) R.data.family.cheeger)
    rw [heq n ((le_max_left N₂ N₃).trans hn)]
    exact hN₃ n ((le_max_right N₂ N₃).trans hn)

end CompressorNormalizationAssembly
end GroupApproximation
