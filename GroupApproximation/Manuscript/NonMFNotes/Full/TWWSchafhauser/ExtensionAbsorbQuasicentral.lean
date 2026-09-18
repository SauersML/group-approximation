import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ExtensionAbsorbQuasicentralSeq

/-!
# Quasicentral approximate units

Lane TWWSch3c2C1, work order WO-TWWSch-3c2-C1.  Manuscript `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (l.1376--1378).  The absorption argument there uses a
quasicentral approximate unit of the compacts inside the bounded operators (Arveson 1977,
Thm. 1; Kasparov 1980, §3; Higson--Roe, *Analytic K-homology*, 3.2).

`exists_quasicentral_approxUnit_of_hom` proves the statement for any separable non-unital
C⋆-algebra `A` and any `⋆`-homomorphism `ι : A → B` whose range absorbs multiplication by `B`
on both sides (`hL`, `hR`).  For a sequence `F` in `B` and tolerances `ε n > 0` it produces
positive contractions `e n ∈ A` such that:

* `e` is increasing and `‖e (n+1) e n - e n‖ < ε n`;
* `‖[ι (e n), F m]‖ < ε n` for `m ≤ n`;
* `e n k → k` and `k e n → k` for every `k ∈ A`.

The sequence iterates `quasiUnit_exists_step` (the averaging of `arvesonPair_exists_average`
along Mathlib's increasing approximate unit).  Step `n` averages above
`quasiUnitRatio ε n • g n`, commutes with `F 0, …, F n`, absorbs `g n` and the first `n + 1`
points of a dense sequence `K`.  All of this holds to within the tolerance `u n = quasiUnitGap ε n`.
The output is then rescaled, `e n = (1 - u (n+1)) • g (n+1)`.  The ratios are chosen so that
the rescaled sequence is increasing, and density (`quasiUnit_tendsto_of_dense`) carries
absorption from `K` to all of `A`.
-/

namespace GroupApproximation
namespace Full
namespace TWWSchafhauser

open Filter Topology

noncomputable section

variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B]

/-- **Quasicentral approximate unit** (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`;
Arveson 1977, Thm. 1; Kasparov 1980, §3; Higson--Roe 3.2), for a separable `A` sitting in `B`
through `ι` as a two-sided ideal. -/
theorem exists_quasicentral_approxUnit_of_hom [TopologicalSpace.SeparableSpace A]
    (ι : A →⋆ₙₐ[ℂ] B) (hL : ∀ (a : A) (y : B), ∃ c : A, ι c = ι a * y)
    (hR : ∀ (a : A) (y : B), ∃ c : A, ι c = y * ι a) (F : ℕ → B) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 < ε n) :
    ∃ e : ℕ → A, (∀ n, 0 ≤ e n) ∧ (∀ n, ‖e n‖ ≤ 1) ∧ Monotone e ∧
      (∀ n, ‖e (n + 1) * e n - e n‖ < ε n) ∧
      (∀ n, ∀ m ≤ n, ‖ι (e n) * F m - F m * ι (e n)‖ < ε n) ∧
      (∀ k, Tendsto (fun n ↦ e n * k) atTop (𝓝 k)) ∧
      (∀ k, Tendsto (fun n ↦ k * e n) atTop (𝓝 k)) := by
  classical
  obtain ⟨K, hK⟩ := TopologicalSpace.exists_dense_seq A
  -- one step of the construction
  have hstep : ∀ (n : ℕ) (x : A), (0 ≤ x ∧ ‖x‖ ≤ 1) → ∃ y : A, (0 ≤ y ∧ ‖y‖ ≤ 1) ∧
      (quasiUnitRatio ε n • x ≤ y ∧
        (∀ m ≤ n, ‖ι y * F m - F m * ι y‖ ≤ quasiUnitGap ε n) ∧
        ‖x - y * x‖ ≤ quasiUnitGap ε n ∧
        ∀ m ≤ n, ‖K m - y * K m‖ ≤ quasiUnitGap ε n ∧ ‖K m - K m * y‖ ≤ quasiUnitGap ε n) := by
    intro n x hx
    obtain ⟨b, hb0, hb1, hbdom, hbY, hbX⟩ := quasiUnit_exists_step ι hL hR hx.1 hx.2
      (quasiUnitRatio_nonneg ε n) (quasiUnitRatio_lt_one hε n)
      ((Finset.range (n + 1)).image F) (insert x ((Finset.range (n + 1)).image K))
      (quasiUnitGap_pos hε n)
    refine ⟨b, ⟨hb0, hb1⟩, hbdom, fun m hm ↦ hbY _ ?_,
      (hbX x (Finset.mem_insert_self _ _)).1, fun m hm ↦ hbX _ ?_⟩
    · exact Finset.mem_image_of_mem F (Finset.mem_range.2 (by omega))
    · exact Finset.mem_insert_of_mem
        (Finset.mem_image_of_mem K (Finset.mem_range.2 (by omega)))
  obtain ⟨g, hg, hgR⟩ := quasiUnit_exists_seq (fun x : A ↦ 0 ≤ x ∧ ‖x‖ ≤ 1) 0
    ⟨le_rfl, by simp⟩ _ hstep
  -- the rescaling factors `1 - u n`
  have hu0 : ∀ n, 0 < quasiUnitGap ε n := quasiUnitGap_pos hε
  have hu4 : ∀ n, quasiUnitGap ε n ≤ 1 / 4 := quasiUnitGap_le_quarter ε
  have ht0 : ∀ n, 0 ≤ 1 - quasiUnitGap ε n := fun n ↦ by linarith [hu4 n]
  have ht1 : ∀ n, 1 - quasiUnitGap ε n ≤ 1 := fun n ↦ by linarith [hu0 n]
  have hnorm : ∀ n, ‖(1 - quasiUnitGap ε (n + 1)) • g (n + 1)‖ ≤ 1 := by
    intro n
    rw [norm_smul, Real.norm_of_nonneg (ht0 _)]
    exact mul_le_one₀ (ht1 _) (norm_nonneg _) (hg _).2
  -- absorption of the dense sequence
  have hut := quasiUnitGap_tendsto hε
  have hlimK : ∀ m, Tendsto (fun n ↦ quasiUnitGap ε n + quasiUnitGap ε (n + 1) * ‖K m‖)
      atTop (𝓝 0) := by
    intro m
    have h1 : Tendsto (fun n ↦ quasiUnitGap ε (n + 1)) atTop (𝓝 0) :=
      hut.comp (tendsto_add_atTop_nat 1)
    have h := hut.add (h1.mul_const ‖K m‖)
    rw [zero_mul, add_zero] at h
    exact h
  have hcost : ∀ n (X Y : A), ‖X - Y‖ ≤ quasiUnitGap ε n →
      ‖(1 - quasiUnitGap ε (n + 1)) • X - Y‖ ≤
        quasiUnitGap ε n + quasiUnitGap ε (n + 1) * ‖Y‖ := by
    intro n X Y hXY
    have h := quasiUnit_norm_smul_sub_le (ht0 (n + 1)) (ht1 (n + 1)) X Y
    have hs : 1 - (1 - quasiUnitGap ε (n + 1)) = quasiUnitGap ε (n + 1) := by ring
    rw [hs] at h
    linarith
  -- the dense-sequence limits
  have hKL : ∀ m, Tendsto (fun n ↦ ((1 - quasiUnitGap ε (n + 1)) • g (n + 1)) * K m) atTop
      (𝓝 (K m)) := by
    intro m
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero'
      (Eventually.of_forall fun n ↦ norm_nonneg _) ?_ (hlimK m))
    refine eventually_atTop.2 ⟨m, fun n hn ↦ ?_⟩
    show ‖((1 - quasiUnitGap ε (n + 1)) • g (n + 1)) * K m - K m‖ ≤
      quasiUnitGap ε n + quasiUnitGap ε (n + 1) * ‖K m‖
    rw [smul_mul_assoc]
    refine hcost n _ _ ?_
    rw [norm_sub_rev]
    exact ((hgR n).2.2.2 m hn).1
  have hKR : ∀ m, Tendsto (fun n ↦ K m * ((1 - quasiUnitGap ε (n + 1)) • g (n + 1))) atTop
      (𝓝 (K m)) := by
    intro m
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero'
      (Eventually.of_forall fun n ↦ norm_nonneg _) ?_ (hlimK m))
    refine eventually_atTop.2 ⟨m, fun n hn ↦ ?_⟩
    show ‖K m * ((1 - quasiUnitGap ε (n + 1)) • g (n + 1)) - K m‖ ≤
      quasiUnitGap ε n + quasiUnitGap ε (n + 1) * ‖K m‖
    rw [mul_smul_comm]
    refine hcost n _ _ ?_
    rw [norm_sub_rev]
    exact ((hgR n).2.2.2 m hn).2
  refine ⟨fun n ↦ (1 - quasiUnitGap ε (n + 1)) • g (n + 1),
    fun n ↦ smul_nonneg (ht0 _) (hg _).1, hnorm, ?_, ?_, ?_, ?_, ?_⟩
  -- monotonicity
  · refine monotone_nat_of_le_succ fun n ↦ ?_
    show (1 - quasiUnitGap ε (n + 1)) • g (n + 1) ≤ (1 - quasiUnitGap ε (n + 1 + 1)) • g (n + 1 + 1)
    have hd : quasiUnitRatio ε (n + 1) • g (n + 1) ≤ g (n + 1 + 1) := (hgR (n + 1)).1
    have h := smul_le_smul_of_nonneg_left hd (ht0 (n + 1 + 1))
    rw [smul_smul, quasiUnitRatio_mul] at h
    exact h
  -- `e (n+1) e n ≈ e n`
  · intro n
    show ‖((1 - quasiUnitGap ε (n + 1 + 1)) • g (n + 1 + 1)) *
        ((1 - quasiUnitGap ε (n + 1)) • g (n + 1)) - (1 - quasiUnitGap ε (n + 1)) • g (n + 1)‖
        < ε n
    have hid : ((1 - quasiUnitGap ε (n + 1 + 1)) • g (n + 1 + 1)) *
        ((1 - quasiUnitGap ε (n + 1)) • g (n + 1)) - (1 - quasiUnitGap ε (n + 1)) • g (n + 1) =
        (1 - quasiUnitGap ε (n + 1)) •
          ((1 - quasiUnitGap ε (n + 1 + 1)) • (g (n + 1 + 1) * g (n + 1)) - g (n + 1)) := by
      rw [smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul, smul_smul,
        mul_comm (1 - quasiUnitGap ε (n + 1 + 1))]
    have hX : ‖g (n + 1 + 1) * g (n + 1) - g (n + 1)‖ ≤ quasiUnitGap ε (n + 1) := by
      rw [norm_sub_rev]
      exact (hgR (n + 1)).2.2.1
    have hc := hcost (n + 1) _ _ hX
    have hG : quasiUnitGap ε (n + 1 + 1) * ‖g (n + 1)‖ ≤ quasiUnitGap ε (n + 1 + 1) :=
      mul_le_of_le_one_right (hu0 _).le (hg _).2
    have hlt1 := quasiUnitGap_succ_lt hε n
    have hlt2 := quasiUnitGap_succ_lt hε (n + 1)
    have hle := quasiUnitGap_le hε n
    have hε0 := hε n
    rw [hid, norm_smul, Real.norm_of_nonneg (ht0 _)]
    calc (1 - quasiUnitGap ε (n + 1)) *
          ‖(1 - quasiUnitGap ε (n + 1 + 1)) • (g (n + 1 + 1) * g (n + 1)) - g (n + 1)‖
        ≤ ‖(1 - quasiUnitGap ε (n + 1 + 1)) • (g (n + 1 + 1) * g (n + 1)) - g (n + 1)‖ :=
          mul_le_of_le_one_left (norm_nonneg _) (ht1 _)
      _ < ε n := by linarith
  -- quasicentrality
  · intro n m hm
    show ‖ι ((1 - quasiUnitGap ε (n + 1)) • g (n + 1)) * F m -
        F m * ι ((1 - quasiUnitGap ε (n + 1)) • g (n + 1))‖ < ε n
    have hc : ‖ι (g (n + 1)) * F m - F m * ι (g (n + 1))‖ ≤ quasiUnitGap ε n :=
      (hgR n).2.1 m hm
    have hle := quasiUnitGap_le hε n
    have hε0 := hε n
    rw [quasiUnit_map_real_smul, smul_mul_assoc, mul_smul_comm, ← smul_sub, norm_smul,
      Real.norm_of_nonneg (ht0 _)]
    calc (1 - quasiUnitGap ε (n + 1)) * ‖ι (g (n + 1)) * F m - F m * ι (g (n + 1))‖
        ≤ ‖ι (g (n + 1)) * F m - F m * ι (g (n + 1))‖ :=
          mul_le_of_le_one_left (norm_nonneg _) (ht1 _)
      _ < ε n := by linarith
  -- absorption from the left, by density
  · intro k
    refine quasiUnit_tendsto_of_dense
      (fun n x ↦ ((1 - quasiUnitGap ε (n + 1)) • g (n + 1)) * x) (fun n x y ↦ ?_) K hK hKL k
    show ‖((1 - quasiUnitGap ε (n + 1)) • g (n + 1)) * x -
      ((1 - quasiUnitGap ε (n + 1)) • g (n + 1)) * y‖ ≤ ‖x - y‖
    rw [← mul_sub]
    calc ‖((1 - quasiUnitGap ε (n + 1)) • g (n + 1)) * (x - y)‖
        ≤ ‖(1 - quasiUnitGap ε (n + 1)) • g (n + 1)‖ * ‖x - y‖ := norm_mul_le _ _
      _ ≤ ‖x - y‖ := mul_le_of_le_one_left (norm_nonneg _) (hnorm n)
  -- absorption from the right, by density
  · intro k
    refine quasiUnit_tendsto_of_dense
      (fun n x ↦ x * ((1 - quasiUnitGap ε (n + 1)) • g (n + 1))) (fun n x y ↦ ?_) K hK hKR k
    show ‖x * ((1 - quasiUnitGap ε (n + 1)) • g (n + 1)) -
      y * ((1 - quasiUnitGap ε (n + 1)) • g (n + 1))‖ ≤ ‖x - y‖
    rw [← sub_mul]
    calc ‖(x - y) * ((1 - quasiUnitGap ε (n + 1)) • g (n + 1))‖
        ≤ ‖x - y‖ * ‖(1 - quasiUnitGap ε (n + 1)) • g (n + 1)‖ := norm_mul_le _ _
      _ ≤ ‖x - y‖ := mul_le_of_le_one_right (norm_nonneg _) (hnorm n)

end

end TWWSchafhauser
end Full
end GroupApproximation
