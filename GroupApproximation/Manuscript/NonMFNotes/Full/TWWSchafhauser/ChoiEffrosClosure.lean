import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ChoiEffrosArvesonPairSqrt
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ChoiEffrosArvesonStep
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ChoiEffrosCPLimit

/-!
# Choi–Effros lifting, Arveson's closure theorem

Lane `TWWSchafhauser-3a` (work order `WO-TWWCore-3`, piece 3a).

Let `π : B → C` be a `⋆`-homomorphism of C⋆-algebras and `φ : A → C` a
contraction on a separable C⋆-algebra.  Suppose `φ` is *approximately
cpc-liftable*: on every finite set, within every `ε > 0`, `φ` agrees with
`π ∘ ψ` for some completely positive contraction `ψ : A → B`.  Then `φ` has an
exact completely positive contractive lift.

* `exists_arveson_splice` — given a cpc approximate lift `ψ₀` on `F` (error `δ`)
  and a finer target `(F', ε)`, there is a cpc approximate lift on `F'`
  (error `ε`) within `δ + 4ε` of `ψ₀` on `F`: splice `ψ₀` with a fresh
  approximate lift `ψ₁` along an Arveson pair (`exists_arvesonPair`,
  `arvesonCombination`);
* `exists_cpc_lift_of_approx` — iterate the splice along the finite sets
  `{u 0, …, u n}` of a dense sequence with errors `2⁻ⁿ`; the resulting sequence
  is pointwise Cauchy on the dense set and its limit is the lift
  (`exists_cpc_lift_of_cauchy`).

Sources: W. Arveson, *Notes on extensions of C⋆-algebras*, Duke Math. J. **44**
(1977), 329–355, §2, Theorem 6; N. P. Brown, N. Ozawa, *C⋆-algebras and
finite-dimensional approximations*, Lemma C.2 and Theorem C.3.
-/

namespace GroupApproximation
namespace Full
namespace TWWSchafhauser

open Filter Topology

noncomputable section

universe u v w

/-- The unit of a C⋆-algebra has norm at most one (`‖1‖ = ‖1‖²`). -/
theorem choiEffros_norm_one_le {A : Type u} [CStarAlgebra A] : ‖(1 : A)‖ ≤ 1 := by
  have h0 := CStarRing.norm_star_mul_self (x := (1 : A))
  rw [star_one, one_mul] at h0
  nlinarith [norm_nonneg (1 : A)]

variable {A : Type u} {B : Type v} {C : Type w}
  [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

/-- **Arveson's splicing step.**  A cpc approximate lift `ψ₀` of `φ` on `F`
(error `δ`) can be replaced by a cpc approximate lift on any finite `F'`
(error `ε`) that moves `ψ₀` on `F` by at most `δ + 4ε`. -/
theorem exists_arveson_splice (π : B →⋆ₐ[ℂ] C) {φ : A →ₗ[ℂ] C}
    (happrox : ∀ (F : Finset A) (ε : ℝ), 0 < ε → ∃ ψ : A →ₗ[ℂ] B,
      CStarExactness.IsCompletelyPositive ψ ∧ (∀ a, ‖ψ a‖ ≤ ‖a‖) ∧
        ∀ a ∈ F, ‖π (ψ a) - φ a‖ ≤ ε)
    {ψ₀ : A →ₗ[ℂ] B} (h₀ : CStarExactness.IsCompletelyPositive ψ₀)
    (h₀c : ∀ a, ‖ψ₀ a‖ ≤ ‖a‖) {F : Finset A} {δ : ℝ}
    (h₀F : ∀ a ∈ F, ‖π (ψ₀ a) - φ a‖ ≤ δ) (F' : Finset A) (ε : ℝ) (hε : 0 < ε) :
    ∃ ψ : A →ₗ[ℂ] B, CStarExactness.IsCompletelyPositive ψ ∧ (∀ a, ‖ψ a‖ ≤ ‖a‖) ∧
      (∀ a ∈ F', ‖π (ψ a) - φ a‖ ≤ ε) ∧ ∀ a ∈ F, ‖ψ a - ψ₀ a‖ ≤ δ + 4 * ε := by
  classical
  obtain ⟨ψ₁, h₁, h₁c, h₁F⟩ := happrox (F ∪ F') ε hε
  obtain ⟨f, g, hf, hg, hf1, hg1, hfg, hπf, hπg, hY, hX⟩ :=
    exists_arvesonPair π (F.image ⇑ψ₁ ∪ F.image ⇑ψ₀) (F.image fun a ↦ ψ₁ a - ψ₀ a) ε hε
  have h1 : ‖(1 : A)‖ ≤ 1 := choiEffros_norm_one_le
  refine ⟨arvesonCombination f g ψ₁ ψ₀, isCompletelyPositive_arvesonCombination f g h₁ h₀,
    norm_arvesonCombination_apply_le hf hg hfg h₁ h₀ ((h₁c 1).trans h1) ((h₀c 1).trans h1),
    fun a ha ↦ ?_, fun a ha ↦ ?_⟩
  · rw [map_arvesonCombination π hπf hπg]
    exact h₁F a (Finset.mem_union_right F ha)
  · have hYa := (hY (ψ₁ a) (Finset.mem_union_left _ (Finset.mem_image_of_mem ⇑ψ₁ ha))).1
    have hYb := (hY (ψ₀ a) (Finset.mem_union_right _ (Finset.mem_image_of_mem ⇑ψ₀ ha))).2
    have hXa : ‖f * f * (ψ₁ a - ψ₀ a)‖ ≤ ‖π (ψ₁ a - ψ₀ a)‖ + ε :=
      hX (ψ₁ a - ψ₀ a) (Finset.mem_image_of_mem (fun a ↦ ψ₁ a - ψ₀ a) ha)
    have hquot : ‖π (ψ₁ a - ψ₀ a)‖ ≤ ε + δ := by
      rw [map_sub, ← sub_sub_sub_cancel_right (π (ψ₁ a)) (π (ψ₀ a)) (φ a)]
      exact (norm_sub_le _ _).trans
        (add_le_add (h₁F a (Finset.mem_union_left F' ha)) (h₀F a ha))
    have hsplice := norm_arvesonCombination_sub_le hf hg hf1 hg1 hfg ψ₁ ψ₀ a
    linarith

/-- A stage of the Arveson iteration: a completely positive contraction that
lifts `φ` on `F` up to error `δ`. -/
abbrev ChoiEffrosStage (π : B →⋆ₐ[ℂ] C) (φ : A →ₗ[ℂ] C) (F : Finset A) (δ : ℝ)
    (ψ : A →ₗ[ℂ] B) : Prop :=
  CStarExactness.IsCompletelyPositive ψ ∧ (∀ a, ‖ψ a‖ ≤ ‖a‖) ∧ ∀ a ∈ F, ‖π (ψ a) - φ a‖ ≤ δ

/-- **Arveson's closure theorem.**  On a separable C⋆-algebra, a contraction
that is approximately liftable by completely positive contractions on finite
sets has an exact completely positive contractive lift. -/
theorem exists_cpc_lift_of_approx [TopologicalSpace.SeparableSpace A] (π : B →⋆ₐ[ℂ] C)
    {φ : A →ₗ[ℂ] C} (hφc : ∀ a, ‖φ a‖ ≤ ‖a‖)
    (happrox : ∀ (F : Finset A) (ε : ℝ), 0 < ε → ∃ ψ : A →ₗ[ℂ] B,
      CStarExactness.IsCompletelyPositive ψ ∧ (∀ a, ‖ψ a‖ ≤ ‖a‖) ∧
        ∀ a ∈ F, ‖π (ψ a) - φ a‖ ≤ ε) :
    ∃ ψ : A →ₗ[ℂ] B, CStarExactness.IsCompletelyPositive ψ ∧ (∀ a, ‖ψ a‖ ≤ ‖a‖) ∧
      ∀ a, π (ψ a) = φ a := by
  classical
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq A
  obtain ⟨ψ₀, hψ₀⟩ : ∃ ψ₀ : A →ₗ[ℂ] B,
      ChoiEffrosStage π φ ((Finset.range (0 + 1)).image u) ((1 / 2 : ℝ) ^ 0) ψ₀ :=
    happrox _ _ (by positivity)
  have hstep : ∀ (n : ℕ) (ψ : A →ₗ[ℂ] B), ∃ ψ' : A →ₗ[ℂ] B,
      ChoiEffrosStage π φ ((Finset.range (n + 1)).image u) ((1 / 2 : ℝ) ^ n) ψ →
        ChoiEffrosStage π φ ((Finset.range (n + 1 + 1)).image u) ((1 / 2 : ℝ) ^ (n + 1)) ψ' ∧
          ∀ a ∈ (Finset.range (n + 1)).image u, ‖ψ' a - ψ a‖ ≤ 3 * (1 / 2 : ℝ) ^ n := by
    intro n ψ
    by_cases hψ : ChoiEffrosStage π φ ((Finset.range (n + 1)).image u) ((1 / 2 : ℝ) ^ n) ψ
    · obtain ⟨ψ', h', h'c, h'F, h'close⟩ := exists_arveson_splice π happrox hψ.1 hψ.2.1
        hψ.2.2 ((Finset.range (n + 1 + 1)).image u) ((1 / 2 : ℝ) ^ (n + 1)) (by positivity)
      refine ⟨ψ', fun _ ↦ ⟨⟨h', h'c, h'F⟩, fun a ha ↦ ?_⟩⟩
      have hhalf : (1 / 2 : ℝ) ^ (n + 1) = (1 / 2 : ℝ) ^ n / 2 := by ring
      linarith [h'close a ha]
    · exact ⟨ψ, fun h ↦ absurd h hψ⟩
  choose next hnext using hstep
  obtain ⟨seq, hseq0, hseqs⟩ : ∃ seq : ℕ → A →ₗ[ℂ] B,
      seq 0 = ψ₀ ∧ ∀ n, seq (n + 1) = next n (seq n) :=
    ⟨fun n ↦ Nat.rec (motive := fun _ ↦ A →ₗ[ℂ] B) ψ₀ (fun n ψ ↦ next n ψ) n,
      rfl, fun _ ↦ rfl⟩
  have hstage : ∀ n,
      ChoiEffrosStage π φ ((Finset.range (n + 1)).image u) ((1 / 2 : ℝ) ^ n) (seq n) := by
    intro n
    induction n with
    | zero =>
      rw [hseq0]
      exact hψ₀
    | succ n ih =>
      rw [hseqs]
      exact (hnext n (seq n) ih).1
  have hsucc : ∀ k n, k ≤ n →
      ‖seq (n + 1) (u k) - seq n (u k)‖ ≤ 3 * (1 / 2 : ℝ) ^ n := by
    intro k n hkn
    rw [hseqs]
    exact (hnext n (seq n) (hstage n)).2 (u k)
      (Finset.mem_image_of_mem u (Finset.mem_range.2 (Nat.lt_succ_of_le hkn)))
  have hC : ∀ s ∈ Set.range u, CauchySeq fun m ↦ seq m s := by
    rintro _ ⟨k, rfl⟩
    refine (cauchySeq_shift k).1
      (cauchySeq_of_le_geometric (1 / 2) (3 * (1 / 2 : ℝ) ^ k) (by norm_num) fun n ↦ ?_)
    show dist (seq (n + k) (u k)) (seq (n + 1 + k) (u k)) ≤
      3 * (1 / 2 : ℝ) ^ k * (1 / 2) ^ n
    rw [Nat.add_right_comm n 1 k, dist_eq_norm, norm_sub_rev]
    calc ‖seq (n + k + 1) (u k) - seq (n + k) (u k)‖ ≤ 3 * (1 / 2 : ℝ) ^ (n + k) :=
          hsucc k (n + k) (Nat.le_add_left k n)
      _ = 3 * (1 / 2 : ℝ) ^ k * (1 / 2) ^ n := by
          rw [pow_add]
          ring
  have hπ : ∀ s ∈ Set.range u, Tendsto (fun m ↦ π (seq m s)) atTop (𝓝 (φ s)) := by
    rintro _ ⟨k, rfl⟩
    have hbound : ∀ᶠ m in atTop, ‖π (seq m (u k)) - φ (u k)‖ ≤ (1 / 2 : ℝ) ^ m :=
      eventually_atTop.2 ⟨k, fun m hm ↦ (hstage m).2.2 (u k)
        (Finset.mem_image_of_mem u (Finset.mem_range.2 (Nat.lt_succ_of_le hm)))⟩
    exact tendsto_iff_norm_sub_tendsto_zero.2
      (squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) hbound
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)))
  exact exists_cpc_lift_of_cauchy π hφc (fun m ↦ (hstage m).1) (fun m ↦ (hstage m).2.1)
    (show Dense (Set.range u) from hu) hC hπ

end

end TWWSchafhauser
end Full
end GroupApproximation
