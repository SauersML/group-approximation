import GroupApproximation.Sofic.CollapseJointCorner
import GroupApproximation.Sofic.ExactInvolutionLifts
import GroupApproximation.Sofic.InvolutionMicrostateTools

/-!
# Exactly commuting involution microstates for a witness orbit

Let `k` be an involution of `E` whose conjugates along the image of
`iota : Γ →* E` pairwise commute.  In any operator-norm almost
representation the microstates of the orbit elements are almost-commuting
almost-involutions; this file corrects them, window by window and stage by
stage, into a **globally defined, exactly commuting family of exact
involutions** converging to the raw microstates in operator norm.

The correction engine is
`CollapseJointCorner.exists_isExactInvolution_comm_of_unitary_joint'`, which
is Step 1 of `thm:collapse` as the manuscript prints it: at stage `m` the
already-corrected involutions span a joint commutant — a finite intersection
of joint spectral corners — the microstate is compressed into that commutant
in **one** step, and the spectral sign of its Hermitian part is taken **once**,
inside the commutant, so that the earlier involutions are left untouched.  The
cost is therefore linear in the size of the window, `5(m+1)ε`, and there is no
smallness side condition.  (The iterated two-block route
`ExactInvolutionLifts.exists_isExactInvolution_comm_of_unitary` proves the same
statement at cost `3·15^m·ε` under `15^m·3ε ≤ 1`, and needs the separate
commutant-preservation lemma `involutionStep_commutant`, which the manuscript
does not print; it remains available but is no longer on this path.)

The windows exhaust the countable group, the tolerances shrink with the
window, and a `Nat.findGreatest` diagonal produces one family per stage
with the trivial involution as the off-window default.  The output
interface is the single existence theorem `exists_involutionMicrostates`;
everything downstream consumes only its three clauses.
-/

namespace GroupApproximation
namespace InvolutionOrbitMicrostates

open Matrix ExactInvolutionLifts KazhdanCornerMatrices KazhdanCompressorCorner
open scoped Matrix.Norms.L2Operator

variable {Γ E : Type} [Group Γ] [Group E]

/-! ## The witness orbit -/

/-- The conjugation orbit of the witness element. -/
def orbitElement (iota : Γ →* E) (k : E) (γ : Γ) : E :=
  iota γ * k * (iota γ)⁻¹

theorem orbitElement_one (iota : Γ →* E) (k : E) :
    orbitElement iota k 1 = k := by
  unfold orbitElement
  rw [map_one, one_mul, inv_one, mul_one]

theorem orbitElement_mul_self (iota : Γ →* E) {k : E} (hk2 : k * k = 1)
    (γ : Γ) : orbitElement iota k γ * orbitElement iota k γ = 1 := by
  unfold orbitElement
  rw [show iota γ * k * (iota γ)⁻¹ * (iota γ * k * (iota γ)⁻¹) =
    iota γ * (k * k) * (iota γ)⁻¹ by group, hk2]
  group

theorem orbitElement_conj (iota : Γ →* E) (k : E) (g γ : Γ) :
    iota g * orbitElement iota k γ * (iota g)⁻¹ =
      orbitElement iota k (g * γ) := by
  unfold orbitElement
  rw [map_mul]
  group

/-! ## Raw microstates and their defects -/

/-- The raw microstate of an orbit element. -/
noncomputable def raw (B : OpAlmostRepresentation E) (iota : Γ →* E)
    (k : E) (n : ℕ) (γ : Γ) : Matrix (B.model n) (B.model n) ℂ :=
  B.map n (orbitElement iota k γ)

theorem raw_mem_unitaryGroup (B : OpAlmostRepresentation E)
    (iota : Γ →* E) (k : E) (n : ℕ) (γ : Γ) :
    raw B iota k n γ ∈ Matrix.unitaryGroup (B.model n) ℂ :=
  (B.map n (orbitElement iota k γ)).2

/-- The raw microstates are almost involutions. -/
theorem raw_involution_vanishing (B : OpAlmostRepresentation E)
    (iota : Γ →* E) {k : E} (hk2 : k * k = 1) (γ : Γ) :
    OpNormVanishing B (fun n ↦
      raw B iota k n γ * raw B iota k n γ - 1) := by
  have hgrp := orbitElement_mul_self iota hk2 γ
  have hmul := (multiplicativeDefect_vanishing B
    (orbitElement iota k γ) (orbitElement iota k γ)).neg
  have hone := map_one_vanishing B
  refine (hmul.add hone).congr fun n ↦ ?_
  rw [hgrp]
  unfold raw
  abel

/-- The raw microstates almost commute pairwise. -/
theorem raw_commute_vanishing (B : OpAlmostRepresentation E)
    (iota : Γ →* E) (k : E)
    (horb : ∀ γ₁ γ₂ : Γ,
      orbitElement iota k γ₁ * orbitElement iota k γ₂ =
        orbitElement iota k γ₂ * orbitElement iota k γ₁)
    (γ₁ γ₂ : Γ) :
    OpNormVanishing B (fun n ↦
      raw B iota k n γ₁ * raw B iota k n γ₂ -
        raw B iota k n γ₂ * raw B iota k n γ₁) := by
  have h₁ := (multiplicativeDefect_vanishing B
    (orbitElement iota k γ₁) (orbitElement iota k γ₂)).neg
  have h₂ := multiplicativeDefect_vanishing B
    (orbitElement iota k γ₂) (orbitElement iota k γ₁)
  refine (h₁.add h₂).congr fun n ↦ ?_
  rw [horb γ₁ γ₂]
  unfold raw
  abel

/-- Covariance: conjugating a raw microstate by a group microstate tracks
the orbit translation. -/
theorem raw_covariance_vanishing (B : OpAlmostRepresentation E)
    (iota : Γ →* E) (k : E) (g γ : Γ) :
    OpNormVanishing B (fun n ↦
      (B.map n (iota g) : Matrix (B.model n) (B.model n) ℂ) *
          raw B iota k n γ *
          (B.map n (iota g) : Matrix (B.model n) (B.model n) ℂ)ᴴ -
        raw B iota k n (g * γ)) := by
  have h := conj_matrix_defect_vanishing B (iota g) (orbitElement iota k γ)
  refine h.congr fun n ↦ ?_
  rw [orbitElement_conj]
  rfl

/-- Uniform smallness over a finite family of vanishing sequences. -/
theorem opNormVanishing_finset_uniform {ι : Type*}
    (B : OpAlmostRepresentation E) (F : Finset ι)
    (x : ι → ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hx : ∀ i ∈ F, OpNormVanishing B (x i)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, ∀ i ∈ F, ‖x i n‖ ≤ ε := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨0, fun n _ i hi ↦ absurd hi (Finset.notMem_empty i)⟩
  | @insert i₀ F hi₀ ih =>
      obtain ⟨N₁, hN₁⟩ := hx i₀ (Finset.mem_insert_self i₀ F) ε hε
      obtain ⟨N₂, hN₂⟩ := ih fun i hi ↦ hx i (Finset.mem_insert_of_mem hi)
      refine ⟨max N₁ N₂, fun n hn i hi ↦ ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hiF
      · exact hN₁ n ((le_max_left _ _).trans hn)
      · exact hN₂ n ((le_max_right _ _).trans hn) i hiF

/-- The identity matrix is an exact involution. -/
theorem isExactInvolution_one {Y : Type*} [Fintype Y] [DecidableEq Y] :
    IsExactInvolution (1 : Matrix Y Y ℂ) :=
  ⟨Matrix.conjTranspose_one, one_mul 1⟩

/-- Commutator degradation when one factor is replaced by a nearby
matrix, against a unitary. -/
theorem norm_comm_swap {Y : Type*} [Fintype Y] [DecidableEq Y]
    {R R' u : Matrix Y Y ℂ} (hu : u ∈ Matrix.unitaryGroup Y ℂ)
    {η δ : ℝ} (hcomm : ‖R * u - u * R‖ ≤ η) (hclose : ‖R' - R‖ ≤ δ) :
    ‖R' * u - u * R'‖ ≤ η + 2 * δ := by
  have hunorm : ‖u‖ ≤ 1 := norm_le_one_of_mem_unitary hu
  have hsplit : R' * u - u * R' =
      ((R' - R) * u - u * (R' - R)) + (R * u - u * R) := by
    noncomm_ring
  calc
    ‖R' * u - u * R'‖ =
        ‖((R' - R) * u - u * (R' - R)) + (R * u - u * R)‖ := by
      rw [hsplit]
    _ ≤ ‖(R' - R) * u - u * (R' - R)‖ + ‖R * u - u * R‖ :=
      norm_add_le _ _
    _ ≤ (‖(R' - R) * u‖ + ‖u * (R' - R)‖) + η := by
      have := norm_sub_le ((R' - R) * u) (u * (R' - R))
      linarith
    _ ≤ (‖R' - R‖ * ‖u‖ + ‖u‖ * ‖R' - R‖) + η := by
      have h1 := Matrix.l2_opNorm_mul (R' - R) u
      have h2 := Matrix.l2_opNorm_mul u (R' - R)
      linarith
    _ ≤ η + 2 * δ := by
      have hnn : (0 : ℝ) ≤ ‖R' - R‖ := norm_nonneg _
      nlinarith [hclose, hunorm, norm_nonneg u]

/-! ## Window families -/

/-- On any finite window and at any tolerance, every sufficiently late
stage carries a globally defined, exactly commuting family of exact
involutions approximating the raw microstates on the window, trivial off
the window. -/
theorem exists_family_on (B : OpAlmostRepresentation E) (iota : Γ →* E)
    {k : E} (hk2 : k * k = 1)
    (horb : ∀ γ₁ γ₂ : Γ,
      orbitElement iota k γ₁ * orbitElement iota k γ₂ =
        orbitElement iota k γ₂ * orbitElement iota k γ₁)
    (F : Finset Γ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, ∃ V : Γ → Matrix (B.model n) (B.model n) ℂ,
      (∀ γ, IsExactInvolution (V γ)) ∧
      (∀ γ₁ γ₂, V γ₁ * V γ₂ = V γ₂ * V γ₁) ∧
      (∀ γ ∈ F, ‖V γ - raw B iota k n γ‖ ≤ ε) ∧
      (∀ γ ∉ F, V γ = 1) := by
  classical
  revert ε
  induction F using Finset.induction_on with
  | empty =>
      intro ε hε
      refine ⟨0, fun n _ ↦ ⟨fun _ ↦ 1, fun _ ↦ isExactInvolution_one,
        fun _ _ ↦ rfl,
        fun γ hγ ↦ absurd hγ (Finset.notMem_empty γ), fun _ _ ↦ rfl⟩⟩
  | @insert γ₀ F hγ₀ ih =>
      intro ε hε
      have hden : (0 : ℝ) < 5 * ((F.card : ℝ) + 1) := by positivity
      have hden' : (5 : ℝ) * ((F.card : ℝ) + 1) ≠ 0 := ne_of_gt hden
      set ε₀ : ℝ := ε / (5 * ((F.card : ℝ) + 1)) with hε₀def
      have hε₀ : 0 < ε₀ := by
        rw [hε₀def]
        exact div_pos hε hden
      have hε₀mul : 5 * ((F.card : ℝ) + 1) * ε₀ = ε := by
        rw [hε₀def]
        exact mul_div_cancel₀ ε hden'
      set ε₁ : ℝ := min ε (ε₀ / 8) with hε₁def
      have hε₁ : 0 < ε₁ := lt_min hε (by positivity)
      obtain ⟨N₁, hN₁⟩ := ih (ε := ε₁) hε₁
      obtain ⟨N₂, hN₂⟩ :=
        raw_involution_vanishing B iota hk2 γ₀ (ε₀ / 2) (by positivity)
      obtain ⟨N₃, hN₃⟩ := opNormVanishing_finset_uniform B F
        (fun μ ↦ fun n ↦
          raw B iota k n μ * raw B iota k n γ₀ -
            raw B iota k n γ₀ * raw B iota k n μ)
        (fun μ _ ↦ raw_commute_vanishing B iota k horb μ γ₀)
        (ε := ε₀ / 2) (by positivity)
      refine ⟨max N₁ (max N₂ N₃), fun n hn ↦ ?_⟩
      obtain ⟨V, hVinv, hVcomm, hVclose, hVoff⟩ :=
        hN₁ n ((le_max_left _ _).trans hn)
      have hu := raw_mem_unitaryGroup B iota k n γ₀
      have hinv : ‖raw B iota k n γ₀ * raw B iota k n γ₀ - 1‖ ≤ ε₀ := by
        have h := hN₂ n ((le_max_left N₂ N₃).trans
          ((le_max_right N₁ (max N₂ N₃)).trans hn))
        linarith
      have hcomm : ∀ μ ∈ F,
          ‖V μ * raw B iota k n γ₀ - raw B iota k n γ₀ * V μ‖ ≤ ε₀ := by
        intro μ hμ
        have hbase := hN₃ n ((le_max_right N₂ N₃).trans
          ((le_max_right N₁ (max N₂ N₃)).trans hn)) μ hμ
        have hclose : ‖V μ - raw B iota k n μ‖ ≤ ε₀ / 8 :=
          (hVclose μ hμ).trans (min_le_right _ _)
        have h := norm_comm_swap hu hbase hclose
        linarith
      obtain ⟨W, hWinv, hWcomm, hWclose⟩ :=
        CollapseJointCorner.exists_isExactInvolution_comm_of_unitary_joint'
          V hVinv (fun i j ↦ hVcomm i j) F hu hε₀.le hinv hcomm
      refine ⟨fun γ ↦ if γ = γ₀ then W else V γ, ?_, ?_, ?_, ?_⟩
      · intro γ
        dsimp only
        by_cases hγ : γ = γ₀
        · rw [if_pos hγ]
          exact hWinv
        · rw [if_neg hγ]
          exact hVinv γ
      · intro γ₁ γ₂
        dsimp only
        by_cases h₁ : γ₁ = γ₀ <;> by_cases h₂ : γ₂ = γ₀
        · rw [if_pos h₁, if_pos h₂]
        · rw [if_pos h₁, if_neg h₂]
          by_cases hμ : γ₂ ∈ F
          · exact hWcomm γ₂ hμ
          · rw [hVoff γ₂ hμ, one_mul, mul_one]
        · rw [if_neg h₁, if_pos h₂]
          by_cases hμ : γ₁ ∈ F
          · exact (hWcomm γ₁ hμ).symm
          · rw [hVoff γ₁ hμ, one_mul, mul_one]
        · rw [if_neg h₁, if_neg h₂]
          exact hVcomm γ₁ γ₂
      · intro γ hγ
        dsimp only
        rcases Finset.mem_insert.mp hγ with rfl | hγF
        · rw [if_pos rfl]
          calc
            ‖W - raw B iota k n γ‖ ≤ 5 * ((F.card : ℝ) + 1) * ε₀ := hWclose
            _ = ε := hε₀mul
        · have hne : γ ≠ γ₀ := by
            intro h
            rw [h] at hγF
            exact hγ₀ hγF
          rw [if_neg hne]
          exact (hVclose γ hγF).trans (min_le_left _ _)
      · intro γ hγ
        dsimp only
        have hne : γ ≠ γ₀ := fun h ↦ hγ (h ▸ Finset.mem_insert_self γ₀ F)
        have hγF : γ ∉ F := fun h ↦ hγ (Finset.mem_insert_of_mem h)
        rw [if_neg hne]
        exact hVoff γ hγF

/-! ## The stagewise family -/

/-- **Exactly commuting involution microstates.**  For a countable source,
one family per stage: exact involutions, globally pairwise commuting,
converging in operator norm to the raw orbit microstates. -/
theorem exists_involutionMicrostates [Countable Γ]
    (B : OpAlmostRepresentation E) (iota : Γ →* E) {k : E}
    (hk2 : k * k = 1)
    (horb : ∀ γ₁ γ₂ : Γ,
      orbitElement iota k γ₁ * orbitElement iota k γ₂ =
        orbitElement iota k γ₂ * orbitElement iota k γ₁) :
    ∃ V : ∀ n, Γ → Matrix (B.model n) (B.model n) ℂ,
      (∀ n γ, IsExactInvolution (V n γ)) ∧
      (∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁) ∧
      (∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ)) := by
  classical
  haveI : Nonempty Γ := ⟨1⟩
  obtain ⟨e, he⟩ := exists_surjective_nat Γ
  have hall : ∀ N : ℕ, ∃ N₀, ∀ n ≥ N₀,
      ∃ V : Γ → Matrix (B.model n) (B.model n) ℂ,
        (∀ γ, IsExactInvolution (V γ)) ∧
        (∀ γ₁ γ₂, V γ₁ * V γ₂ = V γ₂ * V γ₁) ∧
        (∀ γ ∈ (Finset.range (N + 1)).image e,
          ‖V γ - raw B iota k n γ‖ ≤ 1 / (N + 1)) ∧
        (∀ γ ∉ (Finset.range (N + 1)).image e, V γ = 1) :=
    fun N ↦ exists_family_on B iota hk2 horb
      ((Finset.range (N + 1)).image e) (by positivity)
  set c : ℕ → ℕ := fun N ↦ Classical.choose (hall N)
  have hc : ∀ N, ∀ n ≥ c N,
      ∃ V : Γ → Matrix (B.model n) (B.model n) ℂ,
        (∀ γ, IsExactInvolution (V γ)) ∧
        (∀ γ₁ γ₂, V γ₁ * V γ₂ = V γ₂ * V γ₁) ∧
        (∀ γ ∈ (Finset.range (N + 1)).image e,
          ‖V γ - raw B iota k n γ‖ ≤ 1 / (N + 1)) ∧
        (∀ γ ∉ (Finset.range (N + 1)).image e, V γ = 1) :=
    fun N ↦ Classical.choose_spec (hall N)
  letI : ∀ n, DecidablePred (fun N ↦ ∀ M ≤ N, c M ≤ n) :=
    fun n ↦ Classical.decPred _
  set good : ℕ → ℕ := fun n ↦ Nat.findGreatest (fun N ↦ ∀ M ≤ N, c M ≤ n) n
  refine ⟨fun n ↦ if h : ∀ M ≤ good n, c M ≤ n then
      Classical.choose (hc (good n) n (h (good n) le_rfl))
    else fun _ ↦ 1, ?_, ?_, ?_⟩
  · intro n γ
    dsimp only
    by_cases h : ∀ M ≤ good n, c M ≤ n
    · rw [dif_pos h]
      exact (Classical.choose_spec (hc (good n) n (h (good n) le_rfl))).1 γ
    · rw [dif_neg h]
      exact isExactInvolution_one
  · intro n γ₁ γ₂
    dsimp only
    by_cases h : ∀ M ≤ good n, c M ≤ n
    · rw [dif_pos h]
      exact (Classical.choose_spec (hc (good n) n (h (good n) le_rfl))).2.1 γ₁ γ₂
    · rw [dif_neg h]
  · intro γ ε hε
    obtain ⟨j, hj⟩ := he γ
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (1 / ε)
    set N₁ : ℕ := max (max j N₀) 1
    have hN₁ε : 1 / (N₁ + 1 : ℝ) ≤ ε := by
      have hN₀N₁ : (N₀ : ℝ) ≤ N₁ := by
        exact_mod_cast (le_max_right j N₀).trans (le_max_left _ 1)
      have hpos : (0 : ℝ) < N₁ + 1 := by positivity
      rw [div_le_iff₀ hpos]
      have h1 : 1 / ε < N₁ + 1 := by linarith
      rw [div_lt_iff₀ hε] at h1
      linarith [h1, mul_comm (N₁ + 1 : ℝ) ε]
    set M₁ : ℕ := Finset.sup (Finset.range (N₁ + 1)) c
    refine ⟨max N₁ M₁, fun n hn ↦ ?_⟩
    have hP : ∀ M ≤ N₁, c M ≤ n := by
      intro M hM
      have hmem : M ∈ Finset.range (N₁ + 1) := by
        rw [Finset.mem_range]
        omega
      exact (Finset.le_sup hmem).trans ((le_max_right N₁ M₁).trans hn)
    have hgood_ge : N₁ ≤ good n := by
      have h := Nat.le_findGreatest (P := fun N ↦ ∀ M ≤ N, c M ≤ n)
        ((le_max_left N₁ M₁).trans hn) hP
      exact h
    have hPgood : ∀ M ≤ good n, c M ≤ n := by
      have h := Nat.findGreatest_spec (P := fun N ↦ ∀ M ≤ N, c M ≤ n)
        ((le_max_left N₁ M₁).trans hn) hP
      exact h
    dsimp only
    rw [dif_pos hPgood]
    obtain ⟨hVinv, hVcomm, hVclose, hVoff⟩ :=
      Classical.choose_spec (hc (good n) n (hPgood (good n) le_rfl))
    have hγmem : γ ∈ (Finset.range (good n + 1)).image e := by
      refine Finset.mem_image.mpr ⟨j, ?_, hj⟩
      rw [Finset.mem_range]
      have : j ≤ N₁ := (le_max_left j N₀).trans (le_max_left _ 1)
      omega
    have hclose := hVclose γ hγmem
    refine hclose.trans ?_
    have hmono : 1 / (good n + 1 : ℝ) ≤ 1 / (N₁ + 1 : ℝ) := by
      have h1 : (0 : ℝ) < N₁ + 1 := by positivity
      have h2 : (N₁ + 1 : ℝ) ≤ good n + 1 := by
        exact_mod_cast Nat.add_le_add_right hgood_ge 1
      gcongr
    exact hmono.trans hN₁ε

end InvolutionOrbitMicrostates
end GroupApproximation
