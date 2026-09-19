import GroupApproximation.Sofic.KazhdanCornerModel

/-!
# Diagonal extraction for the Kazhdan moving corner

The moving compression is eventually nonzero and almost unitary for each
fixed group element.  This file performs the countable diagonal extraction:
at stage `n`, the first `n + 1` enumerated group elements all have Gram defect
at most `1 / (n + 2)`, while the selected original weak-MF stage is at least
`n`.  Thus every fixed element is eventually represented by its exact polar
correction and all original eventual estimates remain available.
-/

namespace GroupApproximation
namespace KazhdanCornerMatrices

open Filter Matrix
open scoped Matrix.Norms.L2Operator

variable {G : Type} [Group G]

/-- All finite-stage input chosen for one Kazhdan moving-corner
construction. -/
structure MovingCornerSetup (G : Type) [Group G] where
  S : Finset G
  epsilon : ℝ
  one_mem : 1 ∈ S
  symmetric : ∀ g ∈ S, g⁻¹ ∈ S
  generates : Subgroup.closure (S : Set G) = ⊤
  epsilon_pos : 0 < epsilon
  epsilon_le_one : epsilon ≤ 1
  kazhdan : IsKazhdanPair.{0, 0} G S epsilon
  approximation : WeakMFApproximation G
  cutoff : ℝ
  gap_lt_cutoff : 1 - epsilon ^ 2 / (4 * S.card) < cutoff
  cutoff_lt_one : cutoff < 1

/-- Property `(T)` and a sequential weak-MF approximation supply moving-corner
data with a cutoff strictly between the Kazhdan spectral bound and `1`. -/
theorem exists_movingCornerSetup [Countable G]
    (hT : HasKazhdanPropertyT.{0, 0} G) (hMF : IsWeakMF G) :
    Nonempty (MovingCornerSetup G) := by
  classical
  obtain ⟨S, epsilon, hone, hsymm, hgen, hepsilon, hepsilonOne, hpair⟩ :=
    KazhdanProjection.HasKazhdanPropertyT.exists_symmetric_generating_pair hT
  obtain ⟨delta, hdelta, happrox⟩ := hMF
  let A : WeakMFApproximation G :=
    Classical.choice (exists_weakMFApproximation hdelta happrox)
  have hcardNat : 0 < S.card := Finset.card_pos.mpr ⟨1, hone⟩
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hcardNat
  have hgap : 0 < epsilon ^ 2 / (4 * (S.card : ℝ)) :=
    div_pos (sq_pos_of_pos hepsilon) (mul_pos (by norm_num) hcard)
  let c : ℝ := 1 - epsilon ^ 2 / (4 * S.card)
  let t : ℝ := (c + 1) / 2
  have hct : c < t := by dsimp [c, t]; linarith
  have htOne : t < 1 := by dsimp [c, t]; linarith
  exact ⟨{
    S := S
    epsilon := epsilon
    one_mem := hone
    symmetric := hsymm
    generates := hgen
    epsilon_pos := hepsilon
    epsilon_le_one := hepsilonOne
    kazhdan := hpair
    approximation := A
    cutoff := t
    gap_lt_cutoff := hct
    cutoff_lt_one := htOne }⟩

/-- Closed positive control: the setup certificate is inhabited for the
trivial group. -/
theorem movingCornerSetup_punit : Nonempty (MovingCornerSetup PUnit) := by
  have hT : HasKazhdanPropertyT.{0, 0} PUnit := by
    refine ⟨{1}, 1, by
      refine ⟨by norm_num, ?_⟩
      intro E _ _ _ rho x hx _
      refine ⟨x, ?_, ?_⟩
      · intro hzero
        rw [hzero, norm_zero] at hx
        norm_num at hx
      · intro g
        have hg : g = 1 := Subsingleton.elim _ _
        rw [hg, map_one]
        rfl⟩
  exact exists_movingCornerSetup hT (isWeakMF_of_finite PUnit)

/-- Every fixed compressed element has vanishing Gram defect. -/
theorem MovingCornerSetup.gram_eventually_small (D : MovingCornerSetup G)
    (g : G) : ∀ eta : ℝ, 0 < eta → ∃ N, ∀ n ≥ N,
    ‖cornerGram (movingCompression D.approximation.toOpAlmostRepresentation D.S D.cutoff n g) - 1‖ ≤
      eta :=
  movingCompression_gram_eventually_small D.kazhdan D.S (by rfl)
    D.one_mem D.epsilon_le_one D.symmetric D.generates D.approximation.toOpAlmostRepresentation
      D.gap_lt_cutoff g

/-- Every pair of fixed compressed elements is asymptotically
multiplicative. -/
theorem MovingCornerSetup.multiplicative_eventually
    (D : MovingCornerSetup G) (g h : G) :
    ∀ eta : ℝ, 0 < eta → ∃ N, ∀ n ≥ N,
      ‖movingCompression D.approximation.toOpAlmostRepresentation D.S D.cutoff n (g * h) -
        movingCompression D.approximation.toOpAlmostRepresentation D.S D.cutoff n g *
          movingCompression D.approximation.toOpAlmostRepresentation D.S D.cutoff n h‖ ≤ eta :=
  movingCompression_multiplicative_eventually D.kazhdan D.S (by rfl)
    D.one_mem D.epsilon_le_one D.symmetric D.generates D.approximation.toOpAlmostRepresentation
      D.gap_lt_cutoff g h

/-- The moving coordinate type is eventually inhabited. -/
theorem MovingCornerSetup.eventually_nonempty [Nontrivial G]
    (D : MovingCornerSetup G) :
    ∃ N, ∀ n ≥ N, Nonempty
      {i : D.approximation.toOpAlmostRepresentation.model n //
        movingPredicate D.approximation.toOpAlmostRepresentation D.S D.cutoff n i} := by
  simpa only [WeakMFMovingIndex] using
    eventually_nonempty_weakMFMovingIndex D.kazhdan D.S (by rfl)
      D.one_mem D.epsilon_le_one D.symmetric D.generates D.approximation
        D.gap_lt_cutoff

/-- Accuracy imposed at diagonal stage `n`. -/
noncomputable def diagonalTolerance (n : ℕ) : ℝ := 1 / (n + 2)

theorem diagonalTolerance_pos (n : ℕ) : 0 < diagonalTolerance n := by
  simp only [diagonalTolerance]
  positivity

theorem diagonalTolerance_le_half (n : ℕ) :
    diagonalTolerance n ≤ 1 / 2 := by
  simp only [diagonalTolerance]
  apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
  have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  linarith

theorem diagonalTolerance_eventually_le {eta : ℝ} (heta : 0 < eta) :
    ∃ N, ∀ n ≥ N, diagonalTolerance n ≤ eta := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / eta)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hlarge : 1 / eta < (n : ℝ) + 2 := by linarith
  simp only [diagonalTolerance]
  rw [div_le_iff₀ (by positivity)]
  rw [div_lt_iff₀ heta] at hlarge
  linarith

/-- Perturbing three factors controls the resulting multiplication defect. -/
theorem norm_mul_defect_of_perturbations {Y : Type*} [Fintype Y]
    [DecidableEq Y] (Wgh Wg Wh Cgh Cg Ch : Matrix Y Y ℂ) :
    ‖Wgh - Wg * Wh‖ ≤
      ‖Wgh - Cgh‖ + ‖Cgh - Cg * Ch‖ +
        ‖Cg - Wg‖ * ‖Wh‖ + ‖Cg‖ * ‖Ch - Wh‖ := by
  have hsplit : Wgh - Wg * Wh =
      (Wgh - Cgh) + (Cgh - Cg * Ch) +
        (Cg - Wg) * Wh + Cg * (Ch - Wh) := by
    noncomm_ring
  rw [hsplit]
  calc
    ‖(Wgh - Cgh) + (Cgh - Cg * Ch) + (Cg - Wg) * Wh +
        Cg * (Ch - Wh)‖ ≤
      ‖Wgh - Cgh‖ + ‖Cgh - Cg * Ch‖ + ‖(Cg - Wg) * Wh‖ +
        ‖Cg * (Ch - Wh)‖ := by
          calc
            _ ≤ ‖(Wgh - Cgh) + (Cgh - Cg * Ch) + (Cg - Wg) * Wh‖ +
                ‖Cg * (Ch - Wh)‖ := norm_add_le _ _
            _ ≤ (‖(Wgh - Cgh) + (Cgh - Cg * Ch)‖ +
                ‖(Cg - Wg) * Wh‖) + ‖Cg * (Ch - Wh)‖ :=
              by
                have h := norm_add_le
                  ((Wgh - Cgh) + (Cgh - Cg * Ch)) ((Cg - Wg) * Wh)
                linarith
            _ ≤ ((‖Wgh - Cgh‖ + ‖Cgh - Cg * Ch‖) +
                ‖(Cg - Wg) * Wh‖) + ‖Cg * (Ch - Wh)‖ :=
              by
                have h := norm_add_le (Wgh - Cgh) (Cgh - Cg * Ch)
                linarith
    _ ≤ ‖Wgh - Cgh‖ + ‖Cgh - Cg * Ch‖ +
        ‖Cg - Wg‖ * ‖Wh‖ + ‖Cg‖ * ‖Ch - Wh‖ := by
      have hleft := Matrix.l2_opNorm_mul (Cg - Wg) Wh
      have hright := Matrix.l2_opNorm_mul Cg (Ch - Wh)
      linarith

/-- A cofinal schedule on which the moving corner is nonempty and the first
`n + 1` enumerated elements all satisfy the stage-`n` Gram bound. -/
structure MovingCornerSchedule [Nontrivial G] (D : MovingCornerSetup G) where
  enumerate : ℕ → G
  enumerate_surjective : Function.Surjective enumerate
  stage : ℕ → ℕ
  stage_ge : ∀ n, n ≤ stage n
  moving_nonempty : ∀ n, Nonempty
    {i : D.approximation.toOpAlmostRepresentation.model (stage n) //
      movingPredicate D.approximation.toOpAlmostRepresentation D.S D.cutoff (stage n) i}
  gram_close : ∀ n k, k ≤ n →
    ‖cornerGram (movingCompression D.approximation.toOpAlmostRepresentation D.S D.cutoff
      (stage n) (enumerate k)) - 1‖ ≤ diagonalTolerance n

/-- Countability supplies a schedule satisfying all finite initial Gram
constraints at once. -/
theorem exists_movingCornerSchedule [Nontrivial G] [Countable G]
    (D : MovingCornerSetup G) : Nonempty (MovingCornerSchedule D) := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat G
  obtain ⟨Nzero, hNzero⟩ := D.eventually_nonempty
  let F : ℕ → Finset G := fun n ↦ (Finset.range (n + 1)).image e
  have hsimultaneous (n : ℕ) : ∃ N, ∀ m ≥ N, ∀ g ∈ F n,
      ‖cornerGram (movingCompression D.approximation.toOpAlmostRepresentation D.S D.cutoff m g) - 1‖ ≤
        diagonalTolerance n := by
    apply eventually_finset (F n)
    intro g _
    exact D.gram_eventually_small g (diagonalTolerance n)
      (diagonalTolerance_pos n)
  let threshold : ℕ → ℕ := fun n ↦ Classical.choose (hsimultaneous n)
  have hthreshold (n : ℕ) : ∀ m ≥ threshold n, ∀ g ∈ F n,
      ‖cornerGram (movingCompression D.approximation.toOpAlmostRepresentation D.S D.cutoff m g) - 1‖ ≤
        diagonalTolerance n := Classical.choose_spec (hsimultaneous n)
  let stage : ℕ → ℕ := fun n ↦ max n (max Nzero (threshold n))
  refine ⟨{
    enumerate := e
    enumerate_surjective := he
    stage := stage
    stage_ge := fun n ↦ le_max_left _ _
    moving_nonempty := fun n ↦ hNzero (stage n) (by
      exact (le_max_left Nzero (threshold n)).trans
        (le_max_right n (max Nzero (threshold n))))
    gram_close := ?_ }⟩
  intro n k hk
  exact hthreshold n (stage n)
    ((le_max_right Nzero (threshold n)).trans
      (le_max_right n (max Nzero (threshold n)))) (e k)
    (Finset.mem_image.mpr ⟨k, by simp only [Finset.mem_range]; omega, rfl⟩)

/-- A chosen enumeration index for each group element. -/
noncomputable def MovingCornerSchedule.code [Nontrivial G]
    {D : MovingCornerSetup G} (R : MovingCornerSchedule D) (g : G) : ℕ :=
  Classical.choose (R.enumerate_surjective g)

@[simp] theorem MovingCornerSchedule.enumerate_code [Nontrivial G]
    {D : MovingCornerSetup G} (R : MovingCornerSchedule D) (g : G) :
    R.enumerate (R.code g) = g :=
  Classical.choose_spec (R.enumerate_surjective g)

/-- The selected moving coordinate type, bundled as a finite matrix model. -/
noncomputable abbrev MovingCornerSchedule.model [Nontrivial G]
    {D : MovingCornerSetup G} (R : MovingCornerSchedule D) (n : ℕ) :
    FiniteModel :=
  weakMFMovingModel D.approximation.toOpAlmostRepresentation D.S D.cutoff (R.stage n)

theorem MovingCornerSchedule.model_nonempty [Nontrivial G]
    {D : MovingCornerSetup G} (R : MovingCornerSchedule D) (n : ℕ) :
    0 < Fintype.card (R.model n) := by
  rw [Fintype.card_pos_iff]
  exact R.moving_nonempty n

/-- Exact scheduled unitary.  Once `g` has entered the finite exhaustion, it
is the polar correction of the moving compression; before that finite stage
it is initialized to the identity. -/
noncomputable def MovingCornerSchedule.map [Nontrivial G]
    {D : MovingCornerSetup G} (R : MovingCornerSchedule D)
    (n : ℕ) (g : G) :
    @Matrix.unitaryGroup (R.model n) (R.model n).decidableEq
      (R.model n).fintype ℂ Complex.commRing Complex.instStarRing := by
  by_cases hg : R.code g ≤ n
  · have hclose := R.gram_close n (R.code g) hg
    rw [R.enumerate_code g] at hclose
    exact polarCorrectedMovingCompression D.approximation.toOpAlmostRepresentation D.S D.cutoff
      (R.stage n) g (diagonalTolerance_le_half n) hclose
  · exact 1

/-- Pointwise polar-correction estimate once an element is active in the
finite exhaustion. -/
theorem MovingCornerSchedule.map_close_of_code_le [Nontrivial G]
    {D : MovingCornerSetup G} (R : MovingCornerSchedule D)
    (n : ℕ) (g : G) (hg : R.code g ≤ n) :
    ‖(R.map n g : Matrix (R.model n) (R.model n) ℂ) -
        movingCompression D.approximation.toOpAlmostRepresentation D.S D.cutoff (R.stage n) g‖ ≤
      2 * diagonalTolerance n := by
  rw [MovingCornerSchedule.map, dif_pos hg]
  exact norm_polarCorrectedMovingCompression_sub_le D.approximation.toOpAlmostRepresentation D.S
    D.cutoff (R.stage n) g (diagonalTolerance_pos n).le
      (diagonalTolerance_le_half n) (by
        simpa only [R.enumerate_code g] using
          R.gram_close n (R.code g) hg)

/-- Every fixed scheduled unitary is eventually within twice the diagonal
tolerance of its uncorrected moving compression. -/
theorem MovingCornerSchedule.map_eventually_close [Nontrivial G]
    {D : MovingCornerSetup G} (R : MovingCornerSchedule D) (g : G) :
    ∃ N, ∀ n ≥ N,
      ‖(R.map n g : Matrix (R.model n) (R.model n) ℂ) -
        movingCompression D.approximation.toOpAlmostRepresentation D.S D.cutoff (R.stage n) g‖ ≤
          2 * diagonalTolerance n := by
  refine ⟨R.code g, fun n hn ↦ ?_⟩
  exact R.map_close_of_code_le n g hn

/-- On all sufficiently late scheduled stages, the total real normalized
trace of the corrected generator blocks is bounded by the spectral cutoff,
up to the polar-correction error. -/
theorem MovingCornerSchedule.generator_trace_eventually_le
    [Nontrivial G] {D : MovingCornerSetup G} (R : MovingCornerSchedule D) :
    ∃ N, ∀ n ≥ N,
      ∑ g ∈ D.S, (normTrace (R.model n) (R.map n g)).re ≤
        (D.S.card : ℝ) * D.cutoff +
          (D.S.card : ℝ) * (2 * diagonalTolerance n) := by
  classical
  obtain ⟨N, hN⟩ := eventually_finset D.S (fun g n ↦ R.code g ≤ n)
    (fun g _ ↦ ⟨R.code g, fun n hn ↦ hn⟩)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hactive : ∀ g ∈ D.S, R.code g ≤ n := hN n hn
  have hmodel : 0 < Fintype.card (R.model n) := R.model_nonempty n
  have hterm (g : G) (hg : g ∈ D.S) :
      (normTrace (R.model n) (R.map n g)).re ≤
      (normTrace (R.model n)
          (movingCompression D.approximation.toOpAlmostRepresentation D.S D.cutoff (R.stage n) g)).re +
            2 * diagonalTolerance n := by
    let C : Matrix (R.model n) (R.model n) ℂ :=
      movingCompression D.approximation.toOpAlmostRepresentation D.S D.cutoff (R.stage n) g
    have htrace := re_normTrace_le_add_l2_opNorm (R.model n) hmodel
      (R.map n g) C
    have hclose := R.map_close_of_code_le n g (hactive g hg)
    dsimp only [C] at htrace ⊢
    linarith
  have hsum := Finset.sum_le_sum fun g hg ↦ hterm g hg
  have hcorner := sum_re_normTrace_movingCompression_le D.approximation.toOpAlmostRepresentation D.S
    D.one_mem D.cutoff (R.stage n) (R.moving_nonempty n)
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  nlinarith

/-- Squared Hilbert--Schmidt displacement of a unitary is `2 - 2 Re(τ)`. -/
theorem hsLengthSq_eq_two_sub_two_re_normTrace (Y : FiniteModel)
    (hY : 0 < Fintype.card Y) (u : Matrix.unitaryGroup Y ℂ) :
    hsLengthSq Y u = 2 - 2 * (normTrace Y u).re := by
  have hone : (1 : Matrix Y Y ℂ) ∈ Matrix.unitaryGroup Y ℂ :=
    Submonoid.one_mem _
  change hsDistSq Y (u : Matrix Y Y ℂ) 1 = _
  rw [hsDistSq_of_unitary Y u.2 hone hY, Matrix.conjTranspose_one,
    Matrix.mul_one]

/-- Eventually the average corrected generator trace stays uniformly below
one. -/
theorem MovingCornerSchedule.generator_trace_eventually_below_one
    [Nontrivial G] {D : MovingCornerSetup G} (R : MovingCornerSchedule D) :
    ∃ N, ∀ n ≥ N,
      ∑ g ∈ D.S, (normTrace (R.model n) (R.map n g)).re ≤
        (D.S.card : ℝ) * ((1 + D.cutoff) / 2) := by
  obtain ⟨Ntrace, htrace⟩ := R.generator_trace_eventually_le
  obtain ⟨Ntol, htol⟩ := diagonalTolerance_eventually_le
    (show 0 < (1 - D.cutoff) / 4 by linarith [D.cutoff_lt_one])
  refine ⟨max Ntrace Ntol, fun n hn ↦ ?_⟩
  have ht := htrace n ((le_max_left _ _).trans hn)
  have hd := htol n ((le_max_right _ _).trans hn)
  have hcard : (0 : ℝ) ≤ D.S.card := Nat.cast_nonneg _
  nlinarith

/-- The exact scheduled generators retain a fixed positive total tracial
displacement. -/
theorem MovingCornerSchedule.generator_hsLengthSq_eventually_ge
    [Nontrivial G] {D : MovingCornerSetup G} (R : MovingCornerSchedule D) :
    ∃ N, ∀ n ≥ N,
      (D.S.card : ℝ) * (1 - D.cutoff) ≤
        ∑ g ∈ D.S, hsLengthSq (R.model n) (R.map n g) := by
  obtain ⟨N, hN⟩ := R.generator_trace_eventually_below_one
  refine ⟨N, fun n hn ↦ ?_⟩
  have htrace := hN n hn
  simp_rw [hsLengthSq_eq_two_sub_two_re_normTrace
    (R.model n) (R.model_nonempty n)]
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum]
  nlinarith

/-- The scheduled exact unitaries are asymptotically multiplicative in
operator norm. -/
theorem MovingCornerSchedule.map_multiplicative_eventually_op
    [Nontrivial G] {D : MovingCornerSetup G} (R : MovingCornerSchedule D)
    (g h : G) : ∀ eta : ℝ, 0 < eta → ∃ N, ∀ n ≥ N,
    ‖(R.map n (g * h) : Matrix (R.model n) (R.model n) ℂ) -
      (R.map n g : Matrix (R.model n) (R.model n) ℂ) * R.map n h‖ ≤
        eta := by
  intro eta heta
  obtain ⟨Nmul, hmul⟩ := D.multiplicative_eventually g h (eta / 2) (by
    linarith)
  obtain ⟨Ntol, htol⟩ := diagonalTolerance_eventually_le
    (show 0 < eta / 12 by linarith)
  let Ncode := max (R.code (g * h)) (max (R.code g) (R.code h))
  refine ⟨max Nmul (max Ntol Ncode), fun n hn ↦ ?_⟩
  have hnMul : Nmul ≤ n := by omega
  have hnTol : Ntol ≤ n := by omega
  have hnCode : Ncode ≤ n := by omega
  have hghActive : R.code (g * h) ≤ n := by dsimp [Ncode] at hnCode; omega
  have hgActive : R.code g ≤ n := by dsimp [Ncode] at hnCode; omega
  have hhActive : R.code h ≤ n := by dsimp [Ncode] at hnCode; omega
  let Wgh : Matrix (R.model n) (R.model n) ℂ := R.map n (g * h)
  let Wg : Matrix (R.model n) (R.model n) ℂ := R.map n g
  let Wh : Matrix (R.model n) (R.model n) ℂ := R.map n h
  let Cgh : Matrix (R.model n) (R.model n) ℂ :=
    movingCompression D.approximation.toOpAlmostRepresentation D.S D.cutoff (R.stage n) (g * h)
  let Cg : Matrix (R.model n) (R.model n) ℂ :=
    movingCompression D.approximation.toOpAlmostRepresentation D.S D.cutoff (R.stage n) g
  let Ch : Matrix (R.model n) (R.model n) ℂ :=
    movingCompression D.approximation.toOpAlmostRepresentation D.S D.cutoff (R.stage n) h
  have hclosegh : ‖Wgh - Cgh‖ ≤ 2 * diagonalTolerance n :=
    R.map_close_of_code_le n (g * h) hghActive
  have hcloseg : ‖Wg - Cg‖ ≤ 2 * diagonalTolerance n :=
    R.map_close_of_code_le n g hgActive
  have hcloseh : ‖Wh - Ch‖ ≤ 2 * diagonalTolerance n :=
    R.map_close_of_code_le n h hhActive
  have hcloseg' : ‖Cg - Wg‖ ≤ 2 * diagonalTolerance n := by
    rw [show Cg - Wg = -(Wg - Cg) by abel, norm_neg]
    exact hcloseg
  have hcloseh' : ‖Ch - Wh‖ ≤ 2 * diagonalTolerance n := by
    rw [show Ch - Wh = -(Wh - Ch) by abel, norm_neg]
    exact hcloseh
  have hdefect : ‖Cgh - Cg * Ch‖ ≤ eta / 2 := by
    exact hmul (R.stage n) (hnMul.trans (R.stage_ge n))
  letI : Nonempty (R.model n) :=
    Fintype.card_pos_iff.mp (R.model_nonempty n)
  have hWh : ‖Wh‖ = 1 :=
    CStarRing.norm_of_mem_unitary (R.map n h).2
  have hCg : ‖Cg‖ ≤ 1 :=
    norm_movingCompression_le_one D.approximation.toOpAlmostRepresentation D.S D.cutoff (R.stage n) g
  have htermg : ‖Cg - Wg‖ * ‖Wh‖ ≤
      (2 * diagonalTolerance n) * 1 :=
    mul_le_mul hcloseg' hWh.le (norm_nonneg _)
      (mul_nonneg (by norm_num) (diagonalTolerance_pos n).le)
  have htermh : ‖Cg‖ * ‖Ch - Wh‖ ≤
      1 * (2 * diagonalTolerance n) :=
    mul_le_mul hCg hcloseh' (norm_nonneg _) (by norm_num)
  have hbase := norm_mul_defect_of_perturbations Wgh Wg Wh Cgh Cg Ch
  have htolerance := htol n hnTol
  dsimp only [Wgh, Wg, Wh] at hbase ⊢
  nlinarith

/-- The scheduled polar corrections form an asymptotic unitary
representation in the sense consumed by the tracial ultraproduct. -/
noncomputable def MovingCornerSchedule.toAsymptoticUnitaryRepresentation
    [Nontrivial G] {D : MovingCornerSetup G} (R : MovingCornerSchedule D) :
    AsymptoticUnitaryRepresentation G where
  model := R.model
  modelNonempty := R.model_nonempty
  map := R.map
  asymptoticallyMultiplicative := by
    intro g h eta heta
    obtain ⟨N, hN⟩ := R.map_multiplicative_eventually_op g h
      (Real.sqrt eta) (Real.sqrt_pos.2 heta)
    refine ⟨N, fun n hn ↦ ?_⟩
    let E : Matrix (R.model n) (R.model n) ℂ :=
      (R.map n (g * h) : Matrix (R.model n) (R.model n) ℂ) -
        (R.map n g : Matrix (R.model n) (R.model n) ℂ) * R.map n h
    have hop : ‖E‖ ≤ Real.sqrt eta := hN n hn
    calc
      hsDistSq (R.model n) (R.map n (g * h))
          ((R.map n g : Matrix (R.model n) (R.model n) ℂ) * R.map n h) ≤
        ‖E‖ ^ 2 := hsDistSq_le_sq_l2_opNorm (R.model n) _ _
      _ ≤ (Real.sqrt eta) ^ 2 := by
        nlinarith [norm_nonneg E, Real.sqrt_nonneg eta]
      _ = eta := Real.sq_sqrt heta.le

/-- The canonical homomorphism represented by the scheduled polar-corrected
unitaries. -/
noncomputable def MovingCornerSchedule.hyperlinearHom
    [Nontrivial G] {D : MovingCornerSetup G} (R : MovingCornerSchedule D)
    {𝒰 : Ultrafilter ℕ} (hcof : (𝒰 : Filter ℕ) ≤ Filter.cofinite) :
    G →* UniversalHyperlinear 𝒰 R.model R.model_nonempty :=
  R.toAsymptoticUnitaryRepresentation.toUltraproductHom hcof

@[simp] theorem MovingCornerSchedule.hyperlinearHom_apply
    [Nontrivial G] {D : MovingCornerSetup G} (R : MovingCornerSchedule D)
    {𝒰 : Ultrafilter ℕ} (hcof : (𝒰 : Filter ℕ) ≤ Filter.cofinite)
    (g : G) :
    R.hyperlinearHom hcof g = QuotientGroup.mk (fun n ↦ R.map n g) := rfl

/-- The diagonal moving corner therefore induces a homomorphism into its
tracial matrix ultraproduct. -/
theorem MovingCornerSchedule.exists_hyperlinearHom
    [Nontrivial G] {D : MovingCornerSetup G} (R : MovingCornerSchedule D)
    {𝒰 : Ultrafilter ℕ} (hcof : (𝒰 : Filter ℕ) ≤ Filter.cofinite) :
    Nonempty (G →* UniversalHyperlinear 𝒰 R.model R.model_nonempty) :=
  ⟨R.hyperlinearHom hcof⟩

/-- The induced ultraproduct homomorphism is nontrivial on at least one
Kazhdan generator. -/
theorem MovingCornerSchedule.exists_generator_hyperlinearHom_ne_one
    [Nontrivial G] {D : MovingCornerSetup G} (R : MovingCornerSchedule D)
    {𝒰 : Ultrafilter ℕ} (hcof : (𝒰 : Filter ℕ) ≤ Filter.cofinite) :
    ∃ g ∈ D.S, R.hyperlinearHom hcof g ≠ 1 := by
  classical
  by_contra htrivial
  push Not at htrivial
  have hnull (g : G) (hg : g ∈ D.S) :
      IsNullUnitarySeq 𝒰 R.model (fun n ↦ R.map n g) := by
    have heq : (1 : UniversalHyperlinear 𝒰 R.model R.model_nonempty) =
        QuotientGroup.mk (fun n ↦ R.map n g) := by
      rw [← R.hyperlinearHom_apply hcof g]
      exact (htrivial g hg).symm
    change QuotientGroup.mk
      (1 : ∀ n, Matrix.unitaryGroup (R.model n) ℂ) =
        QuotientGroup.mk (fun n ↦ R.map n g) at heq
    have hmem := QuotientGroup.eq.mp heq
    have hmem' : (fun n ↦ R.map n g) ∈
        nullUnitarySubgroup 𝒰 R.model R.model_nonempty := by
      simpa only [inv_one, one_mul] using hmem
    exact hmem'
  let eta : ℝ := (1 - D.cutoff) / 2
  have heta : 0 < eta := by dsimp [eta]; linarith [D.cutoff_lt_one]
  have hallSmall : ∀ᶠ n in (𝒰 : Filter ℕ), ∀ g ∈ D.S,
      hsLengthSq (R.model n) (R.map n g) < eta := by
    rw [Finset.eventually_all]
    intro g hg
    exact hnull g hg eta heta
  have hsumSmall : ∀ᶠ n in (𝒰 : Filter ℕ),
      ∑ g ∈ D.S, hsLengthSq (R.model n) (R.map n g) <
        (D.S.card : ℝ) * (1 - D.cutoff) / 2 := by
    filter_upwards [hallSmall] with n hn
    calc
      ∑ g ∈ D.S, hsLengthSq (R.model n) (R.map n g) <
          ∑ _g ∈ D.S, eta :=
        Finset.sum_lt_sum_of_nonempty ⟨1, D.one_mem⟩ hn
      _ = (D.S.card : ℝ) * (1 - D.cutoff) / 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        dsimp [eta]
        ring
  obtain ⟨N, hN⟩ := R.generator_hsLengthSq_eventually_ge
  have hsumLarge : ∀ᶠ n in (𝒰 : Filter ℕ),
      (D.S.card : ℝ) * (1 - D.cutoff) ≤
        ∑ g ∈ D.S, hsLengthSq (R.model n) (R.map n g) :=
    eventually_of_atTop hcof N hN
  obtain ⟨n, hnLarge, hnSmall⟩ := (hsumLarge.and hsumSmall).exists
  have hcard : (0 : ℝ) < D.S.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, D.one_mem⟩
  nlinarith [D.cutoff_lt_one]

end KazhdanCornerMatrices
end GroupApproximation
