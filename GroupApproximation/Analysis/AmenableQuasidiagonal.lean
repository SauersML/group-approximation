import GroupApproximation.Sofic.NormTraceGap

/-!
# Why "amenable implies MF" needs quasidiagonality: permutation models are rigid
in operator norm

`non_mf_group_notes.tex` is edited concurrently, so the sites below are given
by `\label` and by quoted phrase; grep for the quotation, never for a line
number.  The implication *amenable `⟹` MF* occurs in three places:

* `\section{The cyclic comparison}\label{sec:necessity}`, paragraph
  *Sharpness of the Kazhdan hypothesis* --- grep `"hence MF by"`: the realized
  Clifford quotient of Theorem C "is a subgroup of this amenable group and is
  therefore amenable, hence MF by \cite{TWW}".  This is the load-bearing use;
* `\section{Consequences}\label{sec:consequences}` --- grep
  `"homomorphism to any countable"`: a group with saturated defect "admits no
  nontrivial ... homomorphism to any countable residually finite or amenable
  group".  Uncited, and it needs the general statement, not one group;
* the introduction --- grep `"quasidiagonality \cite{TWW}"`: survey prose
  listing classes for which the MF conjecture is known.  Not load-bearing.

The word *quasidiagonality* in the first of these is not decoration.  It marks
the exact point at which the implication stops being elementary, and this file
proves that in the sharpest available form.

## What is proved here

The naive elementary route to MF for an amenable group is the Følner route:
take a Følner set `A`, complete each left translation to a permutation of `A`
(the repository's `AmenableActionSofic.folnerPerm`), and use the resulting
permutation matrices as the finite-dimensional almost representation.  That
route produces *soficity*, because the Hamming defect of the completion is
controlled by the Følner boundary.  It cannot produce MF, and the obstruction
is not quantitative slack --- it is absolute:

* `one_le_l2_opNorm_permMatrix_sub`: two **distinct** permutation matrices are
  at `l²`-operator distance at least `1`;
* `l2_opNorm_permMatrix_sub_eq_zero_or_one_le` and
  `l2_opNorm_permMatrix_defect_eq_zero_or_one_le`: consequently the
  operator-norm distance between permutation matrices, and the operator-norm
  multiplicativity defect of a permutation model, take **no value strictly
  between `0` and `1`**;
* `one_le_l2_opNorm_permMatrix_sub_of_hammingDistance_pos` and
  `one_le_l2_opNorm_permMatrix_defect_of_hammingDistance_pos`: a *positive*
  normalized Hamming defect, however small, already forces operator-norm
  defect at least `1`.

So an operator-norm model whose unitaries are permutation matrices is
approximate only if it is exact.  Følner averaging buys nothing in operator
norm: `exists_hammingDistance_lt_and_one_le_l2_opNorm` exhibits, at every
accuracy `ε > 0`, a pair of permutations with normalized Hamming distance
below `ε` and operator-norm distance at least `1`.

This is the one-sidedness of `Sofic.NormTraceGap` pushed to the place where it
bites.  Operator-norm defects dominate Hilbert--Schmidt defects
(`hsDistSq_le_sq_l2_opNorm`); on permutation matrices the domination is
infinitely lossy in the other direction.

The group-level consequences --- that the permutation route certifies exactly
the LEF groups, and that it provably cannot certify the manuscript's realized
Clifford quotient --- are in `Algebra.AmenableMFProof`.

**This file does not prove "amenable implies MF", and nothing in this
repository does.**  What it proves is that the elementary route to it is
closed, so the manuscript's three uses rest on Tikuisis--White--Winter as a
genuine external input.
-/

namespace GroupApproximation

open Matrix
open scoped Matrix.Norms.L2Operator

/-! ## A single disagreeing coordinate -/

/-- At a coordinate where two permutations disagree, the difference of their
permutation matrices has an entry equal to `1`. -/
theorem permMatrix_sub_apply_of_ne (Y : FiniteModel) (σ τ : Equiv.Perm Y)
    {x : Y} (hx : σ x ≠ τ x) :
    (σ.permMatrix ℂ - τ.permMatrix ℂ) x (σ x) = 1 := by
  have h1 : (σ.permMatrix ℂ) x (σ x) = 1 := by
    rw [permMatrixC_entry]
    exact if_pos rfl
  have h2 : (τ.permMatrix ℂ) x (σ x) = 0 := by
    rw [permMatrixC_entry]
    exact if_neg (Ne.symm hx)
  rw [Matrix.sub_apply, h1, h2, sub_zero]

/-! ## The gap -/

/-- **Distinct permutation matrices are at operator-norm distance at least
`1`.**  A single disagreeing coordinate contributes a unit entry, and every
entry of a matrix is bounded by its operator norm. -/
theorem one_le_l2_opNorm_permMatrix_sub (Y : FiniteModel) {σ τ : Equiv.Perm Y}
    (h : σ ≠ τ) : 1 ≤ ‖σ.permMatrix ℂ - τ.permMatrix ℂ‖ := by
  have hne : ¬ ∀ x : Y, σ x = τ x := fun hall ↦ h (Equiv.ext hall)
  obtain ⟨x, hx⟩ := not_forall.mp hne
  have hentry :
      Complex.normSq ((σ.permMatrix ℂ - τ.permMatrix ℂ) x (σ x)) = 1 := by
    rw [permMatrix_sub_apply_of_ne Y σ τ hx]
    simp
  have hbound := normSq_entry_le_sq_l2_opNorm Y
    (σ.permMatrix ℂ - τ.permMatrix ℂ) x (σ x)
  rw [hentry] at hbound
  nlinarith [norm_nonneg (σ.permMatrix ℂ - τ.permMatrix ℂ)]

/-- **Rigidity.**  A permutation matrix has no other permutation matrix within
operator-norm distance `1`: approximation below the threshold is equality. -/
theorem eq_of_l2_opNorm_permMatrix_sub_lt_one (Y : FiniteModel)
    {σ τ : Equiv.Perm Y} (h : ‖σ.permMatrix ℂ - τ.permMatrix ℂ‖ < 1) :
    σ = τ := by
  by_contra hne
  exact absurd (one_le_l2_opNorm_permMatrix_sub Y hne) (not_le.mpr h)

/-- **The dichotomy.**  The operator-norm distance between two permutation
matrices is either `0` or at least `1`; it never lies strictly in between. -/
theorem l2_opNorm_permMatrix_sub_eq_zero_or_one_le (Y : FiniteModel)
    (σ τ : Equiv.Perm Y) :
    ‖σ.permMatrix ℂ - τ.permMatrix ℂ‖ = 0 ∨
      1 ≤ ‖σ.permMatrix ℂ - τ.permMatrix ℂ‖ := by
  by_cases h : σ = τ
  · left
    rw [h, sub_self, norm_zero]
  · right
    exact one_le_l2_opNorm_permMatrix_sub Y h

/-! ## Multiplicativity defects of permutation models -/

/-- `permMatrix` is an anti-homomorphism: the product of two permutation
matrices is the permutation matrix of the reversed product. -/
theorem permMatrix_mul_permMatrix (Y : FiniteModel) (σ τ : Equiv.Perm Y) :
    (σ.permMatrix ℂ) * (τ.permMatrix ℂ) = (τ * σ).permMatrix ℂ := by
  rw [Matrix.permMatrix_mul]

/-- **A permutation model with multiplicativity defect below `1` is exactly
multiplicative.** -/
theorem perm_mul_eq_of_l2_opNorm_defect_lt_one (Y : FiniteModel)
    {σ τ ρ : Equiv.Perm Y}
    (h : ‖(σ.permMatrix ℂ) * (τ.permMatrix ℂ) - ρ.permMatrix ℂ‖ < 1) :
    τ * σ = ρ := by
  rw [permMatrix_mul_permMatrix] at h
  exact eq_of_l2_opNorm_permMatrix_sub_lt_one Y h

/-- The multiplicativity defect of a permutation model vanishes exactly when
the model is an exact (anti-)homomorphism at that pair. -/
theorem l2_opNorm_permMatrix_defect_eq_zero_iff (Y : FiniteModel)
    (σ τ ρ : Equiv.Perm Y) :
    ‖(σ.permMatrix ℂ) * (τ.permMatrix ℂ) - ρ.permMatrix ℂ‖ = 0 ↔
      τ * σ = ρ := by
  rw [permMatrix_mul_permMatrix]
  constructor
  · intro h
    refine eq_of_l2_opNorm_permMatrix_sub_lt_one Y ?_
    rw [h]
    norm_num
  · rintro rfl
    rw [sub_self, norm_zero]

/-- **The dichotomy for defects.**  The operator-norm multiplicativity defect
of a permutation model is either `0` or at least `1`.  There is no regime of
small positive operator-norm defect for permutation matrices, and such a
regime is exactly what an MF model of a non-LEF group would have to
supply. -/
theorem l2_opNorm_permMatrix_defect_eq_zero_or_one_le (Y : FiniteModel)
    (σ τ ρ : Equiv.Perm Y) :
    ‖(σ.permMatrix ℂ) * (τ.permMatrix ℂ) - ρ.permMatrix ℂ‖ = 0 ∨
      1 ≤ ‖(σ.permMatrix ℂ) * (τ.permMatrix ℂ) - ρ.permMatrix ℂ‖ := by
  rw [permMatrix_mul_permMatrix]
  exact l2_opNorm_permMatrix_sub_eq_zero_or_one_le Y (τ * σ) ρ

/-! ## Hamming defects do not become operator-norm defects

The Følner construction controls the *Hamming* defect of a completed
translation.  These two statements say that this control is worth nothing in
operator norm. -/

/-- **A positive Hamming defect, however small, forces operator-norm distance
at least `1`.** -/
theorem one_le_l2_opNorm_permMatrix_sub_of_hammingDistance_pos
    (Y : FiniteModel) {σ τ : Equiv.Perm Y} (h : 0 < hammingDistance Y σ τ) :
    1 ≤ ‖σ.permMatrix ℂ - τ.permMatrix ℂ‖ := by
  refine one_le_l2_opNorm_permMatrix_sub Y ?_
  rintro rfl
  rw [hammingDistance_self] at h
  exact lt_irrefl 0 h

/-- The same statement for multiplicativity defects: a Følner-style model with
*any* positive Hamming multiplicativity defect has operator-norm
multiplicativity defect at least `1`. -/
theorem one_le_l2_opNorm_permMatrix_defect_of_hammingDistance_pos
    (Y : FiniteModel) {σ τ ρ : Equiv.Perm Y}
    (h : 0 < hammingDistance Y (τ * σ) ρ) :
    1 ≤ ‖(σ.permMatrix ℂ) * (τ.permMatrix ℂ) - ρ.permMatrix ℂ‖ := by
  rw [permMatrix_mul_permMatrix]
  exact one_le_l2_opNorm_permMatrix_sub_of_hammingDistance_pos Y h

/-! ## The separation is realized, not merely possible

A transposition of a large finite set is Hamming-close to the identity and
operator-norm-far from it.  Without this, the dichotomy above would be
consistent with the two metrics never actually separating. -/

/-- A transposition disagrees with the identity exactly at the two transposed
points. -/
theorem hammingDisagreement_one_swap (Y : FiniteModel) {a b : Y} (hab : a ≠ b) :
    hammingDisagreement (1 : Equiv.Perm Y) (Equiv.swap a b) =
      ({a, b} : Finset Y) := by
  ext y
  simp only [mem_hammingDisagreement, Equiv.Perm.coe_one, id_eq,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hy
    by_contra hcon
    push Not at hcon
    exact hy (Equiv.swap_apply_of_ne_of_ne hcon.1 hcon.2).symm
  · rintro (rfl | rfl)
    · rw [Equiv.swap_apply_left]
      exact hab
    · rw [Equiv.swap_apply_right]
      exact Ne.symm hab

/-- The normalized Hamming distance from the identity to a transposition is
`2` over the size of the model: it tends to zero as the model grows. -/
theorem hammingDistance_one_swap (Y : FiniteModel) {a b : Y} (hab : a ≠ b) :
    hammingDistance Y (1 : Equiv.Perm Y) (Equiv.swap a b) =
      2 / (Fintype.card Y : ℝ) := by
  unfold hammingDistance
  rw [hammingDisagreement_one_swap Y hab, Finset.card_pair hab]
  norm_num

/-- The transposition witness at a fixed model: Hamming-close to the identity
once the model is large, operator-norm-far from it always. -/
theorem hammingDistance_lt_and_one_le_l2_opNorm_swap
    (Y : FiniteModel) {a b : Y} (hab : a ≠ b) {ε : ℝ}
    (hsmall : 2 / (Fintype.card Y : ℝ) < ε) :
    hammingDistance Y (1 : Equiv.Perm Y) (Equiv.swap a b) < ε ∧
      1 ≤ ‖(1 : Equiv.Perm Y).permMatrix ℂ -
        (Equiv.swap a b).permMatrix ℂ‖ := by
  refine ⟨?_, ?_⟩
  · rw [hammingDistance_one_swap Y hab]
    exact hsmall
  · refine one_le_l2_opNorm_permMatrix_sub Y ?_
    intro hcontra
    have happ := Equiv.Perm.congr_fun hcontra a
    rw [Equiv.swap_apply_left] at happ
    exact hab happ

/-- **The two metrics separate at every accuracy.**  For every `ε > 0` there is
a finite model and a pair of permutations of it whose normalized Hamming
distance is below `ε` while their permutation matrices stay at operator-norm
distance at least `1`.

This is the precise sense in which the Følner route to MF fails: soficity's
accuracy parameter can be driven to zero with the operator-norm defect pinned
at `1`. -/
theorem exists_hammingDistance_lt_and_one_le_l2_opNorm {ε : ℝ} (hε : 0 < ε) :
    ∃ (Y : FiniteModel) (σ τ : Equiv.Perm Y),
      hammingDistance Y σ τ < ε ∧
        1 ≤ ‖σ.permMatrix ℂ - τ.permMatrix ℂ‖ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / ε)
  have hnε : (2 : ℝ) < (n : ℝ) * ε := (div_lt_iff₀ hε).mp hn
  have h0 : (0 : ℕ) < n + 2 := by omega
  have h1 : (1 : ℕ) < n + 2 := by omega
  have hab : (⟨0, h0⟩ : Fin (n + 2)) ≠ ⟨1, h1⟩ := by
    intro hcontra
    have hval : (0 : ℕ) = 1 := congrArg Fin.val hcontra
    exact absurd hval (by omega)
  have hcardnat :
      Fintype.card
          (⟨Fin (n + 2), inferInstance, inferInstance⟩ : FiniteModel) = n + 2 :=
    Fintype.card_fin (n + 2)
  have hsmall :
      2 / (Fintype.card
          (⟨Fin (n + 2), inferInstance, inferInstance⟩ : FiniteModel) : ℝ)
        < ε := by
    rw [hcardnat]
    have hpos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by exact_mod_cast h0
    rw [div_lt_iff₀ hpos]
    push_cast
    nlinarith
  exact ⟨(⟨Fin (n + 2), inferInstance, inferInstance⟩ : FiniteModel), _, _,
    hammingDistance_lt_and_one_le_l2_opNorm_swap
      (⟨Fin (n + 2), inferInstance, inferInstance⟩ : FiniteModel) hab hsmall⟩

end GroupApproximation
