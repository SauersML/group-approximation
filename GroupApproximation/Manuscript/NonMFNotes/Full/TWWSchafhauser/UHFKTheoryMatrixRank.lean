import GroupApproximation.KTheory.MatrixProjection
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Projections in `M_N(ℂ)` are classified by their trace

Lane `TWWSch3d2Q1` (work order `WO-TWWSch-3d2-Q1`).  Manuscript:
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378), through
C. Schafhauser, *A new proof of the Tikuisis--White--Winter theorem*, J. reine
angew. Math. **759** (2020), §4.  This is the finite-dimensional input to the
minimal `K`-theory of the universal UHF algebra `Q` (Glimm, Trans. AMS **95**
(1960); Rørdam--Larsen--Laustsen, *An introduction to K-theory for
C⋆-algebras*, Prop. 2.2.2 and Ex. 3.4; Davidson, *C⋆-algebras by example*, III.5).

A projection `p ∈ M_N(ℂ)` is unitarily diagonalised by the spectral theorem,
`p = U D U*` with `D = diag(λ₀ ∘ e⁻¹)`.  Here `λ₀ : Fin N → ℝ` is antitone, and
its values lie in `{0, 1}` because `D` is again a projection.  An antitone
`{0,1}`-valued sequence is determined by its sum.  So two projections with the
same trace have literally the same diagonal `D`, and `D * U*` implements
`p ∼ D`.

## Main declarations

* `uhfK_antitone_zero_one_eq`: an antitone `{0,1}`-sequence is fixed by its sum;
* `uhfK_eigenvalues_zero_or_one`, `uhfK_trace_eq_natCast`;
* `uhfK_murrayVonNeumannEquiv_of_trace_eq`: equal trace ⇒ Murray--von Neumann
  equivalent, in `M_N(ℂ)`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open Matrix Unitary

/-- An antitone `{0,1}`-valued sequence is determined by its sum (the counting
step behind RLL Ex. 3.4, `thm:fixed-radical-membership` in
`non_mf_group_notes.tex`). -/
theorem uhfK_antitone_zero_one_eq {N : ℕ} {f g : Fin N → ℝ} (hf : Antitone f)
    (hg : Antitone g) (hf01 : ∀ i, f i = 0 ∨ f i = 1) (hg01 : ∀ i, g i = 0 ∨ g i = 1)
    (hsum : ∑ i, f i = ∑ i, g i) : f = g := by
  have key : ∀ {f g : Fin N → ℝ}, Antitone f → Antitone g → (∀ i, f i = 0 ∨ f i = 1) →
      (∀ i, g i = 0 ∨ g i = 1) → ∑ i, f i = ∑ i, g i → ∀ i, f i = 1 → g i = 0 → False := by
    intro f g hf hg hf01 hg01 hsum i hfi hgi
    have hle : ∀ j ∈ Finset.univ, g j ≤ f j := by
      intro j _
      rcases le_total j i with hji | hij
      · have h1 := hf hji
        rcases hg01 j with h | h <;> linarith
      · have h1 := hg hij
        rcases hf01 j with h | h <;> linarith
    have hlt : ∃ j ∈ Finset.univ, g j < f j :=
      ⟨i, Finset.mem_univ _, by rw [hfi, hgi]; norm_num⟩
    exact (Finset.sum_lt_sum hle hlt).ne hsum.symm
  funext i
  rcases hf01 i with h | h
  · rcases hg01 i with h' | h'
    · rw [h, h']
    · exact (key hg hf hg01 hf01 hsum.symm i h' h).elim
  · rcases hg01 i with h' | h'
    · exact (key hf hg hf01 hg01 hsum i h h').elim
    · rw [h, h']

section Matrices

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A projection of `M_N(ℂ)` is Hermitian. -/
theorem uhfK_isHermitian {p : Matrix n n ℂ} (hp : IsStarProjection p) : p.IsHermitian :=
  Matrix.isHermitian_iff_isSelfAdjoint.2 hp.isSelfAdjoint

/-- The diagonal of the spectral decomposition of a projection is a projection
(`thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem uhfK_diagonal_isStarProjection {p : Matrix n n ℂ} (hp : IsStarProjection p)
    (hA : p.IsHermitian) :
    IsStarProjection (diagonal (RCLike.ofReal ∘ hA.eigenvalues) : Matrix n n ℂ) := by
  rw [← hA.conjStarAlgAut_star_eigenvectorUnitary]
  exact hp.map _

/-- The eigenvalues of a projection are `0` or `1`. -/
theorem uhfK_eigenvalues_zero_or_one {p : Matrix n n ℂ} (hp : IsStarProjection p)
    (hA : p.IsHermitian) (i : n) : hA.eigenvalues i = 0 ∨ hA.eigenvalues i = 1 := by
  have h := (uhfK_diagonal_isStarProjection hp hA).isIdempotentElem.eq
  rw [diagonal_mul_diagonal] at h
  have hi := congrFun (diagonal_injective h) i
  simp only [Function.comp_apply] at hi
  have hi' : hA.eigenvalues i * hA.eigenvalues i = hA.eigenvalues i := by exact_mod_cast hi
  have h2 : hA.eigenvalues i * (hA.eigenvalues i - 1) = 0 := by
    rw [mul_sub, mul_one, hi', sub_self]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact Or.inl h3
  · exact Or.inr (sub_eq_zero.1 h3)

/-- The ordered eigenvalues `λ₀` of a projection are `0` or `1`. -/
theorem uhfK_eigenvalues₀_zero_or_one {p : Matrix n n ℂ} (hp : IsStarProjection p)
    (hA : p.IsHermitian) (j : Fin (Fintype.card n)) :
    hA.eigenvalues₀ j = 0 ∨ hA.eigenvalues₀ j = 1 := by
  have h := uhfK_eigenvalues_zero_or_one hp hA
    (Fintype.equivOfCardEq (α := Fin (Fintype.card n)) (β := n) (Fintype.card_fin _) j)
  simpa only [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply] using h

/-- The two indexings of the eigenvalues have the same sum. -/
theorem uhfK_sum_eigenvalues_eq_sum_eigenvalues₀ {p : Matrix n n ℂ} (hA : p.IsHermitian) :
    ∑ i, hA.eigenvalues i = ∑ j, hA.eigenvalues₀ j :=
  Equiv.sum_comp (Fintype.equivOfCardEq (α := Fin (Fintype.card n)) (β := n)
    (Fintype.card_fin _)).symm hA.eigenvalues₀

/-- **The trace of a projection is its rank**, a natural number at most `N`. -/
theorem uhfK_trace_eq_natCast {p : Matrix n n ℂ} (hp : IsStarProjection p) :
    ∃ r : ℕ, r ≤ Fintype.card n ∧ p.trace = (r : ℂ) := by
  have hA := uhfK_isHermitian hp
  classical
  refine ⟨#{i | hA.eigenvalues i = 1}, ?_, ?_⟩
  · exact Finset.card_le_univ _
  · rw [hA.trace_eq_sum_eigenvalues, ← Finset.sum_boole]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases uhfK_eigenvalues_zero_or_one hp hA i with h | h
    · rw [if_neg (by rw [h]; norm_num), h]
      simp
    · rw [if_pos h, h]
      simp

/-- A projection conjugated from `d` by a unitary is equivalent to `d`, implemented
by `d * U*`. -/
theorem uhfK_murrayVonNeumannEquiv_of_eq_conj {A : Type*} [Semiring A] [StarRing A]
    {p d U : A} (hU : star U * U = 1) (hd : IsStarProjection d) (hspec : p = U * d * star U) :
    MurrayVonNeumannEquiv p d := by
  refine ⟨d * star U, ?_, ?_⟩
  · rw [star_mul, star_star, hd.isSelfAdjoint.star_eq]
    calc U * d * (d * star U) = U * (d * d) * star U := by simp only [mul_assoc]
      _ = p := by rw [hd.isIdempotentElem.eq]; exact hspec.symm
  · rw [star_mul, star_star, hd.isSelfAdjoint.star_eq]
    calc d * star U * (U * d) = d * (star U * U) * d := by simp only [mul_assoc]
      _ = d := by rw [hU, mul_one, hd.isIdempotentElem.eq]

/-- A projection is equivalent to the diagonal of its spectral decomposition. -/
theorem uhfK_murrayVonNeumannEquiv_diagonal {p : Matrix n n ℂ} (hp : IsStarProjection p)
    (hA : p.IsHermitian) :
    MurrayVonNeumannEquiv p (diagonal (RCLike.ofReal ∘ hA.eigenvalues) : Matrix n n ℂ) := by
  have hspec := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  exact uhfK_murrayVonNeumannEquiv_of_eq_conj (Unitary.coe_star_mul_self _)
    (uhfK_diagonal_isStarProjection hp hA) hspec

/-- **Projections of `M_N(ℂ)` with equal trace are Murray--von Neumann
equivalent** (RLL Ex. 3.4; `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
theorem uhfK_murrayVonNeumannEquiv_of_trace_eq {p q : Matrix n n ℂ}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (h : p.trace = q.trace) :
    MurrayVonNeumannEquiv p q := by
  have hA := uhfK_isHermitian hp
  have hB := uhfK_isHermitian hq
  rw [hA.trace_eq_sum_eigenvalues, hB.trace_eq_sum_eigenvalues] at h
  have h' : ∑ i, hA.eigenvalues i = ∑ i, hB.eigenvalues i := by exact_mod_cast h
  rw [uhfK_sum_eigenvalues_eq_sum_eigenvalues₀, uhfK_sum_eigenvalues_eq_sum_eigenvalues₀] at h'
  have h0 : hA.eigenvalues₀ = hB.eigenvalues₀ :=
    uhfK_antitone_zero_one_eq hA.eigenvalues₀_antitone hB.eigenvalues₀_antitone
      (uhfK_eigenvalues₀_zero_or_one hp hA) (uhfK_eigenvalues₀_zero_or_one hq hB) h'
  have hev : hA.eigenvalues = hB.eigenvalues := funext fun _ => congrFun h0 _
  have hDp := uhfK_murrayVonNeumannEquiv_diagonal hp hA
  have hDq := uhfK_murrayVonNeumannEquiv_diagonal hq hB
  rw [hev] at hDp
  exact hDp.trans hp.isIdempotentElem hq.isIdempotentElem hDq.symm

end Matrices

end GroupApproximation.Full.TWWSchafhauser
