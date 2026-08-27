import GroupApproximation.Sofic.KazhdanCornerModel
import GroupApproximation.Sofic.ExteriorMFProfile

/-!
# The first-order language of the ordered field of reals, and the printed
semialgebraic norm conditions

This module supplies the two ingredients the printed proof of
`prop:mf-upper-bound` uses to make its matrix condition `Φ(P,n,c)` decidable:

* the **syntax** of the first-order theory of the ordered field of real
  numbers (`RealTerm`, `RealFormula`) with its Tarski semantics
  (`RealFormula.Holds`), and Tarski's decidability theorem over that syntax
  carried as the hypothesis structure `TarskiInput` (the lane's only cited
  input);
* the **semialgebraic form** of the three conditions the printed proof
  imposes.  Unitarity is a system of polynomial equations in the real
  coordinates (`mem_unitaryGroup_iff_entry_equations` together with
  `star_mul_re_im`); a bound `‖X‖ ≤ t` is the nonnegativity of a quadratic
  form (`l2_opNorm_le_iff_quadraticForm_nonneg`); and a bound `‖X‖ ≥ t` is the
  existence of a unit vector (`le_l2_opNorm_iff_exists_unit_vector`).

The second of those needs the operator norm of a matrix on a nonempty finite
index set to be *attained*.  That is `exists_unit_vector_attaining_l2_opNorm`,
proved here with no open leaves from the repository's spectral input
`exists_eigenvalue_mul_conjTranspose_eq_sq_opNorm`: the eigenvector of `X^*X`
for its top eigenvalue `‖X‖²` is the required unit vector.

Printed sentences covered: `a0d0247bea30`, `9f1f2f176f18`, and the second
clause of `9eae4d68673a`.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace Certificates

open Matrix

open scoped Matrix Matrix.Norms.L2Operator

/-! ## Terms -/

/-- Terms of the first-order language of ordered fields: variables indexed by
`ℕ`, integer constants, and the ring operations.  Rational constants are not
needed: every rational quantity in the printed proof is cleared by multiplying
the corresponding polynomial inequality by a positive integer. -/
inductive RealTerm : Type
  | var : ℕ → RealTerm
  | const : ℤ → RealTerm
  | add : RealTerm → RealTerm → RealTerm
  | neg : RealTerm → RealTerm
  | mul : RealTerm → RealTerm → RealTerm
  deriving Inhabited

/-- The value of a term under an assignment of reals to the variables. -/
noncomputable def RealTerm.eval (ρ : ℕ → ℝ) : RealTerm → ℝ
  | RealTerm.var i => ρ i
  | RealTerm.const m => (m : ℝ)
  | RealTerm.add s t => RealTerm.eval ρ s + RealTerm.eval ρ t
  | RealTerm.neg s => -RealTerm.eval ρ s
  | RealTerm.mul s t => RealTerm.eval ρ s * RealTerm.eval ρ t

@[simp] theorem RealTerm.eval_var (ρ : ℕ → ℝ) (i : ℕ) :
    (RealTerm.var i).eval ρ = ρ i := rfl

@[simp] theorem RealTerm.eval_const (ρ : ℕ → ℝ) (m : ℤ) :
    (RealTerm.const m).eval ρ = (m : ℝ) := rfl

@[simp] theorem RealTerm.eval_add (ρ : ℕ → ℝ) (s t : RealTerm) :
    (RealTerm.add s t).eval ρ = s.eval ρ + t.eval ρ := rfl

@[simp] theorem RealTerm.eval_neg (ρ : ℕ → ℝ) (s : RealTerm) :
    (RealTerm.neg s).eval ρ = -s.eval ρ := rfl

@[simp] theorem RealTerm.eval_mul (ρ : ℕ → ℝ) (s t : RealTerm) :
    (RealTerm.mul s t).eval ρ = s.eval ρ * t.eval ρ := rfl

/-- The sum of a list of terms. -/
def RealTerm.sumList : List RealTerm → RealTerm
  | [] => RealTerm.const 0
  | t :: rest => RealTerm.add t (RealTerm.sumList rest)

theorem RealTerm.eval_sumList (ρ : ℕ → ℝ) :
    ∀ l : List RealTerm,
      (RealTerm.sumList l).eval ρ = (l.map fun t => t.eval ρ).sum
  | [] => by simp [RealTerm.sumList]
  | t :: rest => by simp [RealTerm.sumList, RealTerm.eval_sumList ρ rest]

/-! ## Formulas -/

/-- Formulas of the first-order language of the ordered field of reals.  Atoms
are polynomial equations and polynomial inequalities; the quantifiers bind a
named variable. -/
inductive RealFormula : Type
  | eqZero : RealTerm → RealFormula
  | leZero : RealTerm → RealFormula
  | and : RealFormula → RealFormula → RealFormula
  | or : RealFormula → RealFormula → RealFormula
  | not : RealFormula → RealFormula
  | ex : ℕ → RealFormula → RealFormula
  | all : ℕ → RealFormula → RealFormula
  deriving Inhabited

/-- Tarski satisfaction of a formula under an assignment. -/
def RealFormula.Holds (ρ : ℕ → ℝ) : RealFormula → Prop
  | RealFormula.eqZero t => t.eval ρ = 0
  | RealFormula.leZero t => t.eval ρ ≤ 0
  | RealFormula.and φ ψ => RealFormula.Holds ρ φ ∧ RealFormula.Holds ρ ψ
  | RealFormula.or φ ψ => RealFormula.Holds ρ φ ∨ RealFormula.Holds ρ ψ
  | RealFormula.not φ => ¬ RealFormula.Holds ρ φ
  | RealFormula.ex i φ => ∃ r : ℝ, RealFormula.Holds (Function.update ρ i r) φ
  | RealFormula.all i φ => ∀ r : ℝ, RealFormula.Holds (Function.update ρ i r) φ

@[simp] theorem RealFormula.holds_eqZero (ρ : ℕ → ℝ) (t : RealTerm) :
    (RealFormula.eqZero t).Holds ρ ↔ t.eval ρ = 0 := Iff.rfl

@[simp] theorem RealFormula.holds_leZero (ρ : ℕ → ℝ) (t : RealTerm) :
    (RealFormula.leZero t).Holds ρ ↔ t.eval ρ ≤ 0 := Iff.rfl

@[simp] theorem RealFormula.holds_and (ρ : ℕ → ℝ) (φ ψ : RealFormula) :
    (RealFormula.and φ ψ).Holds ρ ↔ φ.Holds ρ ∧ ψ.Holds ρ := Iff.rfl

@[simp] theorem RealFormula.holds_or (ρ : ℕ → ℝ) (φ ψ : RealFormula) :
    (RealFormula.or φ ψ).Holds ρ ↔ φ.Holds ρ ∨ ψ.Holds ρ := Iff.rfl

@[simp] theorem RealFormula.holds_not (ρ : ℕ → ℝ) (φ : RealFormula) :
    (RealFormula.not φ).Holds ρ ↔ ¬ φ.Holds ρ := Iff.rfl

@[simp] theorem RealFormula.holds_ex (ρ : ℕ → ℝ) (i : ℕ) (φ : RealFormula) :
    (RealFormula.ex i φ).Holds ρ ↔ ∃ r : ℝ, φ.Holds (Function.update ρ i r) :=
  Iff.rfl

@[simp] theorem RealFormula.holds_all (ρ : ℕ → ℝ) (i : ℕ) (φ : RealFormula) :
    (RealFormula.all i φ).Holds ρ ↔ ∀ r : ℝ, φ.Holds (Function.update ρ i r) :=
  Iff.rfl

/-- The conjunction of a list of formulas. -/
def RealFormula.andList : List RealFormula → RealFormula
  | [] => RealFormula.eqZero (RealTerm.const 0)
  | φ :: rest => RealFormula.and φ (RealFormula.andList rest)

theorem RealFormula.holds_andList (ρ : ℕ → ℝ) :
    ∀ l : List RealFormula,
      (RealFormula.andList l).Holds ρ ↔ ∀ φ ∈ l, φ.Holds ρ
  | [] => by simp [RealFormula.andList]
  | φ :: rest => by
      simp only [RealFormula.andList, RealFormula.holds_and,
        RealFormula.holds_andList ρ rest, List.mem_cons]
      constructor
      · rintro ⟨hφ, hrest⟩ ψ (rfl | hψ)
        · exact hφ
        · exact hrest ψ hψ
      · intro h
        exact ⟨h φ (Or.inl rfl), fun ψ hψ => h ψ (Or.inr hψ)⟩

/-- Existential quantification over a list of variable indices. -/
def RealFormula.exList : List ℕ → RealFormula → RealFormula
  | [], φ => φ
  | i :: rest, φ => RealFormula.ex i (RealFormula.exList rest φ)

/-- Universal quantification over a list of variable indices. -/
def RealFormula.allList : List ℕ → RealFormula → RealFormula
  | [], φ => φ
  | i :: rest, φ => RealFormula.all i (RealFormula.allList rest φ)

theorem RealFormula.holds_exList (φ : RealFormula) :
    ∀ (l : List ℕ) (ρ : ℕ → ℝ),
      (RealFormula.exList l φ).Holds ρ ↔
        ∃ σ : ℕ → ℝ, (∀ j, j ∉ l → σ j = ρ j) ∧ φ.Holds σ := by
  intro l
  induction l with
  | nil =>
      intro ρ
      constructor
      · intro h
        exact ⟨ρ, fun _ _ => rfl, h⟩
      · rintro ⟨σ, hσ, hφ⟩
        have hσρ : σ = ρ := funext fun j => hσ j (by simp)
        rw [hσρ] at hφ
        exact hφ
  | cons i rest ih =>
      intro ρ
      constructor
      · rintro ⟨r, hr⟩
        obtain ⟨σ, hσ, hφ⟩ := (ih (Function.update ρ i r)).1 hr
        refine ⟨σ, ?_, hφ⟩
        intro j hj
        rw [List.mem_cons] at hj
        push_neg at hj
        rw [hσ j hj.2, Function.update_apply, if_neg hj.1]
      · rintro ⟨σ, hσ, hφ⟩
        refine ⟨σ i, (ih (Function.update ρ i (σ i))).2 ⟨σ, ?_, hφ⟩⟩
        intro j hj
        by_cases hji : j = i
        · subst hji
          rw [Function.update_apply, if_pos rfl]
        · rw [Function.update_apply, if_neg hji]
          refine hσ j ?_
          rw [List.mem_cons]
          push_neg
          exact ⟨hji, hj⟩

theorem RealFormula.holds_allList (φ : RealFormula) :
    ∀ (l : List ℕ) (ρ : ℕ → ℝ),
      (RealFormula.allList l φ).Holds ρ ↔
        ∀ σ : ℕ → ℝ, (∀ j, j ∉ l → σ j = ρ j) → φ.Holds σ := by
  intro l
  induction l with
  | nil =>
      intro ρ
      constructor
      · intro h σ hσ
        have hσρ : σ = ρ := funext fun j => hσ j (by simp)
        rw [hσρ]
        exact h
      · intro h
        exact h ρ fun _ _ => rfl
  | cons i rest ih =>
      intro ρ
      constructor
      · intro h σ hσ
        refine (ih (Function.update ρ i (σ i))).1 (h (σ i)) σ ?_
        intro j hj
        by_cases hji : j = i
        · subst hji
          rw [Function.update_apply, if_pos rfl]
        · rw [Function.update_apply, if_neg hji]
          refine hσ j ?_
          rw [List.mem_cons]
          push_neg
          exact ⟨hji, hj⟩
      · intro h r
        refine (ih (Function.update ρ i r)).2 fun σ hσ => h σ ?_
        intro j hj
        rw [List.mem_cons] at hj
        push_neg at hj
        rw [hσ j hj.2, Function.update_apply, if_neg hj.1]

/-! ## Tarski's theorem, as an explicit hypothesis -/

-- LITERATURE INPUT (assumed): Tarski, quantifier elimination for real closed
-- fields (A Decision Method for Elementary Algebra and Geometry, 1951).
/-- **Tarski's theorem**, carried as a hypothesis rather than proved.  Its two
fields are the cited statement, one for one: a decision procedure for formulas
of the first-order theory of the ordered field of real numbers, and its
correctness at the zero assignment --- the only assignment the printed proof
evaluates at, since `Φ(P,n,c)` binds all of its variables.

Nothing here is proved and nothing here is postulated.  A consumer that wants
the manuscript's conclusion takes a term of this structure as an argument, so
every theorem downstream carries the citation visibly in its own statement. -/
structure TarskiInput where
  /-- The decision procedure supplied by quantifier elimination. -/
  decideFormula : RealFormula → Bool
  /-- It decides truth at the zero assignment. -/
  decideFormula_iff :
    ∀ φ : RealFormula, decideFormula φ = true ↔ φ.Holds fun _ => 0

/-! ## Complex scalars, entrywise -/

variable {Y : Type} [Fintype Y] [DecidableEq Y]

/-- The squared modulus as a complex product.  Used to turn every entrywise
sum of squared moduli into a matrix entry. -/
theorem ofReal_normSq (z : ℂ) : ((Complex.normSq z : ℝ) : ℂ) = star z * z := by
  rw [Complex.star_def, mul_comm, Complex.mul_conj]

/-- The diagonal entry of `Aᴴ * A` is the squared mass of the `i`-th column. -/
theorem column_mass_eq (A : Matrix Y Y ℂ) (i : Y) :
    ((∑ y : Y, Complex.normSq (A y i) : ℝ) : ℂ) = (Aᴴ * A) i i := by
  rw [Complex.ofReal_sum, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Matrix.conjTranspose_apply, ofReal_normSq]

/-- The `i`-th column of a matrix is `A *ᵥ e_i`, entrywise. -/
theorem mulVec_column (A B : Matrix Y Y ℂ) (i : Y) (y : Y) :
    (A *ᵥ fun l => B l i) y = (A * B) y i := by
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-! ## Unitarity as a system of polynomial equations -/

/-- `prop:mf-upper-bound`, proof sentence `a0d0247bea30`, first clause:
"unitarity is a system of polynomial equations".  One equation for each
ordered pair of column indices, each a quadratic in the matrix entries. -/
theorem mem_unitaryGroup_iff_entry_equations (U : Matrix Y Y ℂ) :
    U ∈ Matrix.unitaryGroup Y ℂ ↔
      ∀ p q : Y, ∑ l : Y, star (U l p) * U l q
        = if p = q then (1 : ℂ) else 0 := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  constructor
  · intro h p q
    have hpq := congrArg (fun M : Matrix Y Y ℂ => M p q) h
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
      using hpq
  · intro h
    ext p q
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
      using h p q

/-- `prop:mf-upper-bound`, proof sentence `a0d0247bea30`, second clause:
"Writing `U_j = A_j + i B_j` with real matrices", each entry equation of
`mem_unitaryGroup_iff_entry_equations` splits into two **real polynomial**
equations in the coordinates `A_j`, `B_j`: the real and imaginary parts of
`conj z * w` are the two displayed real quadratic forms in the coordinates of
`z` and `w`. -/
theorem star_mul_re_im (z w : ℂ) :
    (star z * w).re = z.re * w.re + z.im * w.im ∧
      (star z * w).im = z.re * w.im - z.im * w.re := by
  have hre : (star z).re = z.re := by simp
  have him : (star z).im = -z.im := by simp
  refine ⟨?_, ?_⟩
  · rw [Complex.mul_re, hre, him]
    ring
  · rw [Complex.mul_im, hre, him]
    ring

/-! ## The two semialgebraic norm conditions -/

/-- `prop:mf-upper-bound`, proof sentence `9f1f2f176f18`, first clause:
"`‖X‖ ≤ t` holds precisely when `t² - X^*X` is positive semidefinite".

Positive semidefiniteness of `t² - X^*X` is the nonnegativity of the quadratic
form `v ↦ t²‖v‖² - ‖Xv‖²`, a polynomial in the real coordinates of `v` and of
`X`; that is the form in which the condition enters the first-order
sentence. -/
theorem l2_opNorm_le_iff_quadraticForm_nonneg (X : Matrix Y Y ℂ) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖X‖ ≤ t ↔ ∀ v : Y → ℂ,
      0 ≤ t ^ 2 * (∑ i : Y, Complex.normSq (v i)) -
        ∑ i : Y, Complex.normSq ((X *ᵥ v) i) := by
  constructor
  · intro hX v
    have hle := KazhdanCornerMatrices.sum_normSq_mulVec_le_general X v
    have h0 : (0 : ℝ) ≤ ‖X‖ := norm_nonneg X
    have hsq : ‖X‖ ^ 2 ≤ t ^ 2 := by nlinarith
    have hnn : (0 : ℝ) ≤ ∑ i : Y, Complex.normSq (v i) :=
      Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (v i)
    nlinarith
  · intro h
    refine KazhdanCornerMatrices.l2_opNorm_le_of_sum_normSq_general X ht
      fun v => ?_
    have hv := h v
    linarith

/-- **The operator norm is attained on the unit sphere.**  The eigenvector of
`X^*X` belonging to its top eigenvalue `‖X‖²` is a unit vector on which the
squared mass of `Xv` is exactly `‖X‖²`.

No open leaves: the spectral input is the repository's
`exists_eigenvalue_mul_conjTranspose_eq_sq_opNorm`. -/
theorem exists_unit_vector_attaining_l2_opNorm (hY : Nonempty Y)
    (X : Matrix Y Y ℂ) :
    ∃ v : Y → ℂ, (∑ y : Y, Complex.normSq (v y)) = 1 ∧
      ‖X‖ ^ 2 ≤ ∑ y : Y, Complex.normSq ((X *ᵥ v) y) := by
  letI : Nonempty Y := hY
  set D : Matrix Y Y ℂ := Xᴴ with hDdef
  set H : Matrix Y Y ℂ := D * Dᴴ with hHdef
  let hH : H.IsHermitian := Matrix.isHermitian_mul_conjTranspose_self D
  let V : Matrix Y Y ℂ := hH.eigenvectorUnitary
  obtain ⟨i, hi⟩ :=
    exists_eigenvalue_mul_conjTranspose_eq_sq_opNorm D inferInstance
  have hVV : Vᴴ * V = 1 :=
    Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  have hdiag : Vᴴ * H * V =
      Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
    have hspec : H =
        V * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) * Vᴴ :=
      hH.spectral_theorem
    calc
      Vᴴ * H * V = Vᴴ *
          (V * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) * Vᴴ) * V :=
        congrArg (fun K : Matrix Y Y ℂ ↦ Vᴴ * K * V) hspec
      _ = (Vᴴ * V) * Matrix.diagonal
          (RCLike.ofReal ∘ hH.eigenvalues) * (Vᴴ * V) := by
        noncomm_ring
      _ = Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
        rw [hVV, Matrix.one_mul, Matrix.mul_one]
  have hHX : H = Xᴴ * X := by
    rw [hHdef, hDdef, Matrix.conjTranspose_conjTranspose]
  have hcolmass : ∑ y : Y, Complex.normSq (V y i) = 1 := by
    have hcast := column_mass_eq V i
    rw [hVV, Matrix.one_apply_eq] at hcast
    exact_mod_cast hcast
  have hAA : (X * V)ᴴ * (X * V) = Vᴴ * H * V := by
    rw [Matrix.conjTranspose_mul, hHX]
    noncomm_ring
  have hentry : ((X * V)ᴴ * (X * V)) i i = (hH.eigenvalues i : ℂ) := by
    rw [hAA, hdiag]
    simp [Function.comp_apply]
  have hmass : ∑ y : Y, Complex.normSq ((X *ᵥ fun l => V l i) y)
      = hH.eigenvalues i := by
    have hcast : ((∑ y : Y, Complex.normSq ((X *ᵥ fun l => V l i) y) : ℝ) : ℂ)
        = ((X * V)ᴴ * (X * V)) i i := by
      rw [← column_mass_eq (X * V) i]
      congr 1
    rw [hentry] at hcast
    exact_mod_cast hcast
  have hnorm : hH.eigenvalues i = ‖X‖ ^ 2 := by
    have hiD : hH.eigenvalues i = ‖D‖ ^ 2 := hi
    rw [hiD, hDdef, Matrix.l2_opNorm_conjTranspose]
  exact ⟨fun l => V l i, hcolmass, by rw [hmass, hnorm]⟩

/-- `prop:mf-upper-bound`, proof sentence `9f1f2f176f18`, second clause: "for
`t ≥ 0`, `‖X‖ ≥ t` holds precisely when there is a vector `v` with `‖v‖ = 1`
and `‖Xv‖² ≥ t²`."  The right-hand side is again polynomial in the real
coordinates, with the vector existentially quantified. -/
theorem le_l2_opNorm_iff_exists_unit_vector (hY : Nonempty Y)
    (X : Matrix Y Y ℂ) {t : ℝ} (ht : 0 ≤ t) :
    t ≤ ‖X‖ ↔ ∃ v : Y → ℂ, (∑ i : Y, Complex.normSq (v i)) = 1 ∧
      t ^ 2 ≤ ∑ i : Y, Complex.normSq ((X *ᵥ v) i) := by
  constructor
  · intro hX
    obtain ⟨v, hv1, hv2⟩ := exists_unit_vector_attaining_l2_opNorm hY X
    refine ⟨v, hv1, ?_⟩
    have h0 : (0 : ℝ) ≤ ‖X‖ := norm_nonneg X
    nlinarith
  · rintro ⟨v, hv1, hv2⟩
    have hle := KazhdanCornerMatrices.sum_normSq_mulVec_le_general X v
    rw [hv1, mul_one] at hle
    have h0 : (0 : ℝ) ≤ ‖X‖ := norm_nonneg X
    nlinarith

end Certificates
end MFRecognition
end Manuscript
end GroupApproximation
