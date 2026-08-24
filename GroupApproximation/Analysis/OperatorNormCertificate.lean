import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Finite rational certificates for operator-norm bounds

The operator norm of a complex matrix is not a rational number, and comparing
it with a rational bound is not, on the face of it, a finitely checkable
condition.  This file supplies the two comparisons that a finite check needs.

Write `froSq A` for the sum of the squared moduli of the entries --- a quantity
that is rational whenever the entries are.  Two crude estimates relate it to
the operator norm, each costing a fixed power of the dimension:

    ‖A‖ ^ 2 ≤ card ^ 4 * froSq A        and        froSq A ≤ card ^ 2 * ‖A‖ ^ 2.

Sharp constants would cost a Cauchy--Schwarz argument and buy nothing: the
intended use multiplies them against a doubly exponential factor.

The point of the file is what those estimates give when combined with the
C-star identity.  `Aᴴ * A` is self-adjoint, so `IsSelfAdjoint.norm_pow_two_pow`
makes its norm *exactly* multiplicative along powers of two,

    ‖(Aᴴ * A) ^ 2 ^ m‖ = ‖Aᴴ * A‖ ^ 2 ^ m = ‖A‖ ^ 2 ^ (m + 1),

so a single natural number `m` certifies a strict operator-norm bound, and the
check is a comparison of two real numbers built from the entries by ring
operations.  No eigenvalue computation, positive-definiteness decision
procedure or Cholesky factorisation appears anywhere.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace OperatorNormCertificate

open scoped Matrix
open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Coordinates of a Euclidean vector -/

omit [DecidableEq n] in
/-- A coordinate is bounded by the norm. -/
theorem norm_coord_le (x : EuclideanSpace ℂ n) (i : n) : ‖x i‖ ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq]
  have hle : ‖x i‖ ^ 2 ≤ ∑ j, ‖x j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ i)
  calc ‖x i‖ = Real.sqrt (‖x i‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (∑ j, ‖x j‖ ^ 2) := Real.sqrt_le_sqrt hle

/-! ## The operator norm through the Euclidean continuous linear map -/

/-- The defining bound. -/
theorem norm_apply_le (A : Matrix n n ℂ) (x : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A x‖ ≤ ‖A‖ * ‖x‖ := by
  rw [Matrix.cstar_norm_def]
  exact ContinuousLinearMap.le_opNorm _ x

/-- The coordinates of the image are the matrix acting on the coordinates. -/
theorem apply_coord (A : Matrix n n ℂ) (x : EuclideanSpace ℂ n) (i : n) :
    (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A x) i = ∑ j, A i j * x j := rfl

/-- Every entry is bounded by the operator norm. -/
theorem norm_entry_le_opNorm (A : Matrix n n ℂ) (i j : n) : ‖A i j‖ ≤ ‖A‖ := by
  classical
  set x : EuclideanSpace ℂ n := PiLp.single 2 j (1 : ℂ) with hxdef
  have hxj : x j = (1 : ℂ) := by rw [hxdef]; simp
  have hxne : ∀ k, k ≠ j → x k = 0 := by
    intro k hk; rw [hxdef]; simp [hk]
  have hxnorm : ‖x‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    have hsum : ∑ k, ‖x k‖ ^ 2 = 1 := by
      rw [Finset.sum_eq_single j]
      · rw [hxj]; simp
      · intro b _ hb; rw [hxne b hb]; simp
      · intro hcon; exact absurd (Finset.mem_univ j) hcon
    rw [hsum, Real.sqrt_one]
  have hle := norm_apply_le A x
  rw [hxnorm, mul_one] at hle
  have hval : (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A x) i = A i j := by
    rw [apply_coord, Finset.sum_eq_single j]
    · rw [hxj, mul_one]
    · intro b _ hb; rw [hxne b hb, mul_zero]
    · intro hcon; exact absurd (Finset.mem_univ j) hcon
  have hcoord := norm_coord_le (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A x) i
  rw [hval] at hcoord
  exact hcoord.trans hle

/-- An entrywise bound gives an operator-norm bound, with a crude dimensional
constant. -/
theorem opNorm_le_of_entry_bound (A : Matrix n n ℂ) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ i j, ‖A i j‖ ≤ M) :
    ‖A‖ ≤ (Fintype.card n : ℝ) ^ 2 * M := by
  set N : ℝ := (Fintype.card n : ℝ) with hN
  have hNnonneg : 0 ≤ N := by rw [hN]; positivity
  have hexp : N * N ^ 2 ≤ (N ^ 2) ^ 2 := by
    rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | hpos
    · rw [hN, h0]; norm_num
    · have h1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast hpos
      nlinarith
  have hkey : ∀ x : EuclideanSpace ℂ n,
      ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A x‖ ≤ N ^ 2 * M * ‖x‖ := by
    intro x
    have hrow : ∀ i, ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A x) i‖
        ≤ N * M * ‖x‖ := by
      intro i
      rw [apply_coord]
      have hsum : ‖∑ j, A i j * x j‖ ≤ ∑ _j : n, M * ‖x‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
        intro j _
        rw [norm_mul]
        exact mul_le_mul (h i j) (norm_coord_le x j) (norm_nonneg _) hM
      have hcard : ∑ _j : n, M * ‖x‖ = N * (M * ‖x‖) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN]
      calc ‖∑ j, A i j * x j‖ ≤ ∑ _j : n, M * ‖x‖ := hsum
        _ = N * (M * ‖x‖) := hcard
        _ = N * M * ‖x‖ := by ring
    rw [EuclideanSpace.norm_eq]
    have hsq : ∑ i, ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A x) i‖ ^ 2
        ≤ N * (N * M * ‖x‖) ^ 2 := by
      have hstep := Finset.sum_le_sum (s := (Finset.univ : Finset n))
        (f := fun i => ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A x) i‖ ^ 2)
        (g := fun _ => (N * M * ‖x‖) ^ 2)
        (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hrow i) 2)
      refine hstep.trans (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN]
    have hfac : N * (N * M * ‖x‖) ^ 2 ≤ (N ^ 2 * M * ‖x‖) ^ 2 := by
      have hmx : (0 : ℝ) ≤ (M * ‖x‖) ^ 2 := sq_nonneg _
      calc N * (N * M * ‖x‖) ^ 2 = (N * N ^ 2) * (M * ‖x‖) ^ 2 := by ring
        _ ≤ (N ^ 2) ^ 2 * (M * ‖x‖) ^ 2 := mul_le_mul_of_nonneg_right hexp hmx
        _ = (N ^ 2 * M * ‖x‖) ^ 2 := by ring
    calc Real.sqrt (∑ i, ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A x) i‖ ^ 2)
        ≤ Real.sqrt ((N ^ 2 * M * ‖x‖) ^ 2) := Real.sqrt_le_sqrt (hsq.trans hfac)
      _ = N ^ 2 * M * ‖x‖ := Real.sqrt_sq (by positivity)
  rw [Matrix.cstar_norm_def]
  exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) hkey

/-! ## The Frobenius quantity -/

/-- The sum of the squared moduli of the entries. -/
noncomputable def froSq (A : Matrix n n ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

omit [DecidableEq n] in
theorem froSq_nonneg (A : Matrix n n ℂ) : 0 ≤ froSq A := by
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  positivity

omit [DecidableEq n] in
theorem sq_entry_le_froSq (A : Matrix n n ℂ) (i j : n) :
    ‖A i j‖ ^ 2 ≤ froSq A := by
  have hinner : ‖A i j‖ ^ 2 ≤ ∑ j', ‖A i j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' => ‖A i j'‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ j)
  refine hinner.trans ?_
  exact Finset.single_le_sum (f := fun i' => ∑ j', ‖A i' j'‖ ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)

/-- `froSq` is bounded by the operator norm, with a dimensional constant. -/
theorem froSq_le (A : Matrix n n ℂ) :
    froSq A ≤ (Fintype.card n : ℝ) ^ 2 * ‖A‖ ^ 2 := by
  have hentry : ∀ i j : n, ‖A i j‖ ^ 2 ≤ ‖A‖ ^ 2 := fun i j =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_entry_le_opNorm A i j) 2
  calc froSq A ≤ ∑ _i : n, ∑ _j : n, ‖A‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
    _ = (Fintype.card n : ℝ) ^ 2 * ‖A‖ ^ 2 := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          nsmul_eq_mul]
        ring

/-- The operator norm is bounded by `froSq`, with a dimensional constant. -/
theorem opNorm_sq_le_froSq (A : Matrix n n ℂ) :
    ‖A‖ ^ 2 ≤ (Fintype.card n : ℝ) ^ 4 * froSq A := by
  have hentry : ∀ i j : n, ‖A i j‖ ≤ Real.sqrt (froSq A) := by
    intro i j
    calc ‖A i j‖ = Real.sqrt (‖A i j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (froSq A) := Real.sqrt_le_sqrt (sq_entry_le_froSq A i j)
  have hb := opNorm_le_of_entry_bound A (Real.sqrt_nonneg (froSq A)) hentry
  have hsq : ‖A‖ ^ 2 ≤ ((Fintype.card n : ℝ) ^ 2 * Real.sqrt (froSq A)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hb 2
  refine hsq.trans (le_of_eq ?_)
  rw [mul_pow, Real.sq_sqrt (froSq_nonneg A)]
  ring

/-! ## The certificate

The C-star identity makes the norm of the self-adjoint square exactly
multiplicative along powers of two, which is what turns a strict operator-norm
bound into a single natural number. -/

/-- A power of a number in the unit interval is at most one. -/
theorem pow_le_one_of_le_one {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    ∀ c : ℕ, r ^ c ≤ 1
  | 0 => by simp
  | c + 1 => by
      have ih := pow_le_one_of_le_one h0 h1 c
      have hnn : 0 ≤ r ^ c := pow_nonneg h0 c
      rw [pow_succ]
      nlinarith

/-- Powers of a number in the unit interval decrease. -/
theorem pow_antitone_of_le_one {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1)
    (a b : ℕ) (hab : a ≤ b) : r ^ b ≤ r ^ a := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add]
  have hc := pow_le_one_of_le_one h0 h1 c
  have hna : 0 ≤ r ^ a := pow_nonneg h0 a
  nlinarith

/-- Every natural number is at most its own power of two. -/
theorem self_le_two_pow : ∀ k : ℕ, k ≤ 2 ^ k
  | 0 => by norm_num
  | m + 1 => by
      have ih := self_le_two_pow m
      have hp : 0 < 2 ^ m := by positivity
      rw [pow_succ]
      omega

/-- Strict comparison descends through a common power. -/
theorem lt_of_pow_lt_pow {a b : ℝ} (hb : 0 ≤ b) {k : ℕ}
    (h : a ^ k < b ^ k) : a < b := by
  rcases lt_or_ge a b with hlt | hge
  · exact hlt
  · exact absurd (pow_le_pow_left₀ hb hge k) (not_le.2 h)

omit [DecidableEq n] in
theorem isSelfAdjoint_conjTranspose_mul (A : Matrix n n ℂ) :
    IsSelfAdjoint (Aᴴ * A) := by
  show star (Aᴴ * A) = Aᴴ * A
  simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul]

/-- **The norm of the self-adjoint square is exactly multiplicative along
powers of two.** -/
theorem norm_conjTranspose_mul_pow (A : Matrix n n ℂ) (m : ℕ) :
    ‖(Aᴴ * A) ^ 2 ^ m‖ = ‖A‖ ^ 2 ^ (m + 1) := by
  rw [(isSelfAdjoint_conjTranspose_mul A).norm_pow_two_pow m,
    Matrix.l2_opNorm_conjTranspose_mul_self]
  rw [← sq, ← pow_mul]
  congr 1
  rw [pow_succ']

/-- **Soundness of the certificate.**  One natural number certifies a strict
operator-norm bound. -/
theorem opNorm_lt_of_certificate (A : Matrix n n ℂ) {q : ℝ} (hq : 0 < q) (m : ℕ)
    (h : (Fintype.card n : ℝ) ^ 4 * froSq ((Aᴴ * A) ^ 2 ^ m)
      < q ^ 2 ^ (m + 2)) :
    ‖A‖ < q := by
  have hle := opNorm_sq_le_froSq ((Aᴴ * A) ^ 2 ^ m)
  rw [norm_conjTranspose_mul_pow A m] at hle
  have hexp : (‖A‖ ^ 2 ^ (m + 1)) ^ 2 = ‖A‖ ^ 2 ^ (m + 2) := by
    rw [← pow_mul, ← pow_succ]
  rw [hexp] at hle
  exact lt_of_pow_lt_pow hq.le (lt_of_le_of_lt hle h)

/-- **Completeness of the certificate.**  A strict operator-norm bound is
always certified. -/
theorem exists_certificate_of_opNorm_lt (A : Matrix n n ℂ) {q : ℝ} (hq : 0 < q)
    (h : ‖A‖ < q) :
    ∃ m : ℕ, (Fintype.card n : ℝ) ^ 4 * froSq ((Aᴴ * A) ^ 2 ^ m)
      < q ^ 2 ^ (m + 2) := by
  set C : ℝ := (Fintype.card n : ℝ) ^ 6 with hC
  have hCnonneg : 0 ≤ C := by rw [hC]; positivity
  set r : ℝ := ‖A‖ / q with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r < 1 := by rw [hr]; exact (div_lt_one hq).2 h
  obtain ⟨N, hN⟩ :=
    exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (C + 1) by positivity) hr1
  refine ⟨N, ?_⟩
  have hNle : N ≤ 2 ^ (N + 2) := by
    have h1 := self_le_two_pow N
    have h2 : 2 ^ N ≤ 2 ^ (N + 2) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hpow : r ^ 2 ^ (N + 2) < 1 / (C + 1) :=
    lt_of_le_of_lt (pow_antitone_of_le_one hr0 hr1.le N (2 ^ (N + 2)) hNle) hN
  have hAq : ‖A‖ = r * q := by rw [hr]; field_simp
  have hstep : (Fintype.card n : ℝ) ^ 4 * froSq ((Aᴴ * A) ^ 2 ^ N)
      ≤ C * ‖A‖ ^ 2 ^ (N + 2) := by
    have hf := froSq_le ((Aᴴ * A) ^ 2 ^ N)
    rw [norm_conjTranspose_mul_pow A N] at hf
    have hexp : (‖A‖ ^ 2 ^ (N + 1)) ^ 2 = ‖A‖ ^ 2 ^ (N + 2) := by
      rw [← pow_mul, ← pow_succ]
    rw [hexp] at hf
    have hmul := mul_le_mul_of_nonneg_left hf
      (by positivity : (0 : ℝ) ≤ (Fintype.card n : ℝ) ^ 4)
    refine hmul.trans (le_of_eq ?_)
    rw [hC]; ring
  refine lt_of_le_of_lt hstep ?_
  have hqpow : (0 : ℝ) < q ^ 2 ^ (N + 2) := by positivity
  have hrewrite : ‖A‖ ^ 2 ^ (N + 2) = r ^ 2 ^ (N + 2) * q ^ 2 ^ (N + 2) := by
    rw [hAq, mul_pow]
  rw [hrewrite]
  have hfrac : C * r ^ 2 ^ (N + 2) < 1 := by
    rcases eq_or_lt_of_le hCnonneg with hzero | hpos
    · rw [← hzero, zero_mul]; norm_num
    · have hCC : C * r ^ 2 ^ (N + 2) < C * (1 / (C + 1)) :=
        mul_lt_mul_of_pos_left hpow hpos
      have hlt1 : C * (1 / (C + 1)) < 1 := by
        rw [mul_one_div, div_lt_one (by linarith)]
        linarith
      exact hCC.trans hlt1
  calc C * (r ^ 2 ^ (N + 2) * q ^ 2 ^ (N + 2))
      = (C * r ^ 2 ^ (N + 2)) * q ^ 2 ^ (N + 2) := by ring
    _ < 1 * q ^ 2 ^ (N + 2) := mul_lt_mul_of_pos_right hfrac hqpow
    _ = q ^ 2 ^ (N + 2) := one_mul _

end OperatorNormCertificate
end GroupApproximation
