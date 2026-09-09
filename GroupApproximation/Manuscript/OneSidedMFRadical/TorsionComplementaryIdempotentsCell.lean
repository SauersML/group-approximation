import GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotentsDiagonal

/-!
# The printed cell `v = uD(r)`, `c`, `z`, `y`, `ℓ` of `prop:torsion-defect-ring`

`non_mf_groups_exist.tex`, Proposition `prop:torsion-defect-ring`, the proof:

> Let `u` be the compressor of Lemma `lem:ring-compression-cell`, put
> `w_{ij} = (1+f_{ji})(1-f_{ij})(1+f_{ji})`, `r = w_{14}w_{25}`, and `v = uD(r)`.
> Since `D(r)` centralizes `L`, `vLv^{-1} ≤ L`.  Put
> `c = D(1+f_{02})`, `y = e_{42}(f_{10})`, `z = D(1+f_{12})`, `ℓ = e_{21}(1)`,
> `B = ⟨L,v,c,y⟩`.
> Then `c ∈ C_B(L)`, and from `r f_{02} r^{-1} = f_{05}`, `r f_{12} r^{-1} = f_{45}`,
> `f_{02}t^3 = f_{05}`, and `t^3 f_{45} = f_{12}t^3`, direct multiplication with
> the displayed `u` gives `v c v^{-1} = e_{14}(f_{02})` and `v z v^{-1} = z`.

Coordinates are 0-indexed: the printed `e_{14}` is
`elementaryRoot (coreIdx 0) lastIdx`, the printed `e_{21}` is
`elementaryRoot (coreIdx 1) (coreIdx 0)`, the printed `e_{42}` is
`elementaryRoot lastIdx (coreIdx 1)`, and the printed `e_{24}` is
`elementaryRoot (coreIdx 1) lastIdx`.

## How the two conjugations are organised

Both are `u D(a) u^{-1}` for a diagonal `a` that the printed identities supply,
and both are proved as *multiplicative* identities `u D(a) = g u`, so no inverse
of `u` is ever expanded.  Since `D` is multiplicative and `D(r)` centralises
`L`, conjugation by `v = uD(r)` splits as

  `v D(1+x) v^{-1} = u D(r(1+x)r^{-1}) u^{-1}`,

and the printed `r f_{02} r^{-1} = f_{05}`, `r f_{12} r^{-1} = f_{45}` say which
diagonal to feed to `u`.  The two remaining identities `f_{02}t^3 = f_{05}` and
`t^3 f_{45} = f_{12}t^3` are exactly the single nonzero entry of `u·(f E_{44})`
in each case; they are what makes

  `u D(1+f_{05}) = e_{14}(f_{02}) u`,   `u D(1+f_{45}) = D(1+f_{12}) u`

true.

## The rest of the printed cell

`d = [vcv^{-1}, ℓ] = e_{24}(-f_{02})` is the Steinberg relation in its `i = l`
form, which needs its own two-line ring identity
(`commutator_of_mul_eq_zero`), and `[y, d] = D(1-f_{12}) = z^{-1}` is the
*same* square-zero commutator as `D(1 ± f_{ij})`, at the coordinate pair
`(4, 2)` instead of `(4, 1)`: the printed reasons `f_{02}f_{10} = 0` and
`f_{10}f_{02} = f_{12}` are precisely its two hypotheses.  Both live in
`TorsionComplementaryIdempotentsCentral`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace TorsionComplementaryIdempotents

open GroupApproximation.OneSidedCompressor
open scoped commutatorElement

universe u

/-! ## Small index facts -/

theorem oneNeZeroFin : (1 : Fin 3) ≠ 0 := by decide

theorem zeroNeTwoNat : (0 : ℕ) ≠ 2 := by decide

theorem oneNeTwoNat : (1 : ℕ) ≠ 2 := by decide

variable {R : Type u} [Ring R]

/-! ## Two more square-zero commutators -/

/-- The Steinberg relation in its `i = l` form: if `XY = 0` and `X² = Y² = 0`
then the group commutator is `1 - YX`. -/
theorem commutator_of_mul_eq_zero {A : Type*} [Ring A] {X Y : A}
    (hXX : X * X = 0) (hYY : Y * Y = 0) (hXY : X * Y = 0) :
    (1 + X) * (1 + Y) * (1 - X) * (1 - Y) = 1 - Y * X := by
  have hsplit : (1 + X) * (1 + Y) * (1 - X) * (1 - Y)
      = ((1 + X) * (1 + Y)) * ((1 - X) * (1 - Y)) := by noncomm_ring
  have e1 : (1 + X) * (1 + Y) = 1 + X + Y + X * Y := by noncomm_ring
  have e2 : (1 - X) * (1 - Y) = 1 - X - Y + X * Y := by noncomm_ring
  rw [hsplit, e1, e2, hXY]
  calc (1 + X + Y + 0) * (1 - X - Y + 0)
      = (1 - X - Y) + (X - X * X - X * Y) + (Y - Y * X - Y * Y) := by
        noncomm_ring
    _ = 1 - Y * X := by rw [hXX, hXY, hYY]; abel

/-- The printed commutator `D(1 + xy) = [e₄ₖ(x), e_{k4}(y)]` at an arbitrary
core coordinate `k`, whenever `yx = 0`.  At the first core coordinate it is the
printed `D(1 ± f_{ij})`; at the second it is the printed
`[y, d] = D(1 - f_{12})`. -/
theorem commutator_last_eq_lastDiag {q : Fin 4} (hq : lastIdx ≠ q) {x y : R}
    (hyx : y * x = 0) :
    (((⁅elementaryRoot lastIdx q hq x, elementaryRoot q lastIdx (Ne.symm hq) y⁆ :
        elementaryGroup (Fin 4) R) : (Matrix (Fin 4) (Fin 4) R)ˣ) :
      Matrix (Fin 4) (Fin 4) R) = lastDiag (1 + x * y) := by
  have hXX : Matrix.single lastIdx q x * Matrix.single lastIdx q x = 0 :=
    Matrix.single_mul_single_of_ne (c := x) lastIdx q lastIdx (Ne.symm hq) x
  have hYY : Matrix.single q lastIdx y * Matrix.single q lastIdx y = 0 :=
    Matrix.single_mul_single_of_ne (c := y) q lastIdx q hq y
  have hYX : Matrix.single q lastIdx y * Matrix.single lastIdx q x = 0 := by
    rw [Matrix.single_mul_single_same, hyx, Matrix.single_zero]
  have hXY : Matrix.single lastIdx q x * Matrix.single q lastIdx y
      = Matrix.single lastIdx lastIdx (x * y) :=
    Matrix.single_mul_single_same (c := x) lastIdx q lastIdx y
  rw [lastDiag_one_add, ← hXY]
  change (1 + Matrix.single lastIdx q x) * (1 + Matrix.single q lastIdx y) *
      (1 - Matrix.single lastIdx q x) * (1 - Matrix.single q lastIdx y) = _
  exact one_add_commutator_of_square_zero hXX hYY hYX

/-! ## `D(a)` against a single elementary matrix -/

theorem lastDiag_mul_single (a b : R) (p q : Fin 4) :
    lastDiag a * Matrix.single p q b
      = Matrix.single p q ((if p = lastIdx then a else 1) * b) := by
  ext r c
  rw [lastDiag, Matrix.diagonal_mul, Matrix.single_apply, Matrix.single_apply]
  by_cases h : p = r ∧ q = c
  · obtain ⟨hr, hc⟩ := h
    subst hr
    subst hc
    simp
  · simp [h]

theorem single_mul_lastDiag (a b : R) (p q : Fin 4) :
    Matrix.single p q b * lastDiag a
      = Matrix.single p q (b * (if q = lastIdx then a else 1)) := by
  ext r c
  rw [lastDiag, Matrix.mul_diagonal, Matrix.single_apply, Matrix.single_apply]
  by_cases h : p = r ∧ q = c
  · obtain ⟨hr, hc⟩ := h
    subst hr
    subst hc
    simp
  · simp [h]

/-- Powers of `D`. -/
theorem lastDiag_pow (a : R) (m : ℕ) : lastDiag a ^ m = lastDiag (a ^ m) := by
  induction m with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, lastDiag_mul, pow_succ]

theorem elementaryGroup_val_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : elementaryGroup ι R) (m : ℕ) :
    (((x ^ m : elementaryGroup ι R) : (Matrix ι ι R)ˣ) : Matrix ι ι R)
      = ((x : (Matrix ι ι R)ˣ) : Matrix ι ι R) ^ m := by
  induction m with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, elementaryGroup_val_mul, ih]

/-! ## The printed elements -/

section Printed

variable (P : OneSidedInverse R)

/-- The printed `t^3`, in the form the compressor matrix carries it. -/
theorem t_mul_t_mul_t : P.t * P.t * P.t = P.t ^ 3 := by
  rw [pow_succ, pow_succ, pow_one]

/-- **Printed:** `v = uD(r)`. -/
def printedV : elementaryGroup (Fin 4) R := compressor P * diagR P

/-- **Printed:** `c = D(1 + f_{02})`. -/
def printedC : elementaryGroup (Fin 4) R := diagPlus P 0 2

/-- **Printed:** `z = D(1 + f_{12})`. -/
def printedZ : elementaryGroup (Fin 4) R := diagPlus P 1 2

/-- **Printed:** `y = e_{42}(f_{10})`. -/
def printedY : elementaryGroup (Fin 4) R :=
  elementaryRoot lastIdx (coreIdx 1) (last_ne_coreIdx 1) (fUnit P 1 0)

/-- **Printed:** `ℓ = e_{21}(1)`. -/
def printedEllTwoOne (R : Type u) [Ring R] : elementaryGroup (Fin 4) R :=
  elementaryRoot (coreIdx 1) (coreIdx 0) (coreIdx_injective.ne oneNeZeroFin) 1

/-- **Printed:** `d = e_{24}(-f_{02})`. -/
def printedDefectElt : elementaryGroup (Fin 4) R :=
  elementaryRoot (coreIdx 1) lastIdx (coreIdx_ne_last 1) (-fUnit P 0 2)

theorem printedC_matrix :
    ((printedC P : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R)
      = lastDiag (1 + fUnit P 0 2) :=
  diagPlus_matrix P zeroNeTwoNat

theorem printedZ_matrix :
    ((printedZ P : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R)
      = lastDiag (1 + fUnit P 1 2) :=
  diagPlus_matrix P oneNeTwoNat

/-! ### `ℓ ∈ L` and `v` compresses `L` -/

theorem printedEllTwoOne_mem_core : printedEllTwoOne R ∈ core R :=
  elementaryRoot_mem_core 1 0 oneNeZeroFin 1

/-- **Printed:** `D(r)` centralises `L`. -/
theorem diagR_commute_core : ∀ g ∈ core R, Commute (diagR P) g :=
  lastDiag_commute_core (diagR P) _ (diagR_matrix P)

/-- **Printed:** `vLv^{-1} ≤ L`, because `D(r)` centralises `L` and
`uLu^{-1} ≤ L`. -/
theorem printedV_compresses_core :
    ∀ g ∈ core R, printedV P * g * (printedV P)⁻¹ ∈ core R := by
  intro g hg
  have hcomm : diagR P * g = g * diagR P := diagR_commute_core P g hg
  have hrw : printedV P * g * (printedV P)⁻¹
      = compressor P * g * (compressor P)⁻¹ := by
    rw [printedV, mul_inv_rev]
    calc compressor P * diagR P * g * ((diagR P)⁻¹ * (compressor P)⁻¹)
        = compressor P * (diagR P * g) * ((diagR P)⁻¹ * (compressor P)⁻¹) := by
          group
      _ = compressor P * (g * diagR P) * ((diagR P)⁻¹ * (compressor P)⁻¹) := by
          rw [hcomm]
      _ = compressor P * g * (compressor P)⁻¹ := by group
  rw [hrw]
  exact compressor_compresses_core P g hg

/-- **Printed:** `c ∈ C_B(L)`. -/
theorem printedC_commute_core : ∀ g ∈ core R, Commute (printedC P) g :=
  lastDiag_commute_core (printedC P) _ (printedC_matrix P)

/-- `z` commutes with `L`. -/
theorem printedZ_commute_core : ∀ g ∈ core R, Commute (printedZ P) g :=
  lastDiag_commute_core (printedZ P) _ (printedZ_matrix P)

/-! ### The two compressor identities -/

/-- `u·(f_{05}E_{44}) = f_{05}E_{14}`: the printed `f_{02}t^3 = f_{05}` read as
the single nonzero entry, together with `e f_{05} = f_{05}` and the vanishing of
the other three. -/
theorem compressor_mul_single_last_five :
    compressorMatrix P * Matrix.single lastIdx lastIdx (fUnit P 0 5)
      = Matrix.single (coreIdx 0) lastIdx (fUnit P 0 5) := by
  have h0 : P.e * fUnit P 0 5 = fUnit P 0 5 := by
    have h := fUnit_mul_of_eq P 0 0 5
    rwa [fUnit_zero_zero] at h
  have h1 : P.e * P.t * fUnit P 0 5 = 0 := by
    have h : fUnit P 0 1 * fUnit P 0 5 = 0 := fUnit_mul_of_ne P 0 5 (by decide)
    rwa [fUnit, pow_zero, one_mul, pow_one] at h
  have h2 : P.e * P.t * P.t * fUnit P 0 5 = 0 := by
    have h : fUnit P 0 2 * fUnit P 0 5 = 0 := fUnit_mul_of_ne P 0 5 (by decide)
    rwa [fUnit, pow_zero, one_mul, pow_two, ← mul_assoc] at h
  have htpow : P.t ^ 3 * P.e = 0 := by simpa using P.t_pow_mul_e 2
  have h3 : P.t * P.t * P.t * fUnit P 0 5 = 0 := by
    rw [t_mul_t_mul_t P, fUnit, pow_zero, one_mul, ← mul_assoc, htpow, zero_mul]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [compressorMatrix, Matrix.mul_apply, Matrix.single_apply, coreIdx,
      lastIdx, h0, h1, h2, h3]

/-- `(f_{02}E_{14})·u = f_{05}E_{14}`: the printed `f_{02}t^3 = f_{05}`. -/
theorem single_zero_two_mul_compressor :
    Matrix.single (coreIdx 0) lastIdx (fUnit P 0 2) * compressorMatrix P
      = Matrix.single (coreIdx 0) lastIdx (fUnit P 0 5) := by
  have h : fUnit P 0 2 * (P.t * P.t * P.t) = fUnit P 0 5 := by
    rw [t_mul_t_mul_t P, fUnit_zero_two_mul_t_cube P]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [compressorMatrix, Matrix.mul_apply, Matrix.single_apply, coreIdx,
      lastIdx, h]

/-- **Printed:** `u D(1+f_{05}) = e_{14}(f_{02}) u`. -/
theorem compressor_mul_lastDiag_five :
    compressorMatrix P * lastDiag (1 + fUnit P 0 5)
      = (1 + Matrix.single (coreIdx 0) lastIdx (fUnit P 0 2)) *
        compressorMatrix P := by
  rw [lastDiag_one_add, mul_add, mul_one, add_mul, one_mul,
    compressor_mul_single_last_five P, single_zero_two_mul_compressor P]

/-- `u·(f_{45}E_{44}) = f_{15}E_{44}`: the printed `t^3 f_{45} = f_{12}t^3`. -/
theorem compressor_mul_single_last_four_five :
    compressorMatrix P * Matrix.single lastIdx lastIdx (fUnit P 4 5)
      = Matrix.single lastIdx lastIdx (fUnit P 1 5) := by
  have h0 : P.e * fUnit P 4 5 = 0 := by
    have h : fUnit P 0 0 * fUnit P 4 5 = 0 := fUnit_mul_of_ne P 0 5 (by decide)
    rwa [fUnit_zero_zero] at h
  have h1 : P.e * P.t * fUnit P 4 5 = 0 := by
    have h : fUnit P 0 1 * fUnit P 4 5 = 0 := fUnit_mul_of_ne P 0 5 (by decide)
    rwa [fUnit, pow_zero, one_mul, pow_one] at h
  have h2 : P.e * P.t * P.t * fUnit P 4 5 = 0 := by
    have h : fUnit P 0 2 * fUnit P 4 5 = 0 := fUnit_mul_of_ne P 0 5 (by decide)
    rwa [fUnit, pow_zero, one_mul, pow_two, ← mul_assoc] at h
  have h3 : P.t * P.t * P.t * fUnit P 4 5 = fUnit P 1 5 := by
    rw [t_mul_t_mul_t P, t_cube_mul_fUnit_four_five P]
    simp only [fUnit]
    rw [mul_assoc, ← pow_add]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [compressorMatrix, Matrix.mul_apply, Matrix.single_apply, lastIdx,
      h0, h1, h2, h3]

theorem single_one_two_mul_compressor :
    Matrix.single lastIdx lastIdx (fUnit P 1 2) * compressorMatrix P
      = Matrix.single lastIdx lastIdx (fUnit P 1 5) := by
  have h : fUnit P 1 2 * (P.t * P.t * P.t) = fUnit P 1 5 := by
    rw [t_mul_t_mul_t P]
    simp only [fUnit]
    rw [mul_assoc, ← pow_add]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [compressorMatrix, Matrix.mul_apply, Matrix.single_apply, lastIdx, h]

/-- **Printed:** `u D(1+f_{45}) = D(1+f_{12}) u`. -/
theorem compressor_mul_lastDiag_four_five :
    compressorMatrix P * lastDiag (1 + fUnit P 4 5)
      = lastDiag (1 + fUnit P 1 2) * compressorMatrix P := by
  rw [lastDiag_one_add, lastDiag_one_add, mul_add, mul_one, add_mul, one_mul,
    compressor_mul_single_last_four_five P, single_one_two_mul_compressor P]

/-! ### The two printed conjugations -/

/-- `r(1+f_{02}) = (1+f_{05})r`, the multiplicative form of the printed
`r f_{02} r^{-1} = f_{05}`. -/
theorem rUnit_mul_one_add_zero_two :
    ((rUnit P : Rˣ) : R) * (1 + fUnit P 0 2)
      = (1 + fUnit P 0 5) * ((rUnit P : Rˣ) : R) := by
  have hback := fUnit_zero_two_mul_rUnit_inv P
  have h : fUnit P 0 2 = fUnit P 0 5 * ((rUnit P : Rˣ) : R) := by
    calc fUnit P 0 2
        = fUnit P 0 2 * ((((rUnit P)⁻¹ : Rˣ) : R) * ((rUnit P : Rˣ) : R)) := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
      _ = fUnit P 0 5 * ((rUnit P : Rˣ) : R) := by rw [← mul_assoc, hback]
  rw [mul_add, add_mul, mul_one, one_mul, rUnit_mul_fUnit_zero_two P, h]

/-- `r(1+f_{12}) = (1+f_{45})r`, the multiplicative form of the printed
`r f_{12} r^{-1} = f_{45}`. -/
theorem rUnit_mul_one_add_one_two :
    ((rUnit P : Rˣ) : R) * (1 + fUnit P 1 2)
      = (1 + fUnit P 4 5) * ((rUnit P : Rˣ) : R) := by
  have hback := fUnit_four_two_mul_rUnit_inv P
  have h : fUnit P 4 2 = fUnit P 4 5 * ((rUnit P : Rˣ) : R) := by
    calc fUnit P 4 2
        = fUnit P 4 2 * ((((rUnit P)⁻¹ : Rˣ) : R) * ((rUnit P : Rˣ) : R)) := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
      _ = fUnit P 4 5 * ((rUnit P : Rˣ) : R) := by rw [← mul_assoc, hback]
  rw [mul_add, add_mul, mul_one, one_mul, rUnit_mul_fUnit_one_two P, h]

/-- **Printed:** `v c v^{-1} = e_{14}(f_{02})`. -/
theorem printedV_conj_printedC :
    printedV P * printedC P * (printedV P)⁻¹
      = elementaryRoot (coreIdx 0) lastIdx (coreIdx_ne_last 0) (fUnit P 0 2) := by
  have hmat : compressorMatrix P * lastDiag ((rUnit P : Rˣ) : R) *
        lastDiag (1 + fUnit P 0 2)
      = (1 + Matrix.single (coreIdx 0) lastIdx (fUnit P 0 2)) *
        (compressorMatrix P * lastDiag ((rUnit P : Rˣ) : R)) := by
    calc compressorMatrix P * lastDiag ((rUnit P : Rˣ) : R) *
          lastDiag (1 + fUnit P 0 2)
        = compressorMatrix P *
            lastDiag (((rUnit P : Rˣ) : R) * (1 + fUnit P 0 2)) := by
          rw [mul_assoc, lastDiag_mul]
      _ = compressorMatrix P *
            (lastDiag (1 + fUnit P 0 5) * lastDiag ((rUnit P : Rˣ) : R)) := by
          rw [rUnit_mul_one_add_zero_two P, lastDiag_mul]
      _ = (compressorMatrix P * lastDiag (1 + fUnit P 0 5)) *
            lastDiag ((rUnit P : Rˣ) : R) := by rw [mul_assoc]
      _ = ((1 + Matrix.single (coreIdx 0) lastIdx (fUnit P 0 2)) *
            compressorMatrix P) * lastDiag ((rUnit P : Rˣ) : R) := by
          rw [compressor_mul_lastDiag_five P]
      _ = (1 + Matrix.single (coreIdx 0) lastIdx (fUnit P 0 2)) *
            (compressorMatrix P * lastDiag ((rUnit P : Rˣ) : R)) := by
          rw [mul_assoc]
  have key : printedV P * printedC P
      = elementaryRoot (coreIdx 0) lastIdx (coreIdx_ne_last 0) (fUnit P 0 2) *
        printedV P := by
    refine elementaryGroup_ext ?_
    rw [printedV]
    simp only [elementaryGroup_val_mul, compressor_val, diagR_matrix P,
      printedC_matrix P, elementaryRoot_matrix]
    exact hmat
  rw [key]
  group

/-- **Printed:** `v z v^{-1} = z`. -/
theorem printedV_conj_printedZ :
    printedV P * printedZ P * (printedV P)⁻¹ = printedZ P := by
  have hmat : compressorMatrix P * lastDiag ((rUnit P : Rˣ) : R) *
        lastDiag (1 + fUnit P 1 2)
      = lastDiag (1 + fUnit P 1 2) *
        (compressorMatrix P * lastDiag ((rUnit P : Rˣ) : R)) := by
    calc compressorMatrix P * lastDiag ((rUnit P : Rˣ) : R) *
          lastDiag (1 + fUnit P 1 2)
        = compressorMatrix P *
            lastDiag (((rUnit P : Rˣ) : R) * (1 + fUnit P 1 2)) := by
          rw [mul_assoc, lastDiag_mul]
      _ = compressorMatrix P *
            (lastDiag (1 + fUnit P 4 5) * lastDiag ((rUnit P : Rˣ) : R)) := by
          rw [rUnit_mul_one_add_one_two P, lastDiag_mul]
      _ = (compressorMatrix P * lastDiag (1 + fUnit P 4 5)) *
            lastDiag ((rUnit P : Rˣ) : R) := by rw [mul_assoc]
      _ = (lastDiag (1 + fUnit P 1 2) * compressorMatrix P) *
            lastDiag ((rUnit P : Rˣ) : R) := by
          rw [compressor_mul_lastDiag_four_five P]
      _ = lastDiag (1 + fUnit P 1 2) *
            (compressorMatrix P * lastDiag ((rUnit P : Rˣ) : R)) := by
          rw [mul_assoc]
  have key : printedV P * printedZ P = printedZ P * printedV P := by
    refine elementaryGroup_ext ?_
    rw [printedV]
    simp only [elementaryGroup_val_mul, compressor_val, diagR_matrix P,
      printedZ_matrix P]
    exact hmat
  rw [key]
  group

end Printed

end TorsionComplementaryIdempotents
end OneSidedMFRadical
end Manuscript
end GroupApproximation
