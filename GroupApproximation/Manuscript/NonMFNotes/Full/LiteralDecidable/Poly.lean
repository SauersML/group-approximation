import Mathlib.Data.Complex.Basic

/-!
# Neutral real polynomial systems (lane NN02c)

Manuscript: `thm:mf-radical-arithmetic` (non_mf_group_notes.tex), sentence
"This is decidable over the real closed field" (Tarski 1951, Seidenberg 1954).

This file supplies the target language of the reduction of the literal predicate
`NN02b.LiteralD` to real arithmetic: finite systems of polynomial equations and non-strict
inequalities with integer coefficients in countably many real unknowns
(`PolySystem.Holds`), together with a compiler from systems of complex polynomials in
unknowns and their conjugates (`CSystem.Holds`) to real systems, splitting every complex
unknown `ζ k` into the real unknowns `x (2k)` (real part) and `x (2k+1)` (imaginary part).
No decision procedure is assumed here.
-/

namespace GroupApproximation.Full.NN02c

noncomputable section

/-! ### Coefficients -/

/-- A signed natural-number coefficient `(neg, n)`, standing for `-n` if `neg` and `n` else. -/
abbrev Coef := Bool × ℕ

/-- The real value of a signed coefficient. -/
def coefVal (c : Coef) : ℝ := bif c.1 then -(c.2 : ℝ) else (c.2 : ℝ)

theorem coefVal_false (n : ℕ) : coefVal (false, n) = (n : ℝ) := rfl

theorem coefVal_true (n : ℕ) : coefVal (true, n) = -(n : ℝ) := rfl

/-- Negation of a signed coefficient. -/
def negCoef (c : Coef) : Coef := (!c.1, c.2)

theorem coefVal_negCoef (c : Coef) : coefVal (negCoef c) = -coefVal c := by
  obtain ⟨b, n⟩ := c
  cases b
  · show -(n : ℝ) = -(n : ℝ)
    rfl
  · show (n : ℝ) = -(-(n : ℝ))
    exact (neg_neg _).symm

/-! ### Real polynomials and systems -/

/-- A real polynomial with integer coefficients: a list of (coefficient, list of variable
indices) monomials. -/
abbrev Poly := List (Coef × List ℕ)

/-- A polynomial system: equations (first component) and non-strict inequalities `0 ≤ p`
(second component). -/
abbrev PolySystem := List Poly × List Poly

/-- Value of a monomial (product of the listed unknowns). -/
def monoVal (x : ℕ → ℝ) : List ℕ → ℝ
  | [] => 1
  | i :: l => x i * monoVal x l

/-- Value of a polynomial at an assignment of the real unknowns. -/
def evalR (x : ℕ → ℝ) : Poly → ℝ
  | [] => 0
  | m :: p => coefVal m.1 * monoVal x m.2 + evalR x p

/-- A polynomial system is solvable over `ℝ`. -/
def PolySystem.Holds (S : PolySystem) : Prop :=
  ∃ x : ℕ → ℝ, (∀ p ∈ S.1, evalR x p = 0) ∧ ∀ p ∈ S.2, 0 ≤ evalR x p

theorem evalR_append (x : ℕ → ℝ) (p q : Poly) : evalR x (p ++ q) = evalR x p + evalR x q := by
  induction p with
  | nil =>
    show evalR x q = 0 + evalR x q
    rw [zero_add]
  | cons m p ih =>
    show coefVal m.1 * monoVal x m.2 + evalR x (p ++ q) =
      (coefVal m.1 * monoVal x m.2 + evalR x p) + evalR x q
    rw [ih, add_assoc]

/-- Multiply every monomial by the unknown `j`. -/
def mulVar (j : ℕ) (p : Poly) : Poly := p.map fun m => (m.1, j :: m.2)

theorem evalR_mulVar (x : ℕ → ℝ) (j : ℕ) (p : Poly) :
    evalR x (mulVar j p) = x j * evalR x p := by
  induction p with
  | nil =>
    show (0 : ℝ) = x j * 0
    rw [mul_zero]
  | cons m p ih =>
    show coefVal m.1 * (x j * monoVal x m.2) + evalR x (mulVar j p) =
      x j * (coefVal m.1 * monoVal x m.2 + evalR x p)
    rw [ih]
    ring

/-- Negate a polynomial. -/
def negPoly (p : Poly) : Poly := p.map fun m => (negCoef m.1, m.2)

theorem evalR_negPoly (x : ℕ → ℝ) (p : Poly) : evalR x (negPoly p) = -evalR x p := by
  induction p with
  | nil =>
    show (0 : ℝ) = -0
    rw [neg_zero]
  | cons m p ih =>
    show coefVal (negCoef m.1) * monoVal x m.2 + evalR x (negPoly p) =
      -(coefVal m.1 * monoVal x m.2 + evalR x p)
    rw [ih, coefVal_negCoef]
    ring

/-! ### Complex polynomials in unknowns and conjugates -/

/-- A complex polynomial with integer coefficients whose letters `(k, b)` stand for the
unknown `ζ k` (`b = false`) or its conjugate (`b = true`). -/
abbrev CPoly := List (Coef × List (ℕ × Bool))

/-- Value of a letter. -/
def litC (ζ : ℕ → ℂ) (a : ℕ × Bool) : ℂ := bif a.2 then star (ζ a.1) else ζ a.1

theorem litC_false (ζ : ℕ → ℂ) (k : ℕ) : litC ζ (k, false) = ζ k := rfl

theorem litC_true (ζ : ℕ → ℂ) (k : ℕ) : litC ζ (k, true) = star (ζ k) := rfl

/-- Value of a complex monomial. -/
def monoC (ζ : ℕ → ℂ) : List (ℕ × Bool) → ℂ
  | [] => 1
  | a :: l => litC ζ a * monoC ζ l

/-- Value of a complex polynomial. -/
def evalC (ζ : ℕ → ℂ) : CPoly → ℂ
  | [] => 0
  | m :: p => (coefVal m.1 : ℂ) * monoC ζ m.2 + evalC ζ p

theorem star_re_eq (z : ℂ) : (star z).re = z.re := rfl

theorem star_im_eq (z : ℂ) : (star z).im = -z.im := rfl

/-! ### Compilation to real and imaginary parts -/

/-- Multiply a pair (real part, imaginary part) by one letter. -/
def stepMono (a : ℕ × Bool) (rs : Poly × Poly) : Poly × Poly :=
  bif a.2 then
    (mulVar (2 * a.1) rs.1 ++ mulVar (2 * a.1 + 1) rs.2,
      mulVar (2 * a.1) rs.2 ++ negPoly (mulVar (2 * a.1 + 1) rs.1))
  else
    (mulVar (2 * a.1) rs.1 ++ negPoly (mulVar (2 * a.1 + 1) rs.2),
      mulVar (2 * a.1) rs.2 ++ mulVar (2 * a.1 + 1) rs.1)

/-- Real and imaginary parts of the complex monomial `c * l`. -/
def compileMono (c : Coef) (l : List (ℕ × Bool)) : Poly × Poly :=
  l.foldr stepMono ([(c, [])], [])

/-- The complex unknowns determined by a real assignment. -/
def complexify (x : ℕ → ℝ) (k : ℕ) : ℂ := ⟨x (2 * k), x (2 * k + 1)⟩

theorem complexify_re (x : ℕ → ℝ) (k : ℕ) : (complexify x k).re = x (2 * k) := rfl

theorem complexify_im (x : ℕ → ℝ) (k : ℕ) : (complexify x k).im = x (2 * k + 1) := rfl

theorem compileMono_spec (x : ℕ → ℝ) (c : Coef) (l : List (ℕ × Bool)) :
    evalR x (compileMono c l).1 = coefVal c * (monoC (complexify x) l).re ∧
      evalR x (compileMono c l).2 = coefVal c * (monoC (complexify x) l).im := by
  induction l with
  | nil =>
    constructor
    · show coefVal c * 1 + 0 = coefVal c * (1 : ℂ).re
      rw [Complex.one_re]
      ring
    · show (0 : ℝ) = coefVal c * (1 : ℂ).im
      rw [Complex.one_im, mul_zero]
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := ih
    obtain ⟨k, b⟩ := a
    cases b
    · constructor
      · show evalR x (mulVar (2 * k) (compileMono c l).1 ++
            negPoly (mulVar (2 * k + 1) (compileMono c l).2)) =
          coefVal c * (complexify x k * monoC (complexify x) l).re
        rw [evalR_append, evalR_negPoly, evalR_mulVar, evalR_mulVar, h1, h2, Complex.mul_re,
          complexify_re, complexify_im]
        ring
      · show evalR x (mulVar (2 * k) (compileMono c l).2 ++
            mulVar (2 * k + 1) (compileMono c l).1) =
          coefVal c * (complexify x k * monoC (complexify x) l).im
        rw [evalR_append, evalR_mulVar, evalR_mulVar, h1, h2, Complex.mul_im,
          complexify_re, complexify_im]
        ring
    · constructor
      · show evalR x (mulVar (2 * k) (compileMono c l).1 ++
            mulVar (2 * k + 1) (compileMono c l).2) =
          coefVal c * (star (complexify x k) * monoC (complexify x) l).re
        rw [evalR_append, evalR_mulVar, evalR_mulVar, h1, h2, Complex.mul_re, star_re_eq,
          star_im_eq, complexify_re, complexify_im]
        ring
      · show evalR x (mulVar (2 * k) (compileMono c l).2 ++
            negPoly (mulVar (2 * k + 1) (compileMono c l).1)) =
          coefVal c * (star (complexify x k) * monoC (complexify x) l).im
        rw [evalR_append, evalR_negPoly, evalR_mulVar, evalR_mulVar, h1, h2, Complex.mul_im,
          star_re_eq, star_im_eq, complexify_re, complexify_im]
        ring

/-- Real part of a complex polynomial, as a real polynomial. -/
def compileRe (p : CPoly) : Poly := p.flatMap fun m => (compileMono m.1 m.2).1

/-- Imaginary part of a complex polynomial, as a real polynomial. -/
def compileIm (p : CPoly) : Poly := p.flatMap fun m => (compileMono m.1 m.2).2

theorem evalR_compileRe (x : ℕ → ℝ) (p : CPoly) :
    evalR x (compileRe p) = (evalC (complexify x) p).re := by
  induction p with
  | nil =>
    show (0 : ℝ) = (0 : ℂ).re
    exact Complex.zero_re.symm
  | cons m p ih =>
    show evalR x ((compileMono m.1 m.2).1 ++ compileRe p) =
      ((coefVal m.1 : ℂ) * monoC (complexify x) m.2 + evalC (complexify x) p).re
    rw [evalR_append, ih, (compileMono_spec x m.1 m.2).1, Complex.add_re, Complex.re_ofReal_mul]

theorem evalR_compileIm (x : ℕ → ℝ) (p : CPoly) :
    evalR x (compileIm p) = (evalC (complexify x) p).im := by
  induction p with
  | nil =>
    show (0 : ℝ) = (0 : ℂ).im
    exact Complex.zero_im.symm
  | cons m p ih =>
    show evalR x ((compileMono m.1 m.2).2 ++ compileIm p) =
      ((coefVal m.1 : ℂ) * monoC (complexify x) m.2 + evalC (complexify x) p).im
    rw [evalR_append, ih, (compileMono_spec x m.1 m.2).2, Complex.add_im, Complex.im_ofReal_mul]

/-! ### Complex systems -/

/-- A complex system: complex equations and real-part inequalities `0 ≤ re p`. -/
abbrev CSystem := List CPoly × List CPoly

/-- A complex system is solvable. -/
def CSystem.Holds (S : CSystem) : Prop :=
  ∃ ζ : ℕ → ℂ, (∀ p ∈ S.1, evalC ζ p = 0) ∧ ∀ p ∈ S.2, 0 ≤ (evalC ζ p).re

/-- The real system of a complex system (real and imaginary parts of each equation, real
parts of each inequality). -/
def compileSystem (S : CSystem) : PolySystem :=
  (S.1.flatMap fun p => [compileRe p, compileIm p], S.2.map compileRe)

/-- Real coordinates of complex unknowns. -/
def realify (ζ : ℕ → ℂ) (m : ℕ) : ℝ := if m % 2 = 0 then (ζ (m / 2)).re else (ζ (m / 2)).im

theorem complexify_realify (ζ : ℕ → ℂ) : complexify (realify ζ) = ζ := by
  funext k
  apply Complex.ext
  · show realify ζ (2 * k) = (ζ k).re
    have h1 : 2 * k % 2 = 0 := by omega
    have h2 : 2 * k / 2 = k := by omega
    unfold realify
    rw [if_pos h1, h2]
  · show realify ζ (2 * k + 1) = (ζ k).im
    have h1 : ¬ (2 * k + 1) % 2 = 0 := by omega
    have h2 : (2 * k + 1) / 2 = k := by omega
    unfold realify
    rw [if_neg h1, h2]

theorem holds_compileSystem (S : CSystem) :
    PolySystem.Holds (compileSystem S) ↔ CSystem.Holds S := by
  constructor
  · rintro ⟨x, hx1, hx2⟩
    refine ⟨complexify x, fun p hp => ?_, fun p hp => ?_⟩
    · have hm1 : compileRe p ∈ S.1.flatMap fun p => [compileRe p, compileIm p] :=
        List.mem_flatMap.mpr ⟨p, hp, by simp⟩
      have hm2 : compileIm p ∈ S.1.flatMap fun p => [compileRe p, compileIm p] :=
        List.mem_flatMap.mpr ⟨p, hp, by simp⟩
      have hre : evalR x (compileRe p) = 0 := hx1 _ hm1
      have him : evalR x (compileIm p) = 0 := hx1 _ hm2
      rw [evalR_compileRe] at hre
      rw [evalR_compileIm] at him
      exact Complex.ext (by rw [hre, Complex.zero_re]) (by rw [him, Complex.zero_im])
    · have hm : compileRe p ∈ S.2.map compileRe := List.mem_map.mpr ⟨p, hp, rfl⟩
      have h : 0 ≤ evalR x (compileRe p) := hx2 _ hm
      rwa [evalR_compileRe] at h
  · rintro ⟨ζ, hz1, hz2⟩
    refine ⟨realify ζ, fun q hq => ?_, fun q hq => ?_⟩
    · have hq' : q ∈ S.1.flatMap fun p => [compileRe p, compileIm p] := hq
      obtain ⟨p, hp, hqp⟩ := List.mem_flatMap.mp hq'
      rcases List.mem_cons.mp hqp with h | h
      · rw [h, evalR_compileRe, complexify_realify, hz1 p hp, Complex.zero_re]
      · rw [List.mem_singleton] at h
        rw [h, evalR_compileIm, complexify_realify, hz1 p hp, Complex.zero_im]
    · have hq' : q ∈ S.2.map compileRe := hq
      obtain ⟨p, hp, hqp⟩ := List.mem_map.mp hq'
      rw [← hqp, evalR_compileRe, complexify_realify]
      exact hz2 p hp

end

end GroupApproximation.Full.NN02c
