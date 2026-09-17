import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Fibonacci.Words
import GroupApproximation.Manuscript.SimpleKazhdanSofic.RingGeneration
import GroupApproximation.Pestov91.LEFCrossedProduct
import Mathlib.Data.Matrix.Basis
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.IntervalCases
import GroupApproximation.Meta.AxiomGuard

/-!
# The Fibonacci example: the model `φ = φ_1` and the displayed matrices

`simple_kazhdan_sofic_group.tex`, subsection "An example", l.413–435:

> With $\ell=1$ and $y$ in place of $y_\ell$ we get $N=5$ and the model of
> Figure~\ref{fig:models}(a): $\varphi(e_0)=I-\varphi(e_1)$ and [display of $\varphi(u)=P$ and
> $\varphi(e_1)=D_1(e_1)$] with rows and columns indexed by $t=0,\dots,4$ and zeros shown as dots.
> The windows of $y$ centered at $1$ and at $4$ are both $010$, so every $D_1(f)$ has equal
> entries at these positions.

The objects are the printed ones (tex l.375–383, proof of `thm:main`), built concretely for
`X = fibonacciSubshift` and `y = fibonacciY`:

* `fibonacciPoint t ∈ X` agrees with `T^t y` on `[-1, 1]`; it exists because the window of `y` at
  `t` is a word of length `3` of `X` (`fibonacciWordsLengthThree`, `range_word_fibonacciY`).
* `DependsOnWindowOne f`: `f` depends only on the coordinates in `[-1, 1]`.
* `fibonacciWindowModel f t = f(fibonacciPoint t)`; for `f` depending only on `[-1, 1]` this is
  the value of `f` at any point of `X` agreeing with `T^t y` on `[-1, 1]`, so
  `D_1(f) = diagonal (fibonacciWindowModel f)` is the printed `D_1`.
* `fibonacciModel`, the printed `φ_1`: `Σ_j D_1(f_j) P^j` when every `f_j` depends on `[-1, 1]`,
  and `0` otherwise, where `P = shiftMatrix`, `P δ_t = δ_{t+1}`.

Main statements: `fibonacciModelSetup` (l.413–414), `fibonacciDisplay` (l.415–433),
`fibonacciWindowsEqual` (l.434–435).
-/

namespace GroupApproximation.Full.SK08

open SymbolicDynamics.FullShift
open Multiplicative (ofAdd toAdd)

/-- The shift homeomorphism `T` of the Fibonacci subshift. -/
local notation "𝓣" => SimpleKazhdanSofic.subshiftHomeo fibonacciSubshift

/-- The ring `R_X = LC(X, F₂) ⋊_T ℤ` of the Fibonacci subshift. -/
local notation "𝓡" => SimpleKazhdanSofic.R fibonacciSubshift

/-- The coefficient ring `LC(X, F₂)` of `R_X`. -/
local notation "𝓒" => ClopenCoeff (SimpleKazhdanSofic.subshiftHomeo fibonacciSubshift) (ZMod 2)

section Model

/-- A point of `X` agreeing with `T^t y` on `[-1, 1]` (tex l.379–381). -/
theorem exists_fibonacciPoint (t : ℤ) :
    ∃ z : fibonacciSubshift.carrier, ∀ i : ℤ, |i| ≤ 1 → z.1 i = fibonacciY (t + i) := by
  have hwin : WordGraph.word fibonacciY (t - 1) 3 ∈
      WordGraph.language fibonacciSubshift.carrier 3 := by
    rw [fibonacciWordsLengthThree, ← range_word_fibonacciY]
    exact ⟨t - 1, rfl⟩
  obtain ⟨z0, hz0, hz0w⟩ := hwin
  refine ⟨⟨shift (1 : ℤ) z0, fibonacciSubshift.mapsTo 1 hz0⟩, fun i hi => ?_⟩
  obtain ⟨hi1, hi2⟩ := abs_le.mp hi
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = 1 + i :=
    ⟨(1 + i).toNat, Int.toNat_of_nonneg (by omega)⟩
  have h : z0 (0 + ((j : ℕ) : ℤ)) = fibonacciY (t - 1 + ((j : ℕ) : ℤ)) :=
    congrFun hz0w ⟨j, by omega⟩
  rw [zero_add] at h
  show z0 (1 + i) = _
  rw [← hj, h]
  congr 1
  omega

/-- The chosen point of `X` agreeing with `T^t y` on `[-1, 1]`, `t = 0, …, 4`. -/
noncomputable def fibonacciPoint (t : ZMod 5) : fibonacciSubshift.carrier :=
  (exists_fibonacciPoint ((t.val : ℕ) : ℤ)).choose

theorem fibonacciPoint_spec (t : ZMod 5) (i : ℤ) (hi : |i| ≤ 1) :
    (fibonacciPoint t).1 i = fibonacciY ((t.val : ℕ) + i) :=
  (exists_fibonacciPoint ((t.val : ℕ) : ℤ)).choose_spec i hi

/-- `f` depends only on the coordinates in `[-1, 1]` (tex l.379). -/
def DependsOnWindowOne (f : 𝓒) : Prop :=
  ∀ y z : fibonacciSubshift.carrier, (∀ i : ℤ, |i| ≤ 1 → y.1 i = z.1 i) →
    (ClopenCoeff.of 𝓣 (ZMod 2)).symm f y = (ClopenCoeff.of 𝓣 (ZMod 2)).symm f z

theorem dependsOnWindowOne_zero_or_one {f : 𝓒} (hf : f = 0 ∨ f = 1) : DependsOnWindowOne f := by
  rcases hf with rfl | rfl <;> exact fun _ _ _ => rfl

theorem dependsOnWindowOne_letter (a : Bool) :
    DependsOnWindowOne
      (ClopenCoeff.of 𝓣 (ZMod 2) (SimpleKazhdanSofic.letterIndicator fibonacciSubshift a)) :=
  fun y z hyz => by
    show (if y.1 0 = a then (1 : ZMod 2) else 0) = if z.1 0 = a then 1 else 0
    rw [hyz 0 (by norm_num)]

/-- The diagonal of `D_1`: `f ↦ (f(T^t y))_{t ∈ Z/5}`, evaluated at `fibonacciPoint t`. -/
noncomputable def fibonacciWindowModel : 𝓒 →+* (ZMod 5 → ZMod 2) :=
  RingHom.pi fun t => (LocallyConstant.evalRingHom (fibonacciPoint t)).comp
    (ClopenCoeff.of 𝓣 (ZMod 2)).symm.toRingHom

theorem fibonacciWindowModel_apply (f : 𝓒) (t : ZMod 5) :
    fibonacciWindowModel f t = (ClopenCoeff.of 𝓣 (ZMod 2)).symm f (fibonacciPoint t) :=
  rfl

/-- `D_1(f)` at `t` is the value of `f` at any point of `X` agreeing with `T^t y` on `[-1, 1]`
(tex l.380–381). -/
theorem fibonacciWindowModel_apply_of_agree (f : 𝓒) (hf : DependsOnWindowOne f) (t : ZMod 5)
    (z : fibonacciSubshift.carrier)
    (hz : ∀ i : ℤ, |i| ≤ 1 → z.1 i = fibonacciY ((t.val : ℕ) + i)) :
    fibonacciWindowModel f t = (ClopenCoeff.of 𝓣 (ZMod 2)).symm f z := by
  rw [fibonacciWindowModel_apply]
  exact hf _ _ fun i hi => (fibonacciPoint_spec t i hi).trans (hz i hi).symm

/-- `D_1(e_a) = diag(1_{y_t = a})`. -/
theorem fibonacciWindowModel_letter (a : Bool) :
    fibonacciWindowModel
        (ClopenCoeff.of 𝓣 (ZMod 2) (SimpleKazhdanSofic.letterIndicator fibonacciSubshift a)) =
      fun t : ZMod 5 => if fibonacciY ((t.val : ℕ) : ℤ) = a then (1 : ZMod 2) else 0 := by
  funext t
  show (if (fibonacciPoint t).1 0 = a then (1 : ZMod 2) else 0) =
    if fibonacciY ((t.val : ℕ) : ℤ) = a then 1 else 0
  rw [fibonacciPoint_spec t 0 (by norm_num), add_zero]

/-- **The model `φ = φ_1`** on `R_X`, with `N = 5` (tex l.382–383): `Σ_j D_1(f_j) P^j` when every
`f_j` depends only on `[-1, 1]`, and `0` otherwise. -/
noncomputable def fibonacciModel (r : 𝓡) : Matrix (ZMod 5) (ZMod 5) (ZMod 2) := by
  classical
  exact if ∀ g ∈ SkewMonoidAlgebra.support r, DependsOnWindowOne (SkewMonoidAlgebra.coeff r g)
    then Pestov91.periodicModel fibonacciWindowModel r else 0

theorem fibonacciModel_eq_of (r : 𝓡)
    (hr : ∀ g ∈ SkewMonoidAlgebra.support r, DependsOnWindowOne (SkewMonoidAlgebra.coeff r g)) :
    fibonacciModel r = Pestov91.periodicModel fibonacciWindowModel r := by
  unfold fibonacciModel
  split
  · rfl
  · contradiction

theorem fibonacciModel_eq_zero (r : 𝓡)
    (hr : ¬ ∀ g ∈ SkewMonoidAlgebra.support r,
      DependsOnWindowOne (SkewMonoidAlgebra.coeff r g)) :
    fibonacciModel r = 0 := by
  unfold fibonacciModel
  split
  · contradiction
  · rfl

theorem fibonacciModel_single_of (g : Multiplicative ℤ) (f : 𝓒) (hf : DependsOnWindowOne f) :
    fibonacciModel (SkewMonoidAlgebra.single g f) =
      Matrix.diagonal (fibonacciWindowModel f) * Pestov91.shiftMatrix (ZMod 2) 5 (toAdd g) := by
  have hr : ∀ g' ∈ SkewMonoidAlgebra.support (SkewMonoidAlgebra.single g f),
      DependsOnWindowOne (SkewMonoidAlgebra.coeff (SkewMonoidAlgebra.single g f) g') := by
    intro _ _
    rw [SkewMonoidAlgebra.coeff_single_apply]
    split
    · exact hf
    · exact dependsOnWindowOne_zero_or_one (Or.inl rfl)
  rw [fibonacciModel_eq_of _ hr, Pestov91.periodicModel_single]

/-- `φ(f u^j) = D_1(f) P^j` for `f` depending only on `[-1, 1]`. -/
theorem fibonacciModel_single (j : ℤ) (f : 𝓒) (hf : DependsOnWindowOne f) :
    fibonacciModel (SkewMonoidAlgebra.single (ofAdd j) f) =
      Matrix.diagonal (fibonacciWindowModel f) * Pestov91.shiftMatrix (ZMod 2) 5 j :=
  fibonacciModel_single_of (ofAdd j) f hf

theorem fibonacciModel_single_one (g : Multiplicative ℤ) :
    fibonacciModel (SkewMonoidAlgebra.single g 1) = Pestov91.shiftMatrix (ZMod 2) 5 (toAdd g) := by
  rw [fibonacciModel_single_of g 1 (dependsOnWindowOne_zero_or_one (Or.inr rfl)), map_one,
    Matrix.diagonal_one', one_mul]

/-- `φ(1) = I` (tex l.391). -/
theorem fibonacciModel_one : fibonacciModel 1 = 1 := by
  show fibonacciModel (SkewMonoidAlgebra.single 1 1) = 1
  rw [fibonacciModel_single_one]
  exact Pestov91.shiftMatrix_zero

/-- The unit `u` of `R_X`. -/
noncomputable abbrev fibU : 𝓡 :=
  ((ClopenCrossedProduct.unit 𝓣 (ZMod 2) : 𝓡ˣ) : 𝓡)

/-- The unit `u⁻¹` of `R_X`. -/
noncomputable abbrev fibUInv : 𝓡 :=
  (((ClopenCrossedProduct.unit 𝓣 (ZMod 2))⁻¹ : 𝓡ˣ) : 𝓡)

/-- The letter indicator `e_a` of `R_X`. -/
noncomputable abbrev fibLetter (a : Bool) : 𝓡 :=
  ClopenCrossedProduct.coeff 𝓣 (ZMod 2) (SimpleKazhdanSofic.letterIndicator fibonacciSubshift a)

/-- `φ(u^j) = P^j`. -/
theorem fibonacciModel_unit_zpow (j : ℤ) :
    fibonacciModel ((ClopenCrossedProduct.unit 𝓣 (ZMod 2) ^ j : 𝓡ˣ) : 𝓡) =
      Pestov91.shiftMatrix (ZMod 2) 5 j := by
  have h : ((ClopenCrossedProduct.unit 𝓣 (ZMod 2) ^ j : 𝓡ˣ) : 𝓡) =
      SkewMonoidAlgebra.single (ofAdd j) 1 :=
    Pestov91.CrossedProduct.val_unit_zpow j
  rw [h]
  exact fibonacciModel_single_one (ofAdd j)

/-- `φ(u) = P`. -/
theorem fibonacciModel_unit : fibonacciModel fibU = Pestov91.shiftMatrix (ZMod 2) 5 1 := by
  have h := fibonacciModel_unit_zpow 1
  rw [zpow_one] at h
  exact h

/-- `φ(u⁻¹) = P⁻¹ = P^{-1}`. -/
theorem fibonacciModel_unit_inv : fibonacciModel fibUInv = Pestov91.shiftMatrix (ZMod 2) 5 (-1) := by
  have h := fibonacciModel_unit_zpow (-1)
  rw [zpow_neg, zpow_one] at h
  exact h

/-- `φ(e_a) = D_1(e_a) = diag(1_{y_t = a})`. -/
theorem fibonacciModel_letter (a : Bool) :
    fibonacciModel (fibLetter a) =
      Matrix.diagonal fun t : ZMod 5 =>
        if fibonacciY ((t.val : ℕ) : ℤ) = a then (1 : ZMod 2) else 0 := by
  have h : fibonacciModel (SkewMonoidAlgebra.single 1
      (ClopenCoeff.of 𝓣 (ZMod 2) (SimpleKazhdanSofic.letterIndicator fibonacciSubshift a))) =
      Matrix.diagonal (fibonacciWindowModel
        (ClopenCoeff.of 𝓣 (ZMod 2) (SimpleKazhdanSofic.letterIndicator fibonacciSubshift a))) *
        Pestov91.shiftMatrix (ZMod 2) 5 0 :=
    fibonacciModel_single 0 _ (dependsOnWindowOne_letter a)
  rw [Pestov91.shiftMatrix_zero, mul_one, fibonacciWindowModel_letter] at h
  exact h

/-- `φ(e_0) = I - φ(e_1)` (tex l.414). -/
theorem fibonacciModel_letter_false :
    fibonacciModel (fibLetter false) = 1 - fibonacciModel (fibLetter true) := by
  rw [fibonacciModel_letter, fibonacciModel_letter]
  ext a b
  revert a b
  decide +kernel

end Model

/-- **Sentence l.413 (tex l.413–414).** With `ℓ = 1` and `y` in place of `y_ℓ`: `N = 5` is the
least period of `y`, `y` has the words of length `2ℓ + 1 = 3` of `X`, `D_1(f)` at `t` is the value
of `f` at any point of `X` agreeing with `T^t y` on `[-1, 1]`, `φ(Σ_j f_j u^j) = Σ_j D_1(f_j) P^j`
when every `f_j` depends on `[-1, 1]` and `φ = 0` otherwise, `φ(1) = I`, and
`φ(e_0) = I - φ(e_1)`. -/
theorem fibonacciModelSetup :
    Function.minimalPeriod (shift (1 : ℤ)) fibonacciY = 5 ∧
      Set.range (fun i : ℤ => WordGraph.word fibonacciY i 3) =
        WordGraph.language fibonacciSubshift.carrier 3 ∧
      (∀ f : 𝓒, DependsOnWindowOne f → ∀ (t : ZMod 5) (z : fibonacciSubshift.carrier),
        (∀ i : ℤ, |i| ≤ 1 → z.1 i = fibonacciY ((t.val : ℕ) + i)) →
          fibonacciWindowModel f t = (ClopenCoeff.of 𝓣 (ZMod 2)).symm f z) ∧
      (∀ r : 𝓡, (∀ g ∈ SkewMonoidAlgebra.support r,
          DependsOnWindowOne (SkewMonoidAlgebra.coeff r g)) →
        fibonacciModel r = Pestov91.periodicModel fibonacciWindowModel r) ∧
      (∀ r : 𝓡, ¬ (∀ g ∈ SkewMonoidAlgebra.support r,
          DependsOnWindowOne (SkewMonoidAlgebra.coeff r g)) →
        fibonacciModel r = 0) ∧
      (∀ (j : ℤ) (f : 𝓒), DependsOnWindowOne f →
        fibonacciModel (SkewMonoidAlgebra.single (ofAdd j) f) =
          Matrix.diagonal (fibonacciWindowModel f) * Pestov91.shiftMatrix (ZMod 2) 5 j) ∧
      fibonacciModel 1 = 1 ∧
      fibonacciModel (fibLetter false) = 1 - fibonacciModel (fibLetter true) :=
  ⟨minimalPeriod_fibonacciY, range_word_fibonacciY.trans fibonacciWordsLengthThree.symm,
    fibonacciWindowModel_apply_of_agree, fibonacciModel_eq_of, fibonacciModel_eq_zero,
    fibonacciModel_single, fibonacciModel_one, fibonacciModel_letter_false⟩

#audit_axioms GroupApproximation.Full.SK08.fibonacciModelSetup

/-- The displayed matrix `P` (tex l.417–421), rows and columns indexed by `t = 0, …, 4`. -/
def displayedP : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 0, 0, 0, 1;
     1, 0, 0, 0, 0;
     0, 1, 0, 0, 0;
     0, 0, 1, 0, 0;
     0, 0, 0, 1, 0]

/-- The displayed matrix `D_1(e_1)` (tex l.424–428), rows and columns indexed by `t = 0, …, 4`. -/
def displayedD : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 0, 0, 0, 0;
     0, 1, 0, 0, 0;
     0, 0, 0, 0, 0;
     0, 0, 0, 0, 0;
     0, 0, 0, 0, 1]

/-- `P δ_t = δ_{t+1}` (tex l.378). -/
theorem shiftMatrix_mulVec_single (t : ZMod 5) :
    Matrix.mulVec (Pestov91.shiftMatrix (ZMod 2) 5 1) (Pi.single t 1) = Pi.single (t + 1) 1 := by
  rw [Matrix.mulVec_single_one]
  funext a
  show Pestov91.shiftMatrix (ZMod 2) 5 1 a t = Pi.single (t + 1) (1 : ZMod 2) a
  rw [Pestov91.shiftMatrix_apply, Int.cast_one, Pi.single_apply]
  by_cases h : a = t + 1
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg fun h' => h h'.symm, if_neg h]

/-- **Display l.415 (tex l.415–433).** `φ(u) = P` with `P δ_t = δ_{t+1}`, and
`φ(e_1) = D_1(e_1)`; in rows and columns indexed by `t = 0, …, 4` they are the displayed
matrices. -/
theorem fibonacciDisplay :
    fibonacciModel fibU = Pestov91.shiftMatrix (ZMod 2) 5 1 ∧
      (∀ t : ZMod 5, Matrix.mulVec (Pestov91.shiftMatrix (ZMod 2) 5 1) (Pi.single t 1) =
        Pi.single (t + 1) 1) ∧
      (∀ a b : Fin 5, fibonacciModel fibU ((a : ℕ) : ZMod 5) ((b : ℕ) : ZMod 5) =
        displayedP a b) ∧
      fibonacciModel (fibLetter true) =
        Matrix.diagonal (fibonacciWindowModel
          (ClopenCoeff.of 𝓣 (ZMod 2) (SimpleKazhdanSofic.letterIndicator fibonacciSubshift true))) ∧
      ∀ a b : Fin 5, fibonacciModel (fibLetter true) ((a : ℕ) : ZMod 5) ((b : ℕ) : ZMod 5) =
        displayedD a b := by
  refine ⟨fibonacciModel_unit, shiftMatrix_mulVec_single, ?_,
    (fibonacciModel_letter true).trans
      (congrArg Matrix.diagonal (fibonacciWindowModel_letter true).symm), ?_⟩
  · rw [fibonacciModel_unit]
    decide +kernel
  · rw [fibonacciModel_letter]
    decide +kernel

#audit_axioms GroupApproximation.Full.SK08.fibonacciDisplay

/-- **Sentence l.434 (tex l.434–435).** The windows of `y` centered at `1` and at `4` are both
`010`, so every `D_1(f)` (for `f` depending only on `[-1, 1]`) has equal entries at these
positions. -/
theorem fibonacciWindowsEqual :
    WordGraph.word fibonacciY ((1 : ℤ) - 1) 3 = ![false, true, false] ∧
      WordGraph.word fibonacciY ((4 : ℤ) - 1) 3 = ![false, true, false] ∧
      ∀ f : 𝓒, DependsOnWindowOne f →
        Matrix.diagonal (fibonacciWindowModel f) 1 1 =
          Matrix.diagonal (fibonacciWindowModel f) 4 4 := by
  refine ⟨by decide +kernel, by decide +kernel, fun f hf => ?_⟩
  rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, fibonacciWindowModel_apply,
    fibonacciWindowModel_apply]
  refine hf _ _ fun i hi => ?_
  rw [fibonacciPoint_spec 1 i hi, fibonacciPoint_spec 4 i hi]
  obtain ⟨hlo, hhi⟩ := abs_le.mp hi
  interval_cases i <;> decide +kernel

#audit_axioms GroupApproximation.Full.SK08.fibonacciWindowsEqual

end GroupApproximation.Full.SK08
