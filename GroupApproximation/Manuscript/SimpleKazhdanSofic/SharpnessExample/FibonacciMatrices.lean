import GroupApproximation.Manuscript.SimpleKazhdanSofic.SharpnessExample.FibonacciWords
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SubshiftMatricial
import GroupApproximation.Manuscript.SimpleKazhdanSofic.ElementaryGroupFacts
import GroupApproximation.Leavitt.ElementaryFTwoMatrixProduct
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Tactic.IntervalCases
import GroupApproximation.Meta.AxiomGuard

/-!
# An example: the model `φ` of the Fibonacci subshift with `ℓ = 1`

`simple_kazhdan_sofic_group.tex`, subsection "An example", l.413–440:

> With $\ell=1$ and $y$ in place of $y_\ell$ we get $N=5$ and the model of
> Figure~\ref{fig:models}(a): $\varphi(e_0)=I-\varphi(e_1)$ and
> [display of $\varphi(u)=P$ and $\varphi(e_1)=D_1(e_1)=\mathrm{diag}(0,1,0,0,1)$]
> with rows and columns indexed by $t=0,\dots,4$ and zeros shown as dots. The windows of $y$
> centered at $1$ and at $4$ are both $010$, so every $D_1(f)$ has equal entries at these
> positions. But $P^3D_1(e_1)P^{-3}$ is diagonal with entry $y_{t-3}$ at $t$, so
> $D_1(e_1)\,P^3D_1(e_1)P^{-3}=E_{44}$. Then $P^{t-4}E_{44}P^{4-t}=E_{tt}$ and
> $P^{t'-t}E_{tt}=E_{t't}$ give every matrix unit. So $\varphi(S)$ generates $M_5(\F_2)$, and
> the $e_{ij}(\varphi(s))$ with $s\in S$ generate $\SL_{15}(\F_2)$, as in Section~\ref{sec:proof}.

The objects are the printed ones (tex l.379–383), built concretely for `X = fibonacciSubshift`
and `y = fibonacciPeriodicWord`:

* `fibonacciPoint t ∈ X` agrees with `T^t y` on `[-1, 1]`; it exists because the window of `y`
  at `t` is a word of length `3` of `X` (`manuscriptSentence_periodicWordsLengthThree`).
* `fibonacciWindowModel f t = f(fibonacciPoint t)`, a ring hom `LC(X, F₂) → F₂^{Z/5}`; for `f`
  depending only on `[-1, 1]` this is the value of `f` at any point agreeing with `T^t y` on
  `[-1, 1]`, so `D_1(f) = diagonal (fibonacciWindowModel f)` is the printed `D_1`.
* `fibonacciModel = cutoffModel fibonacciWindowModel 1`, the printed `φ_1`:
  `Σ_j D_1(f_j) P^j` when every `f_j` depends on `[-1, 1]`, and `0` otherwise.

Route: `φ(u^j) = P^j` and `φ(e_a) = diag(1_{y_t = a})` are the corpus `cutoffModel_unit_zpow` and
the evaluation at `fibonacciPoint`; the displayed matrices, `P^3 D_1(e_1) P^{-3}`, `E_44` and the
conjugations are finite computations over `Z/5` (`decide +kernel`); generation of `M_5(F₂)` is the
corpus `subring_closure_periodicGenerators_eq_top` with the least period `5`, and generation of
`EL_3(M_5(F₂)) = GL_3(M_5(F₂)) ≅ SL_15(F₂)` is `printedElementaryGeneration` with
`ChainRadical.elementaryGroup_matrix_zmodTwo_eq_top` and block flattening.
-/

namespace GroupApproximation.SimpleKazhdanSofic.SharpnessExample

open SymbolicDynamics.FullShift Matrix Pestov91
open Multiplicative (toAdd ofAdd)

section Model

/-- A point of `X` agreeing with `T^t y` on `[-1, 1]`. -/
theorem exists_fibonacciPoint (t : ℤ) :
    ∃ z : fibonacciSubshift.carrier, ∀ i : ℤ, |i| ≤ ((1 : ℕ) : ℤ) →
      z.1 i = fibonacciPeriodicWord (t + i) := by
  have hwin : WordGraph.word fibonacciPeriodicWord (t - 1) 3 ∈
      WordGraph.language fibonacciSubshift.carrier 3 := by
    rw [← manuscriptSentence_periodicWordsLengthThree.2.2.1]
    exact ⟨t - 1, rfl⟩
  obtain ⟨z0, hz0, hz0w⟩ := hwin
  refine ⟨⟨shift (1 : ℤ) z0, fibonacciSubshift.mapsTo 1 hz0⟩, fun i hi => ?_⟩
  obtain ⟨hi1, hi2⟩ := abs_le.mp hi
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = 1 + i := ⟨(1 + i).toNat, Int.toNat_of_nonneg (by omega)⟩
  have h := congrFun hz0w ⟨j, by omega⟩
  simp only [WordGraph.word_apply, zero_add] at h
  show z0 (1 + i) = _
  rw [← hj, h]
  congr 1
  omega

/-- The chosen point of `X` agreeing with `T^t y` on `[-1, 1]`, `t = 0, …, 4`. -/
noncomputable def fibonacciPoint (t : ZMod 5) : fibonacciSubshift.carrier :=
  (exists_fibonacciPoint ((t.val : ℕ) : ℤ)).choose

theorem fibonacciPoint_spec (t : ZMod 5) (i : ℤ) (hi : |i| ≤ ((1 : ℕ) : ℤ)) :
    (fibonacciPoint t).1 i = fibonacciPeriodicWord ((t.val : ℕ) + i) :=
  (exists_fibonacciPoint ((t.val : ℕ) : ℤ)).choose_spec i hi

/-- The diagonal of `D_1`: `f ↦ (f(T^t y))_{t ∈ Z/5}`, evaluated at `fibonacciPoint t`. -/
noncomputable def fibonacciWindowModel :
    ClopenCoeff (subshiftHomeo fibonacciSubshift) (ZMod 2) →+* (ZMod 5 → ZMod 2) :=
  Pi.ringHom fun t => (LocallyConstant.evalRingHom (fibonacciPoint t)).comp
    (ClopenCoeff.of (subshiftHomeo fibonacciSubshift) (ZMod 2)).symm.toRingHom

theorem fibonacciWindowModel_apply (f : ClopenCoeff (subshiftHomeo fibonacciSubshift) (ZMod 2))
    (t : ZMod 5) :
    fibonacciWindowModel f t =
      (ClopenCoeff.of (subshiftHomeo fibonacciSubshift) (ZMod 2)).symm f (fibonacciPoint t) :=
  rfl

/-- `D_1(f)` at `t` is the value of `f` at any point of `X` agreeing with `T^t y` on `[-1, 1]`. -/
theorem fibonacciWindowModel_apply_of_agree
    (f : ClopenCoeff (subshiftHomeo fibonacciSubshift) (ZMod 2))
    (hf : DependsOnWindow (subshiftHomeo fibonacciSubshift) 1 f) (t : ZMod 5)
    (z : fibonacciSubshift.carrier)
    (hz : ∀ i : ℤ, |i| ≤ ((1 : ℕ) : ℤ) → z.1 i = fibonacciPeriodicWord ((t.val : ℕ) + i)) :
    fibonacciWindowModel f t =
      (ClopenCoeff.of (subshiftHomeo fibonacciSubshift) (ZMod 2)).symm f z := by
  rw [fibonacciWindowModel_apply]
  exact hf _ _ fun i hi => (fibonacciPoint_spec t i hi).trans (hz i hi).symm

/-- **The model `φ = φ_1`** on `R_X = LC(X, F₂) ⋊_T ℤ`, with `N = 5`. -/
noncomputable def fibonacciModel (r : SimpleKazhdanSofic.R fibonacciSubshift) :
    Matrix (ZMod 5) (ZMod 5) (ZMod 2) :=
  cutoffModel fibonacciWindowModel 1 r

/-- The unit `u` of `R_X`. -/
noncomputable abbrev fibU : SimpleKazhdanSofic.R fibonacciSubshift :=
  ((ClopenCrossedProduct.unit (subshiftHomeo fibonacciSubshift) (ZMod 2) :
    (SimpleKazhdanSofic.R fibonacciSubshift)ˣ) : SimpleKazhdanSofic.R fibonacciSubshift)

/-- The power `u^j` of `R_X`. -/
noncomputable abbrev fibUPow (j : ℤ) : SimpleKazhdanSofic.R fibonacciSubshift :=
  ((ClopenCrossedProduct.unit (subshiftHomeo fibonacciSubshift) (ZMod 2) ^ j :
    (SimpleKazhdanSofic.R fibonacciSubshift)ˣ) : SimpleKazhdanSofic.R fibonacciSubshift)

/-- The letter indicator `e_a` of `R_X`. -/
noncomputable abbrev fibLetter (a : Bool) : SimpleKazhdanSofic.R fibonacciSubshift :=
  ClopenCrossedProduct.coeff (subshiftHomeo fibonacciSubshift) (ZMod 2)
    (letterIndicator fibonacciSubshift a)

/-- The letters of `y` over `Z/5`: `t ↦ y_t`. -/
abbrev fibonacciColumn (t : ZMod 5) : Bool :=
  fibonacciPeriodicWord ((t.val : ℕ) : ℤ)

theorem fibonacciModel_eq_of (r : SimpleKazhdanSofic.R fibonacciSubshift)
    (hr : ∀ g ∈ SkewMonoidAlgebra.support r,
      DependsOnWindow (subshiftHomeo fibonacciSubshift) 1 (SkewMonoidAlgebra.coeff r g)) :
    fibonacciModel r = periodicModel fibonacciWindowModel r :=
  cutoffModel_eq_of fibonacciWindowModel hr

theorem fibonacciModel_eq_zero (r : SimpleKazhdanSofic.R fibonacciSubshift)
    (hr : ¬ ∀ g ∈ SkewMonoidAlgebra.support r,
      DependsOnWindow (subshiftHomeo fibonacciSubshift) 1 (SkewMonoidAlgebra.coeff r g)) :
    fibonacciModel r = 0 := by
  unfold fibonacciModel cutoffModel
  rw [if_neg hr]

/-- `φ(f u^j) = D_1(f) P^j` for `f` depending only on `[-1, 1]`. -/
theorem fibonacciModel_single (j : ℤ) (f : ClopenCoeff (subshiftHomeo fibonacciSubshift) (ZMod 2))
    (hf : DependsOnWindow (subshiftHomeo fibonacciSubshift) 1 f) :
    fibonacciModel (SkewMonoidAlgebra.single (ofAdd j) f) =
      Matrix.diagonal (fibonacciWindowModel f) * shiftMatrix (ZMod 2) 5 j := by
  classical
  rw [fibonacciModel_eq_of _ fun g _ => by
    rw [SkewMonoidAlgebra.coeff_single_apply]
    split_ifs
    · exact hf
    · exact dependsOnWindow_zero_or_one (Or.inl rfl), periodicModel_single, toAdd_ofAdd]

theorem fibonacciModel_one : fibonacciModel 1 = 1 :=
  cutoffModel_one fibonacciWindowModel 1

theorem fibonacciModel_unit_zpow (j : ℤ) : fibonacciModel (fibUPow j) = shiftMatrix (ZMod 2) 5 j :=
  cutoffModel_unit_zpow fibonacciWindowModel 1 j

theorem fibonacciModel_unit : fibonacciModel fibU = shiftMatrix (ZMod 2) 5 1 := by
  simpa only [zpow_one] using cutoffModel_unit_zpow fibonacciWindowModel 1 1

theorem fibonacciModel_unit_inv :
    fibonacciModel ((((ClopenCrossedProduct.unit (subshiftHomeo fibonacciSubshift) (ZMod 2))⁻¹ :
      (SimpleKazhdanSofic.R fibonacciSubshift)ˣ) : SimpleKazhdanSofic.R fibonacciSubshift)) =
      shiftMatrix (ZMod 2) 5 (-1) := by
  simpa only [zpow_neg, zpow_one] using cutoffModel_unit_zpow fibonacciWindowModel 1 (-1)

theorem dependsOnWindow_letter (a : Bool) :
    DependsOnWindow (subshiftHomeo fibonacciSubshift) 1
      (ClopenCoeff.of _ (ZMod 2) (letterIndicator fibonacciSubshift a)) :=
  fun y z hyz => by
    show (if y.1 0 = a then (1 : ZMod 2) else 0) = if z.1 0 = a then 1 else 0
    rw [hyz 0 (by simp)]

/-- `D_1(e_a) = diag(1_{y_t = a})`. -/
theorem fibonacciWindowModel_letter (a : Bool) :
    Matrix.diagonal (fibonacciWindowModel
      (ClopenCoeff.of _ (ZMod 2) (letterIndicator fibonacciSubshift a))) =
      letterDiagonal fibonacciColumn a := by
  refine congrArg Matrix.diagonal (funext fun t => ?_)
  show (if (fibonacciPoint t).1 0 = a then (1 : ZMod 2) else 0) =
    if fibonacciColumn t = a then 1 else 0
  rw [fibonacciPoint_spec t 0 (by simp), add_zero]

/-- `φ(e_a) = D_1(e_a) = diag(1_{y_t = a})`. -/
theorem fibonacciModel_letter (a : Bool) :
    fibonacciModel (fibLetter a) = letterDiagonal fibonacciColumn a := by
  show cutoffModel fibonacciWindowModel 1
    (ClopenCrossedProduct.coeff (subshiftHomeo fibonacciSubshift) (ZMod 2)
      (letterIndicator fibonacciSubshift a)) = _
  rw [ClopenCrossedProduct.coeff_apply, Pestov91.CrossedProduct.C_apply]
  have h := fibonacciModel_single 0 _ (dependsOnWindow_letter a)
  rw [ofAdd_zero, shiftMatrix_zero, mul_one, fibonacciWindowModel_letter] at h
  exact h

end Model

/-- **Sentence l.413 (tex l.413–414).** With `ℓ = 1` and `y` in place of `y_ℓ`: `N = 5` is the
least period of `y`, `y` has the words of length `2ℓ + 1 = 3` of `X`, `D_1(f)` at `t` is the value
of `f` at any point of `X` agreeing with `T^t y` on `[-1, 1]`, `φ(Σ_j f_j u^j) = Σ_j D_1(f_j) P^j`
when every `f_j` depends on `[-1, 1]` and `φ = 0` otherwise, `φ(1) = I`, and
`φ(e_0) = I - φ(e_1)`. -/
theorem manuscriptSentence_fibonacciModelSetup :
    leastPeriod fibonacciPeriodicWord = 5 ∧
      Set.range (fun i : ℤ => WordGraph.word fibonacciPeriodicWord i (2 * 1 + 1)) =
        WordGraph.language fibonacciSubshift.carrier (2 * 1 + 1) ∧
      (∀ f : ClopenCoeff (subshiftHomeo fibonacciSubshift) (ZMod 2),
        DependsOnWindow (subshiftHomeo fibonacciSubshift) 1 f → ∀ (t : ZMod 5)
          (z : fibonacciSubshift.carrier),
          (∀ i : ℤ, |i| ≤ ((1 : ℕ) : ℤ) → z.1 i = fibonacciPeriodicWord ((t.val : ℕ) + i)) →
          fibonacciWindowModel f t =
            (ClopenCoeff.of (subshiftHomeo fibonacciSubshift) (ZMod 2)).symm f z) ∧
      (∀ r : SimpleKazhdanSofic.R fibonacciSubshift,
        (∀ g ∈ SkewMonoidAlgebra.support r,
          DependsOnWindow (subshiftHomeo fibonacciSubshift) 1 (SkewMonoidAlgebra.coeff r g)) →
        fibonacciModel r = periodicModel fibonacciWindowModel r) ∧
      (∀ r : SimpleKazhdanSofic.R fibonacciSubshift,
        ¬ (∀ g ∈ SkewMonoidAlgebra.support r,
          DependsOnWindow (subshiftHomeo fibonacciSubshift) 1 (SkewMonoidAlgebra.coeff r g)) →
        fibonacciModel r = 0) ∧
      (∀ (j : ℤ) (f : ClopenCoeff (subshiftHomeo fibonacciSubshift) (ZMod 2)),
        DependsOnWindow (subshiftHomeo fibonacciSubshift) 1 f →
        fibonacciModel (SkewMonoidAlgebra.single (ofAdd j) f) =
          Matrix.diagonal (fibonacciWindowModel f) * shiftMatrix (ZMod 2) 5 j) ∧
      fibonacciModel 1 = 1 ∧
      fibonacciModel (fibLetter false) = 1 - fibonacciModel (fibLetter true) := by
  refine ⟨leastPeriod_fibonacciPeriodicWord, manuscriptSentence_periodicWordsLengthThree.2.2.1,
    fibonacciWindowModel_apply_of_agree, fibonacciModel_eq_of, fibonacciModel_eq_zero,
    fibonacciModel_single, fibonacciModel_one, ?_⟩
  rw [fibonacciModel_letter, fibonacciModel_letter]
  decide +kernel

#audit_axioms manuscriptSentence_fibonacciModelSetup

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

/-- **Display l.415 (tex l.415–432), with l.433.** `φ(u) = P` with `P δ_t = δ_{t+1}`, and
`φ(e_1) = D_1(e_1)`; in rows and columns indexed by `t = 0, …, 4` they are the displayed
matrices. -/
theorem manuscriptSentence_fibonacciDisplay :
    fibonacciModel fibU = shiftMatrix (ZMod 2) 5 1 ∧
      (∀ t : ZMod 5, shiftMatrix (ZMod 2) 5 1 *ᵥ Pi.single t 1 = Pi.single (t + 1) 1) ∧
      (∀ a b : Fin 5, fibonacciModel fibU (a.val : ZMod 5) (b.val : ZMod 5) = displayedP a b) ∧
      fibonacciModel (fibLetter true) =
        Matrix.diagonal (fibonacciWindowModel
          (ClopenCoeff.of _ (ZMod 2) (letterIndicator fibonacciSubshift true))) ∧
      ∀ a b : Fin 5,
        fibonacciModel (fibLetter true) (a.val : ZMod 5) (b.val : ZMod 5) = displayedD a b := by
  refine ⟨fibonacciModel_unit, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · rw [fibonacciModel_unit]
    decide +kernel
  · rw [fibonacciModel_letter, fibonacciWindowModel_letter]
  · rw [fibonacciModel_letter]
    decide +kernel

#audit_axioms manuscriptSentence_fibonacciDisplay

/-- **Sentence l.434 (tex l.434–435).** The windows of `y` centered at `1` and at `4` are both
`010`, so every `D_1(f)` (for `f` depending only on `[-1, 1]`) has equal entries at these
positions. -/
theorem manuscriptSentence_fibonacciWindowsEqual :
    WordGraph.word fibonacciPeriodicWord ((1 : ℤ) - 1) 3 = ![false, true, false] ∧
      WordGraph.word fibonacciPeriodicWord ((4 : ℤ) - 1) 3 = ![false, true, false] ∧
      ∀ f : ClopenCoeff (subshiftHomeo fibonacciSubshift) (ZMod 2),
        DependsOnWindow (subshiftHomeo fibonacciSubshift) 1 f →
        Matrix.diagonal (fibonacciWindowModel f) 1 1 =
          Matrix.diagonal (fibonacciWindowModel f) 4 4 := by
  refine ⟨by decide +kernel, by decide +kernel, fun f hf => ?_⟩
  rw [diagonal_apply_eq, diagonal_apply_eq, fibonacciWindowModel_apply,
    fibonacciWindowModel_apply]
  refine hf _ _ fun i hi => ?_
  rw [fibonacciPoint_spec 1 i hi, fibonacciPoint_spec 4 i hi]
  obtain ⟨hlo, hhi⟩ := abs_le.mp hi
  have hlo' : -1 ≤ i := by omega
  have hhi' : i ≤ 1 := by omega
  interval_cases i <;> decide +kernel

#audit_axioms manuscriptSentence_fibonacciWindowsEqual

/-- **Sentence l.435 (tex l.435–436).** `P^3 = φ(u^3)` with inverse `φ(u^{-3})`,
`P^3 D_1(e_1) P^{-3}` is diagonal with entry `y_{t-3}` at `t`, and
`D_1(e_1) P^3 D_1(e_1) P^{-3} = E_44`. -/
theorem manuscriptSentence_fibonacciConjugateE44 :
    fibonacciModel fibU ^ 3 = fibonacciModel (fibUPow 3) ∧
      fibonacciModel (fibUPow 3) * fibonacciModel (fibUPow (-3)) = 1 ∧
      fibonacciModel (fibUPow 3) * fibonacciModel (fibLetter true) *
          fibonacciModel (fibUPow (-3)) =
        Matrix.diagonal (fun t : ZMod 5 =>
          if fibonacciPeriodicWord (((t - ((3 : ℤ) : ZMod 5)).val : ℕ) : ℤ) = true then
            (1 : ZMod 2) else 0) ∧
      fibonacciModel (fibLetter true) *
          (fibonacciModel (fibUPow 3) * fibonacciModel (fibLetter true) *
            fibonacciModel (fibUPow (-3))) =
        Matrix.single 4 4 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [fibonacciModel_unit, fibonacciModel_unit_zpow, show (3 : ℤ) = 1 + 1 + 1 by norm_num,
      shiftMatrix_add, shiftMatrix_add, pow_three, mul_assoc]
  · rw [fibonacciModel_unit_zpow, fibonacciModel_unit_zpow, ← shiftMatrix_add, add_neg_cancel,
      shiftMatrix_zero]
  · rw [fibonacciModel_unit_zpow, fibonacciModel_unit_zpow, fibonacciModel_letter, letterDiagonal]
    exact shiftMatrix_mul_diagonal_mul_shiftMatrix_neg 3
      (fun t : ZMod 5 => if fibonacciColumn t = true then (1 : ZMod 2) else 0)
  · rw [fibonacciModel_unit_zpow, fibonacciModel_unit_zpow, fibonacciModel_letter]
    decide +kernel

#audit_axioms manuscriptSentence_fibonacciConjugateE44

/-- The translates of `y` over `Z/5` are distinct: `5` is the least period. -/
theorem fibonacci_translates_distinct :
    ∀ t t' : ZMod 5, (∀ i : ZMod 5, fibonacciColumn (t + i) = fibonacciColumn (t' + i)) →
      t = t' :=
  translates_distinct_of_leastPeriod fibonacciPeriodicWord leastPeriod_fibonacciPeriodicWord

/-- `P, P⁻¹` and the `D_1(e_a)` are images of printed generators. -/
theorem periodicGenerators_subset_fibonacciModel_image :
    periodicGenerators fibonacciColumn ⊆
      fibonacciModel '' printedGeneratorsSet fibonacciSubshift := by
  intro x hx
  rcases hx with h | ⟨a, rfl⟩
  · rcases h with rfl | rfl
    · exact ⟨fibU, Set.mem_insert_of_mem _ (Set.mem_union_left _ (Set.mem_insert _ _)),
        fibonacciModel_unit⟩
    · exact ⟨_, Set.mem_insert_of_mem _
        (Set.mem_union_left _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))),
        fibonacciModel_unit_inv⟩
  · exact ⟨fibLetter a, Set.mem_insert_of_mem _ (Set.mem_union_right _ ⟨a, rfl⟩),
      fibonacciModel_letter a⟩

/-- **Sentence l.437 (tex l.437–438).** `P^{t-4} E_44 P^{4-t} = E_tt` and `P^{t'-t} E_tt = E_{t't}`
for `t, t' = 0, …, 4`, with `P^j = φ(u^j)`; so every matrix unit lies in the subring generated by
`φ(S)`, `S = {1, u, u⁻¹} ∪ {e_a}`. -/
theorem manuscriptSentence_fibonacciMatrixUnits :
    (∀ t : ZMod 5, fibonacciModel (fibUPow (((t.val : ℕ) : ℤ) - 4)) * Matrix.single 4 4 1 *
        fibonacciModel (fibUPow (4 - ((t.val : ℕ) : ℤ))) = Matrix.single t t 1) ∧
      (∀ t t' : ZMod 5,
        fibonacciModel (fibUPow (((t'.val : ℕ) : ℤ) - ((t.val : ℕ) : ℤ))) *
          Matrix.single t t 1 = Matrix.single t' t 1) ∧
      ∀ s t : ZMod 5, Matrix.single s t (1 : ZMod 2) ∈
        Subring.closure (fibonacciModel '' printedGeneratorsSet fibonacciSubshift) := by
  refine ⟨fun t => ?_, fun t t' => ?_, fun s t => ?_⟩
  · rw [fibonacciModel_unit_zpow, fibonacciModel_unit_zpow]
    revert t
    decide +kernel
  · rw [fibonacciModel_unit_zpow]
    revert t t'
    decide +kernel
  · exact Subring.closure_mono periodicGenerators_subset_fibonacciModel_image
      (single_mem_closure fibonacciColumn fibonacci_translates_distinct s t)

#audit_axioms manuscriptSentence_fibonacciMatrixUnits

/-- `φ(S)` generates `M_5(F₂)` as a ring. -/
theorem subring_closure_fibonacciModel_image_eq_top :
    Subring.closure (fibonacciModel '' printedGeneratorsSet fibonacciSubshift) = ⊤ :=
  eq_top_iff.2 ((subring_closure_periodicGenerators_eq_top fibonacciColumn
    fibonacci_translates_distinct).ge.trans
      (Subring.closure_mono periodicGenerators_subset_fibonacciModel_image))

/-- The identification `GL_3(M_5(F₂)) ≅ GL_15(F₂) = SL_15(F₂)`, flattening blocks. -/
noncomputable def fibonacciSL15Equiv :
    (Matrix (Fin 3) (Fin 3) (Matrix (ZMod 5) (ZMod 5) (ZMod 2)))ˣ ≃*
      Matrix.SpecialLinearGroup (Fin 3 × ZMod 5) (ZMod 2) :=
  (elementaryBlockUnitEquiv (ι := Fin 3) (κ := ZMod 5) (R := ZMod 2)).trans
    (ChainRadical.unitsZModTwoEquivSL (Fin 3 × ZMod 5))

/-- **Sentence l.438 (tex l.438–440).** `φ(S)` generates `M_5(F₂)`, and the `e_ij(φ(s))` with
`s ∈ S` generate `EL_3(M_5(F₂)) = GL_3(M_5(F₂))`, whose image under block flattening is
`SL_15(F₂)`, `15 = 3 · 5`. -/
theorem manuscriptSentence_fibonacciGeneratesMatrices :
    Subring.closure (fibonacciModel '' printedGeneratorsSet fibonacciSubshift) = ⊤ ∧
      elementaryGroup (Fin 3) (Matrix (ZMod 5) (ZMod 5) (ZMod 2)) =
        Subgroup.closure {z : (Matrix (Fin 3) (Fin 3) (Matrix (ZMod 5) (ZMod 5) (ZMod 2)))ˣ |
          ∃ (i j : Fin 3) (h : i ≠ j) (s : SimpleKazhdanSofic.R fibonacciSubshift),
            s ∈ printedGeneratorsSet fibonacciSubshift ∧ elementaryUnit i j h (fibonacciModel s) = z} ∧
      Subgroup.closure {z : (Matrix (Fin 3) (Fin 3) (Matrix (ZMod 5) (ZMod 5) (ZMod 2)))ˣ |
          ∃ (i j : Fin 3) (h : i ≠ j) (s : SimpleKazhdanSofic.R fibonacciSubshift),
            s ∈ printedGeneratorsSet fibonacciSubshift ∧
              elementaryUnit i j h (fibonacciModel s) = z} = ⊤ ∧
      Subgroup.closure (fibonacciSL15Equiv.toMonoidHom ''
        {z : (Matrix (Fin 3) (Fin 3) (Matrix (ZMod 5) (ZMod 5) (ZMod 2)))ˣ |
          ∃ (i j : Fin 3) (h : i ≠ j) (s : SimpleKazhdanSofic.R fibonacciSubshift),
            s ∈ printedGeneratorsSet fibonacciSubshift ∧
              elementaryUnit i j h (fibonacciModel s) = z}) = ⊤ ∧
      Fintype.card (Fin 3 × ZMod 5) = 15 := by
  have htop := subring_closure_fibonacciModel_image_eq_top
  have h1 : (1 : Matrix (ZMod 5) (ZMod 5) (ZMod 2)) ∈
      fibonacciModel '' printedGeneratorsSet fibonacciSubshift :=
    ⟨1, Set.mem_insert _ _, fibonacciModel_one⟩
  have hgen := printedElementaryGeneration _ _ htop
  rw [Set.insert_eq_of_mem h1] at hgen
  have hle : Subgroup.closure {z : (Matrix (Fin 3) (Fin 3) (Matrix (ZMod 5) (ZMod 5) (ZMod 2)))ˣ |
      ∃ (i j : Fin 3) (h : i ≠ j) (s : Matrix (ZMod 5) (ZMod 5) (ZMod 2)),
        s ∈ fibonacciModel '' printedGeneratorsSet fibonacciSubshift ∧ elementaryUnit i j h s = z} ≤
      Subgroup.closure {z : (Matrix (Fin 3) (Fin 3) (Matrix (ZMod 5) (ZMod 5) (ZMod 2)))ˣ |
        ∃ (i j : Fin 3) (h : i ≠ j) (s : SimpleKazhdanSofic.R fibonacciSubshift),
          s ∈ printedGeneratorsSet fibonacciSubshift ∧
            elementaryUnit i j h (fibonacciModel s) = z} := by
    refine (Subgroup.closure_le _).2 fun z hz => ?_
    obtain ⟨i, j, h, _, ⟨s, hs, rfl⟩, rfl⟩ := hz
    exact Subgroup.subset_closure ⟨i, j, h, s, hs, rfl⟩
  have hge : Subgroup.closure {z : (Matrix (Fin 3) (Fin 3) (Matrix (ZMod 5) (ZMod 5) (ZMod 2)))ˣ |
      ∃ (i j : Fin 3) (h : i ≠ j) (s : SimpleKazhdanSofic.R fibonacciSubshift),
        s ∈ printedGeneratorsSet fibonacciSubshift ∧
          elementaryUnit i j h (fibonacciModel s) = z} ≤
      elementaryGroup (Fin 3) (Matrix (ZMod 5) (ZMod 5) (ZMod 2)) := by
    refine (Subgroup.closure_le _).2 fun z hz => ?_
    obtain ⟨i, j, h, s, _, rfl⟩ := hz
    exact Subgroup.subset_closure ⟨i, j, h, fibonacciModel s, rfl⟩
  have hEL : elementaryGroup (Fin 3) (Matrix (ZMod 5) (ZMod 5) (ZMod 2)) = ⊤ :=
    ChainRadical.elementaryGroup_matrix_zmodTwo_eq_top (ι := Fin 3) (ZMod 5)
  have hclosure : Subgroup.closure
      {z : (Matrix (Fin 3) (Fin 3) (Matrix (ZMod 5) (ZMod 5) (ZMod 2)))ˣ |
        ∃ (i j : Fin 3) (h : i ≠ j) (s : SimpleKazhdanSofic.R fibonacciSubshift),
          s ∈ printedGeneratorsSet fibonacciSubshift ∧
            elementaryUnit i j h (fibonacciModel s) = z} = ⊤ :=
    eq_top_iff.2 ((hEL.symm.trans hgen).trans_le hle)
  refine ⟨htop, le_antisymm (hgen.trans_le hle) hge, hclosure, ?_, ?_⟩
  · rw [← MonoidHom.map_closure, hclosure]
    exact Subgroup.map_top_of_surjective _ fibonacciSL15Equiv.surjective
  · rw [Fintype.card_prod, Fintype.card_fin, ZMod.card]

#audit_axioms manuscriptSentence_fibonacciGeneratesMatrices

end GroupApproximation.SimpleKazhdanSofic.SharpnessExample
