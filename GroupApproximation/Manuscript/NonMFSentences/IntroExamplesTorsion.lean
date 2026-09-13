import GroupApproximation.Algebra.IdempotentSwapInvolution
import GroupApproximation.Algebra.PurelyInfiniteWholeRingCornerUnits
import GroupApproximation.Manuscript.OneSidedMFRadical.UnitGroupHeadline
import GroupApproximation.Manuscript.NonMFSentences.LeavittMFQuotientSentences
import GroupApproximation.Sofic.CliffordWitnessDirectDefect
import GroupApproximation.Sofic.LiteralNonMFLinearWitness
import GroupApproximation.Meta.AxiomGuard

/-!
# Every example of the introduction before `thm:torsion-free` has torsion

`non_mf_groups_exist.tex`, Introduction (tex 292–293):

> Every example above has torsion, and in the lamp construction the obstruction is itself a torsion element.

The examples above are:
* the headline group `H = L_{𝔽₂}(1,2)^×` (`thm:headline`);
* `GL_n(R)` for a countable purely infinite simple ring `R`, and the unit groups of `L_k(1,d)` (tex 243–247);
* the elementary and general linear groups over the crossed products `R_X` over a finite field (tex 249–259);
* the group `W` of `thm:amenable-trace`.

Torsion comes from two mechanisms.
* A ring with a one-sided inverse pair `ts = 1 ≠ st` contains the swap involution of the equivalent orthogonal
  idempotents `1 - st` and `s(1 - st)t` (`IdempotentSwap`). This covers `H` and every purely infinite simple ring.
* Over a nontrivial ring with `p · 1 = 0`, the elementary matrix `e_{12}(1)` has order dividing `p`. This covers the
  groups over `R_X`.

In the lamp construction the obstruction is the central Clifford sign `ε`. It is killed by every homomorphism to an
MF group (`prop:clifford-self-embedding`), and it is an involution: `ε² = 1` and `ε ≠ 1`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences
namespace IntroExamplesTorsion

open MFQuotientUnits

/-- `e_{ij}(a)^m = e_{ij}(m • a)`. -/
theorem elementaryUnit_pow {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R] (i j : ι) (h : i ≠ j)
    (a : R) (m : ℕ) : elementaryUnit i j h a ^ m = elementaryUnit i j h (m • a) := by
  induction m with
  | zero => rw [pow_zero, zero_nsmul, elementaryUnit_zero]
  | succ m ih => rw [pow_succ, ih, elementaryUnit_mul, succ_nsmul]

/-- **Torsion in elementary groups of positive characteristic.** Over a nontrivial ring with `p · 1 = 0`, `p > 0`,
the elementary matrix `e_{12}(1)` is a nontrivial element of `EL_n(R)` of finite order, for every `n ≥ 2`. -/
theorem exists_elementary_torsion (R : Type*) [Ring R] [Nontrivial R] (p : ℕ) (hp : 0 < p)
    (hchar : (p : R) = 0) (n : ℕ) (hn : 2 ≤ n) :
    ∃ g ∈ elementaryGroup (Fin n) R, g ≠ 1 ∧ IsOfFinOrder g := by
  have hij : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := Fin.ne_of_val_ne (by simp)
  refine ⟨elementaryUnit _ _ hij 1, elementaryUnit_mem _ _ hij 1, ?_, ?_⟩
  · intro h1
    exact one_ne_zero (elementaryUnit_injective _ _ hij (h1.trans (elementaryUnit_zero _ _ hij).symm))
  · refine isOfFinOrder_iff_pow_eq_one.2 ⟨p, hp, ?_⟩
    rw [elementaryUnit_pow, nsmul_eq_mul, mul_one, hchar, elementaryUnit_zero]

/-- **Torsion in the units of a purely infinite simple ring.** -/
theorem exists_units_torsion_of_isPurelyInfiniteSimpleRing (R : Type*) [Ring R]
    (hR : IsPurelyInfiniteSimpleRing R) : ∃ g : Rˣ, g ≠ 1 ∧ IsOfFinOrder g := by
  obtain ⟨s, t, hts, hst⟩ := exists_unitProperIsometry hR
  exact IdempotentSwap.exists_isOfFinOrder_ne_one_of_isometry s t hts hst

/-- **Torsion in `GL_n(R)`, `n ≥ 1`, for a purely infinite simple ring `R`**: the scalar copy of a torsion unit. -/
theorem exists_matrixUnits_torsion_of_isPurelyInfiniteSimpleRing (R : Type*) [Ring R]
    (hR : IsPurelyInfiniteSimpleRing R) (n : ℕ) (hn : 1 ≤ n) :
    ∃ g : (Matrix (Fin n) (Fin n) R)ˣ, g ≠ 1 ∧ IsOfFinOrder g := by
  obtain ⟨u, hu, hfin⟩ := exists_units_torsion_of_isPurelyInfiniteSimpleRing R hR
  have hn0 : 0 < n := by omega
  let φ : Rˣ →* (Matrix (Fin n) (Fin n) R)ˣ := Units.map (Matrix.scalar (Fin n) : R →+* _).toMonoidHom
  refine ⟨φ u, ?_, φ.isOfFinOrder hfin⟩
  intro h
  apply hu
  apply Units.ext
  have h00 := congrArg (fun z : (Matrix (Fin n) (Fin n) R)ˣ ↦ (z : Matrix (Fin n) (Fin n) R) ⟨0, hn0⟩ ⟨0, hn0⟩) h
  have h1 : (φ u : Matrix (Fin n) (Fin n) R) = Matrix.scalar (Fin n) (u : R) := rfl
  have h2 : (φ u : Matrix (Fin n) (Fin n) R) ⟨0, hn0⟩ ⟨0, hn0⟩ = (u : R) := by
    rw [h1, Matrix.scalar_apply, Matrix.diagonal_apply_eq]
  have h3 : ((1 : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R) ⟨0, hn0⟩ ⟨0, hn0⟩ = 1 := by
    rw [Units.val_one, Matrix.one_apply_eq]
  exact h2.symm.trans (h00.trans h3)

/-- **tex 292–293 as printed.** Each example of the introduction before `thm:torsion-free` has a nontrivial element
of finite order, and in the lamp construction the obstruction `ε` is an involution that every homomorphism to an MF
group kills. -/
def PrintedIntroExamplesTorsion : Prop :=
  -- `thm:headline`: `H = L_{𝔽₂}(1,2)^×`.
  (∃ g : UniversalLeavitt.BinaryLeavittAlgebraˣ, g ≠ 1 ∧ IsOfFinOrder g) ∧
  -- tex 243–246: `GL_n(R)` for a purely infinite simple ring `R`, `n ≥ 1`.
  (∀ (R : Type) [Ring R], IsPurelyInfiniteSimpleRing R → ∀ n : ℕ, 1 ≤ n →
    ∃ g : (Matrix (Fin n) (Fin n) R)ˣ, g ≠ 1 ∧ IsOfFinOrder g) ∧
  -- tex 246–247: the unit groups of `L_k(1,d)`.
  (∀ (k : Type) [Field k] [Countable k] (d : ℕ), 2 ≤ d →
    ∃ g : (AryLeavitt.AryLeavittAlgebra k d)ˣ, g ≠ 1 ∧ IsOfFinOrder g) ∧
  -- tex 249–259: `EL_n` (hence `GL_n`) over a nontrivial ring of positive characteristic, `n ≥ 2`.
  (∀ (R : Type) [Ring R] [Nontrivial R] (p : ℕ), 0 < p → (p : R) = 0 → ∀ n : ℕ, 2 ≤ n →
    ∃ g ∈ elementaryGroup (Fin n) R, g ≠ 1 ∧ IsOfFinOrder g) ∧
  -- `thm:amenable-trace`: the group `W`.
  (∃ g : LiteralNonMFLinearWitness.WitnessGroup, g ≠ 1 ∧ IsOfFinOrder g) ∧
  -- The lamp obstruction: the central sign `ε` of every Clifford witness is an involution, killed by MF targets.
  (∀ (Γ : Type) [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α),
    MarkedCompression.signAmbient α hα ≠ 1 ∧ MarkedCompression.signAmbient α hα ^ 2 = 1 ∧
      (∀ g, Commute (MarkedCompression.signAmbient α hα) g) ∧
      ∀ [Countable Γ] (a : Γ), a ∉ Set.range α → HasKazhdanPropertyT.{0, 0} Γ →
        ∀ (M : Type) [Group M], IsOperatorMF M → ∀ f : MarkedCompression.Ambient α hα →* M,
          f (MarkedCompression.signAmbient α hα) = 1)

theorem manuscriptIntroExamplesTorsion : PrintedIntroExamplesTorsion := by
  refine ⟨?_, fun R _ hR n hn ↦ exists_matrixUnits_torsion_of_isPurelyInfiniteSimpleRing R hR n hn,
    fun k _ _ d hd ↦ exists_units_torsion_of_isPurelyInfiniteSimpleRing _
      (LeavittMFQuotientSentences.isPurelyInfiniteSimpleRing_aryLeavitt k d hd),
    fun R _ _ p hp hchar n hn ↦ exists_elementary_torsion R p hp hchar n hn, ?_, ?_⟩
  · obtain ⟨-, -, hnt, -⟩ := OneSidedMFRadical.UnitGroupHeadline.manuscriptUnitGroupHeadline
    haveI : Nontrivial UniversalLeavitt.BinaryLeavittAlgebra := by
      obtain ⟨x, y, hxy⟩ := exists_pair_ne UniversalLeavitt.BinaryLeavittAlgebraˣ
      exact ⟨⟨(x : UniversalLeavitt.BinaryLeavittAlgebra), (y : UniversalLeavitt.BinaryLeavittAlgebra),
        fun h ↦ hxy (Units.ext h)⟩⟩
    exact IdempotentSwap.exists_isOfFinOrder_ne_one_of_orthogonalIsometries
      UniversalLeavitt.family.s0 UniversalLeavitt.family.s1 UniversalLeavitt.family.t0
      UniversalLeavitt.family.t1 UniversalLeavitt.family.t0_s0 UniversalLeavitt.family.t0_s1
      UniversalLeavitt.family.t1_s0 UniversalLeavitt.family.t1_s1
  · exact ⟨MarkedCompression.signAmbient _ _, MarkedCompression.signAmbient_ne_one _ _,
      isOfFinOrder_iff_pow_eq_one.2 ⟨2, two_pos, MarkedCompression.signAmbient_sq _ _⟩⟩
  · intro Γ _ α hα
    refine ⟨MarkedCompression.signAmbient_ne_one α hα, MarkedCompression.signAmbient_sq α hα,
      MarkedCompression.signAmbient_central α hα, ?_⟩
    intro _ a ha hT M _ hM f
    exact CliffordWitnessDirectDefect.manuscriptMapSignEqOneOfIsOperatorMFTarget.{0} Γ α hα ha hT M hM f

end IntroExamplesTorsion
end NonMFSentences
end Manuscript
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.Manuscript.NonMFSentences.IntroExamplesTorsion.exists_elementary_torsion
#audit_axioms
  GroupApproximation.Manuscript.NonMFSentences.IntroExamplesTorsion.exists_matrixUnits_torsion_of_isPurelyInfiniteSimpleRing
#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.IntroExamplesTorsion.manuscriptIntroExamplesTorsion
