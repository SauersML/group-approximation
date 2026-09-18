import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableReduction.FiveStepCentralRoot
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableReduction.FiveStepReduction
import GroupApproximation.Meta.AxiomGuard

/-!
# Centrality of `K₂(5, L)` reduces to one root element (lane sk-leavitt-33c, endpoint)

Write `L = L_{𝔽₂}(1,2)`.  The target `BinaryLeavittK2FiveCentralStatement`
(`FiveStepReduction.lean`) says `K₂(5, L) ≤ Z(St_5(L))`.  This module reduces it to

  `FiveStepCentralRootStatement`: every `k ∈ K₂(5, L)` commutes with the one element
  `x_{01}(1)` of `St_5(L)`,

via the ring-independent `fiveStepCentral_K2_le_center_of_commute` (`FiveStepCentralRoot.lean`).

## LOUD: logically equivalent, smaller in proof content only

The converse is also proved (`fiveStepCentralRoot_of_binaryLeavittK2FiveCentral`), so the new
statement is **logically equivalent** to the target.  Any sufficient condition implied by a true
target has to be.  The gain is in proof content.  The target asks `K₂(5, L)` to commute with all
of `St_5(L)`.  The new statement asks it to commute with one element, `x_{01}(1)`.  The passage
from one element to the whole group (normality of the centralizer and Steinberg commutator
calculus) is proved here, over any ring.

## Truth check

`K₂(5, L) = ⊥` (Khanh, arXiv:2609.08428, Thm 5.4) gives the target, and hence the new statement
(`fiveStepCentralRoot_of_binaryLeavittSteinbergInjective`).  So both are true.

## Why the target is not proved outright (negative finding)

The claim that `K₂(n, R)` is central in `St_n(R)` for `n ≥ 3` over *every* ring is **not** a
standard theorem.  Three results are standard.
* Stable centrality, i.e. padded centrality `stab K₂(n) ≤ Z(St_{n+1})`, holds over any ring.  It
  is proved in the corpus as `map_stab_K2_le_center` (`PaddedCentral.lean`).
* Unstable centrality holds for commutative rings with `n ≥ 3` (van der Kallen).
* It also holds for quasi-finite rings with `n ≥ 5` (Tulenbaev).
For an arbitrary noncommutative ring, unstable centrality is open as far as this lane knows.
`L` is not quasi-finite: it is finitely generated, simple and infinite-dimensional over its
centre `𝔽₂`.

The conjugation argument ("`St_n` acts on `K₂` fixing generators") needs a spare index outside
the support of `k`.  It works only for `k` in the image of padding.  It does not work for a
general `k ∈ K₂(5)`.

The Leavitt refinement `D : St_4 → St_5` maps `K₂(4)` onto `K₂(5)`, and `pad = D ∘ σ`
(`FiveStepCorner.lean`).  So the target would follow from `D(K₂(4)) = pad(K₂(4))`, which is
surjective stability `K₂(4) → K₂(5)`.  That is not formally available either.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.SteinbergGroup

/-- The indices `0 ≠ 1` in `Fin 5`. -/
theorem fiveStepCentral_zero_ne_one : (0 : Fin 5) ≠ 1 := by decide

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCentral_zero_ne_one

/-- **Single-root centrality of `K₂(5, L)`**, for `L = L_{𝔽₂}(1,2)`: every element of
`K₂(5, L)` commutes with `x_{01}(1)` in `St_5(L)`.

*Why it is true.*  `K₂(5, L) = ⊥` (Khanh, arXiv:2609.08428, Thm 5.4); see
`fiveStepCentralRoot_of_binaryLeavittSteinbergInjective`.  Not proved in Lean.
*Why it is smaller.*  It is one commutation per element of `K₂(5, L)`, where the target asks
commutation with all of `St_5(L)`.  The spreading from `x_{01}(1)` to `St_5(L)` is
`fiveStepCentral_K2_le_center_of_commute`.  It is logically equivalent to the target (see
`fiveStepCentralRoot_of_binaryLeavittK2FiveCentral`). -/
def FiveStepCentralRootStatement : Prop :=
  ∀ k ∈ BooneHigman.SteinbergBasic.K2 (Fin 5) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)),
    Commute k (x (0 : Fin 5) 1 fiveStepCentral_zero_ne_one
      (1 : BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FiveStepCentralRootStatement

/-- **Endpoint.**  Single-root centrality gives centrality of `K₂(5, L)` in `St_5(L)`. -/
theorem binaryLeavittK2FiveCentral_of_fiveStepCentralRoot (h : FiveStepCentralRootStatement) :
    BinaryLeavittK2FiveCentralStatement :=
  fiveStepCentral_K2_le_center_of_commute (R := BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))
    (n := 5) (by omega) fiveStepCentral_zero_ne_one h

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittK2FiveCentral_of_fiveStepCentralRoot

/-- The converse (LOUD: equivalence).  Centrality gives single-root centrality. -/
theorem fiveStepCentralRoot_of_binaryLeavittK2FiveCentral
    (h : BinaryLeavittK2FiveCentralStatement) : FiveStepCentralRootStatement :=
  fiveStepCentral_commute_of_K2_le_center (R := BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))
    (n := 5) h fiveStepCentral_zero_ne_one

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCentralRoot_of_binaryLeavittK2FiveCentral

/-- **Truth check.**  `K₂(5, L) = ⊥` gives single-root centrality. -/
theorem fiveStepCentralRoot_of_binaryLeavittSteinbergInjective
    (h : LeavittFP.BinaryLeavittSteinbergInjectiveStatement) : FiveStepCentralRootStatement :=
  fiveStepCentralRoot_of_binaryLeavittK2FiveCentral
    (binaryLeavittK2FiveCentral_of_binaryLeavittSteinbergInjective h)

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCentralRoot_of_binaryLeavittSteinbergInjective

/-- **The step from single-root centrality and corner injectivity** (compare
`binaryLeavittK2FiveStep_of_central_of_cornerInjective`). -/
theorem fiveStepCentral_binaryLeavittK2FiveStep_of_root_of_cornerInjective
    (h : FiveStepCentralRootStatement) (hσ : BinaryLeavittFiveCornerInjectiveStatement) :
    BinaryLeavittK2FiveStepStatement :=
  binaryLeavittK2FiveStep_of_central_of_cornerInjective
    (binaryLeavittK2FiveCentral_of_fiveStepCentralRoot h) hσ

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCentral_binaryLeavittK2FiveStep_of_root_of_cornerInjective

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
