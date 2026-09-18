import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableReduction.Superperfect
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.Endpoints
import GroupApproximation.Meta.AxiomGuard

/-!
# The part of stable `K₂(L_{𝔽₂}(1,2)) = 0` that is actually used (lane sk-leavitt-24)

Let `L = L_{𝔽₂}(1,2)` (`BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)`).

## What the manuscript uses

`simple_kazhdan_sofic_group.tex` never mentions `K₂` or Leavitt algebras.  The only sentence
this chain serves is tex l.733–735 (`sec:questions`): "Infinite finitely presented simple Kazhdan
groups exist~\cite{CapraceRemy}, ...".  The manuscript cites Caprace–Rémy.  The Lean route
chosen by the formalisation replaces that citation by `EL_5(L)`
(`FPSimpleKazhdan.BinaryLeavittElementaryFinitelyPresentedStatement`).

## Where `BinaryLeavittStableK2TrivialStatement` is consumed

A grep shows two consumers, both in `StableReduction`:

* `binaryLeavittSteinbergInjective_of_stable hS hT : K₂(5, L) = ⊥`;
* `binaryLeavittUnitsSuperperfect_of_stable hS hT`, which goes through the first one.

(`BinaryCohnStableK2TrivialStatement` is consumed only on the way to
`BinaryLeavittStableK2TrivialStatement`, in `CohnTwo` and `CohnK2`.)  Both consumers use `hS` once,
at `n = 5`, and always together with `hT : BinaryLeavittK2FiveStabilityStatement`.

So the weakest property used is `LeavittK2UsedStatement`: every element of `K₂(5, L)` dies in some
`St_N(L)`.  It is the rank-five instance of stable triviality (`leavittK2Used_of_binaryLeavittStableK2Trivial`),
and the consumers are re-proved from it (`binaryLeavittSteinbergInjective_of_leavittK2Used`, ...).

## LOUD: stable `K₂(L) = 0` is neither needed nor sufficient for the endpoint

* **Not sufficient.**  Every consumer also needs `BinaryLeavittK2FiveStabilityStatement`
  (injective stability from rank five).  That is homological stability for `GL_m(L)` (Khanh,
  arXiv:2609.08428, Thm 2.2), a second research-level input.
* **Not needed.**  The smallest `K₂` input on the endpoint path is already in the repo:
  `LeavittFP.BinaryLeavittSteinbergRankFourK2FinitelyNormallyGeneratedStatement` (`K₂(4, L)`
  finitely normally generated).  It closes the sentence through the refinement surjection and
  the finite presentation of `St_5(L)`.  Stable vanishing does not imply it in Lean without
  stability.

## Truth check

`LeavittK2UsedStatement` is true.  Ara–Brustenga–Cortiñas (2009) give `K_*(L) = 0`, so
stable `K₂(L) = 0`.  Also `K₂(5, L) = ⊥` (Khanh Thm 5.4), and
`leavittK2Used_of_binaryLeavittSteinbergInjective` derives the statement from that in one line.

## Not closed

No elementary Steinberg-word proof was found.  Killing a general `k ∈ K₂(5, L)` stably is the
exactness of `K₂(𝔽₂) →(1-2) K₂(𝔽₂) → K₂(L) → K₁(𝔽₂)` at `K₂(L)`.  That exactness is a
localisation-sequence fact, not word calculus.  The conclusion `K₂(5, L) = ⊥` is equivalent to
Khanh Thm 5.4 at rank five, which `LeavittFP.K2RankFourEndpoints` already records as a failed
word-calculus target.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.SimpleKazhdanSofic SymbolicDynamics.FullShift

/-- **The part of stable `K₂(L_{𝔽₂}(1,2)) = 0` that the consumers use.**  Every `k ∈ K₂(5, L)`
becomes trivial in some `St_N(L)`, `5 ≤ N`, under the relabelling along `Fin.castLE`.

*Strength.*  It is the `n = 5` instance of `BinaryLeavittStableK2TrivialStatement`
(`leavittK2Used_of_binaryLeavittStableK2Trivial`).  The converse would need the higher-rank kernels
`K₂(n, L)`, `n > 5`, to come from rank five compatibly with padding, and this is not proved.

*Why it is true.*  `K₂(5, L) = ⊥` (Khanh, arXiv:2609.08428, Thm 5.4), see
`leavittK2Used_of_binaryLeavittSteinbergInjective`.  Not proved in Lean. -/
def LeavittK2UsedStatement : Prop :=
  ∀ k ∈ GroupApproximation.BooneHigman.SteinbergBasic.K2 (Fin 5)
      (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)),
    ∃ (N : ℕ) (h : 5 ≤ N), GroupApproximation.SteinbergGroup.indexMap (Fin.castLEEmb h) k = 1

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.LeavittK2UsedStatement

/-- **Truth check (from the stable statement).**  Full stable `K₂(L) = 0` gives the used rank-five
instance. -/
theorem leavittK2Used_of_binaryLeavittStableK2Trivial
    (hS : BinaryLeavittStableK2TrivialStatement) : LeavittK2UsedStatement :=
  fun k hk => hS 5 k hk

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.leavittK2Used_of_binaryLeavittStableK2Trivial

/-- **Truth check (from the gap).**  `K₂(5, L) = ⊥` gives the used statement with `N = 5`. -/
theorem leavittK2Used_of_binaryLeavittSteinbergInjective
    (h : GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.BinaryLeavittSteinbergInjectiveStatement) :
    LeavittK2UsedStatement := by
  have h' : GroupApproximation.BooneHigman.SteinbergBasic.K2 (Fin 5)
      (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) = ⊥ := h
  intro k hk
  refine ⟨5, le_rfl, ?_⟩
  rw [(Subgroup.eq_bot_iff_forall _).mp h' k hk, map_one]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.leavittK2Used_of_binaryLeavittSteinbergInjective

/-- **Consumer 1 re-proved.**  `K₂(5, L) = ⊥` from the used statement and injective stability
from rank five. -/
theorem binaryLeavittSteinbergInjective_of_leavittK2Used
    (hU : LeavittK2UsedStatement) (hT : BinaryLeavittK2FiveStabilityStatement) :
    GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.BinaryLeavittSteinbergInjectiveStatement := by
  show GroupApproximation.BooneHigman.SteinbergBasic.K2 (Fin 5)
      (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) = ⊥
  refine (Subgroup.eq_bot_iff_forall _).mpr ?_
  intro k hk
  obtain ⟨N, h, hN⟩ := hU k hk
  exact hT k hk N h hN

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittSteinbergInjective_of_leavittK2Used

/-- **Consumer 2 re-proved.**  Superperfect `Lˣ` from the used statement and injective stability
from rank five. -/
theorem binaryLeavittUnitsSuperperfect_of_leavittK2Used
    (hU : LeavittK2UsedStatement) (hT : BinaryLeavittK2FiveStabilityStatement) :
    GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement :=
  superperfect_of_binaryLeavittSteinbergInjective
    (binaryLeavittSteinbergInjective_of_leavittK2Used hU hT)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittUnitsSuperperfect_of_leavittK2Used

/-- `EL_5(L_{𝔽₂}(1,2))` is finitely presented, from the used statement and injective stability. -/
theorem binaryLeavittElementaryFinitelyPresented_of_leavittK2Used
    (hU : LeavittK2UsedStatement) (hT : BinaryLeavittK2FiveStabilityStatement) :
    GroupApproximation.Manuscript.SimpleKazhdanSofic.FPSimpleKazhdan.BinaryLeavittElementaryFinitelyPresentedStatement :=
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.binaryLeavittElementaryFinitelyPresented_of_binaryLeavittSteinbergInjective
    (binaryLeavittSteinbergInjective_of_leavittK2Used hU hT)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittElementaryFinitelyPresented_of_leavittK2Used

/-- **tex l.730–735**, the finitely presented case, from the used statement and injective
stability from rank five. -/
theorem manuscriptSentence_finitelyPresentedCase_of_leavittK2Used
    (hU : LeavittK2UsedStatement) (hT : BinaryLeavittK2FiveStabilityStatement) :
    (∃ (E : Type) (_ : Group E), Infinite E ∧ Group.IsFinitelyPresented E ∧ IsSimpleGroup E ∧
      HasKazhdanPropertyT.{0, 0} E) ∧
    (∀ (E : Type) [Group E], Group.IsFinitelyPresented E → IsLEF E → IsResiduallyFinite E) ∧
      (∀ (E : Type) [Group E] [IsSimpleGroup E] [Infinite E], ¬ IsResiduallyFinite E) ∧
      ∀ (Λ : Type) [Group Λ] [Group.FG Λ] (Z : Type) [TopologicalSpace Z] [CompactSpace Z]
        [TopologicalSpace.MetrizableSpace Z] [TotallyDisconnectedSpace Z] [PerfectSpace Z]
        [Nonempty Z] [MulAction Λ Z] [ContinuousConstSMul Λ Z], MulAction.IsMinimal Λ Z →
        (∀ ξ : Λ, ξ ≠ 1 → ∀ U : Set Z, IsOpen U → U.Nonempty → ∃ z ∈ U, ξ • z ≠ z) →
        ∀ S : Finset (ClopenGroupCrossedProduct Λ Z (ZMod 2)), 1 ∈ S →
          Subring.closure (S : Set (ClopenGroupCrossedProduct Λ Z (ZMod 2))) = ⊤ →
        ∀ (N : ℕ → ℕ)
          (φ : ∀ k, ClopenGroupCrossedProduct Λ Z (ZMod 2) → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)),
          IsMatricialVia S N φ → ∀ n : ℕ, 3 ≤ n →
            ¬ Group.IsFinitelyPresented
              ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) :=
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.manuscriptSentence_finitelyPresentedCase_of_binaryLeavittSteinbergInjective
    (binaryLeavittSteinbergInjective_of_leavittK2Used hU hT)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.manuscriptSentence_finitelyPresentedCase_of_leavittK2Used

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
