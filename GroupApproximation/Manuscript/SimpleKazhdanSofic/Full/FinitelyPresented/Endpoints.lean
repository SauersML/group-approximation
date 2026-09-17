import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.FinitelyPresented.Basic
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleKazhdanGeneralClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralTheoremClosure
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MainFromGeneral
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MarkedLimitTransport
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FiniteModelsGroup
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FiniteModelsRing
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MainAssembly
import GroupApproximation.Meta.AxiomGuard

/-!
# The groups of `thm:general`(b) and `G_X` are not finitely presented

`simple_kazhdan_sofic_group.tex`, Section `sec:questions` (l.730–732):

> No group in Theorem `thm:general`(b) is finitely presented: a finitely presented LEF group is
> residually finite [Stepin, VershikGordon], and an infinite simple group is not.

and the rows of `tab:props` (l.210–211) for `G_X = EL_3(LC(X, F₂) ⋊_T ℤ)`:

> not residually finite & infinite and simple
>
> not finitely presented & finitely presented LEF groups are residually finite

## Contents

* `not_isFinitelyPresented_general`: the groups `EL_n(R)`, `n ≥ 3`, of `thm:general`(b) are not
  residually finite and not finitely presented. `thm:general` (`printedSimpleKazhdanGeneral`) makes
  them infinite, simple and marked limits of finite groups, and `Full/FinitelyPresented/Basic` finishes.
  The hypothesis of (b) is `IsMatricialVia S N φ`, the corpus reading of the printed hypothesis. It also
  asks `N_k ≥ 1`, which the printed text leaves implicit (the targets are the finite simple groups
  `SL_{nN_k}(F₂)`).
* `isMatricialLEFRing_R`, `isSimpleGroup_elementaryGroup_R`: `LC(X, F₂) ⋊_T ℤ` has matricial finite
  models ("Finite models"), and `EL_n` of it is simple for `n ≥ 3` (`thm:general`(a), through the ring
  isomorphism `ringEquiv S` with the crossed product of the action by powers of `T`).
* `elementaryGroup_R_not_isResiduallyFinite_not_isFinitelyPresented` and the closed
  `printedGXNotResiduallyFiniteNotFinitelyPresented`: for every infinite minimal subshift `X` and every
  `n ≥ 3`, `EL_n(LC(X, F₂) ⋊_T ℤ)` is neither residually finite nor finitely presented. The case
  `n = 3` is `G_X`, closed as `printedGXNotFinitelyPresentedClosed : PrintedGXNotFinitelyPresented`.

Every import is already imported from the library root.
-/

namespace GroupApproximation.Full.SK14

open GroupApproximation.SimpleKazhdanSofic SymbolicDynamics.FullShift

/-! ## `thm:general`(b) -/

/-- **No group in `thm:general`(b) is finitely presented** (tex l.730–732). For `EL_n(R)`, `n ≥ 3`, with
`R = LC(Z, F₂) ⋊ Λ` as in `thm:general` and matricial via `φ_k`, `EL_n(R)` is not residually finite
and not finitely presented. -/
theorem not_isFinitelyPresented_general (Λ : Type) [Group Λ] [Group.FG Λ] (Z : Type)
    [TopologicalSpace Z] [CompactSpace Z] [TopologicalSpace.MetrizableSpace Z]
    [TotallyDisconnectedSpace Z] [PerfectSpace Z] [Nonempty Z] [MulAction Λ Z]
    [ContinuousConstSMul Λ Z] (hmin : MulAction.IsMinimal Λ Z)
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → ∀ U : Set Z, IsOpen U → U.Nonempty → ∃ z ∈ U, ξ • z ≠ z)
    (S : Finset (ClopenGroupCrossedProduct Λ Z (ZMod 2))) (h1 : 1 ∈ S)
    (hS : Subring.closure (S : Set (ClopenGroupCrossedProduct Λ Z (ZMod 2))) = ⊤) (N : ℕ → ℕ)
    (φ : ∀ k, ClopenGroupCrossedProduct Λ Z (ZMod 2) → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))
    (hφ : IsMatricialVia S N φ) (n : ℕ) (hn : 3 ≤ n) :
    ¬ IsResiduallyFinite ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) ∧
      ¬ Group.IsFinitelyPresented
        ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) := by
  obtain ⟨hinf, -, hsimple, -, hlim, -, -, hexp⟩ :=
    printedSimpleKazhdanGeneral Λ Z hmin hfree S h1 hS N φ hφ n hn
  obtain ⟨-, hfin, -⟩ := hexp
  haveI := hinf
  haveI := hsimple
  exact ⟨not_isResiduallyFinite_of_isSimpleGroup_of_infinite _,
    not_isFinitelyPresented_of_isMarkedLimit hfin hlim⟩

/-! ## `G_X` -/

section Subshift

variable {A : Type} [TopologicalSpace A] [DiscreteTopology A] [Finite A]

/-- **`LC(X, F₂) ⋊_T ℤ` has matricial finite models** (section "Finite models"), for every infinite
minimal subshift. -/
theorem isMatricialLEFRing_R (S : Subshift A ℤ) (hinf : Infinite S.carrier) (hmin : IsMinimal S) :
    IsMatricialLEFRing (ZMod 2) (R S) := fun t =>
  exists_matrixModel_clopenCrossedProduct S.isClosed S.mapsTo
    (Set.infinite_coe_iff.mp hinf).nonempty hmin (subshiftHomeo S) (fun _ => rfl) (ZMod 2) t

/-- **`EL_n(LC(X, F₂) ⋊_T ℤ)` is simple** for `n ≥ 3` (`thm:general`(a) at the action of `ℤ` by powers
of the shift). -/
theorem isSimpleGroup_elementaryGroup_R (S : Subshift A ℤ) (hinf : Infinite S.carrier)
    (hmin : IsMinimal S) {n : ℕ} (hn : 3 ≤ n) : IsSimpleGroup ↥(elementaryGroup (Fin n) (R S)) := by
  classical
  haveI := compactSpace_carrier S
  haveI : Nonempty S.carrier := (Set.infinite_coe_iff.mp hinf).nonempty.to_subtype
  haveI := perfectSpace_carrier S hinf hmin
  haveI : Group.FG (Multiplicative ℤ) := fg_multiplicative_int
  have hsimple' := printedGeneralSimplicityStatement (Multiplicative ℤ) S.carrier
    (isMinimal_shift S hmin) (isTopologicallyFree_shift S hinf hmin) n hn
  set eG := (elementaryGroupEquivOfRingEquiv n (ringEquiv S)).symm with heG
  haveI := hsimple'
  haveI : Nontrivial ↥(elementaryGroup (Fin n) (R S)) := eG.injective.nontrivial
  exact IsSimpleGroup.isSimpleGroup_of_surjective eG.toMonoidHom eG.surjective

/-- **`EL_n(LC(X, F₂) ⋊_T ℤ)` is neither residually finite nor finitely presented**, for every infinite
minimal subshift and every `n ≥ 3` (`tab:props`, tex l.210–211, and tex l.730–732). -/
theorem elementaryGroup_R_not_isResiduallyFinite_not_isFinitelyPresented (S : Subshift A ℤ)
    (hinf : Infinite S.carrier) (hmin : IsMinimal S) {n : ℕ} (hn : 3 ≤ n) :
    ¬ IsResiduallyFinite ↥(elementaryGroup (Fin n) (R S)) ∧
      ¬ Group.IsFinitelyPresented ↥(elementaryGroup (Fin n) (R S)) := by
  haveI : Infinite ↥(elementaryGroup (Fin n) (R S)) := infinite_elementaryGroup S hinf hn
  haveI : IsSimpleGroup ↥(elementaryGroup (Fin n) (R S)) :=
    isSimpleGroup_elementaryGroup_R S hinf hmin hn
  exact ⟨not_isResiduallyFinite_of_isSimpleGroup_of_infinite _,
    not_isFinitelyPresented_of_isLEF_of_isSimpleGroup_of_infinite
      ((isMatricialLEFRing_R S hinf hmin).isLEF_elementaryGroup n)⟩

end Subshift

/-- **The rows "not residually finite" and "not finitely presented" of `tab:props`** (tex l.210–211),
as a closed proposition, for `EL_n(LC(X, F₂) ⋊_T ℤ)` and every `n ≥ 3`. -/
def PrintedGXNotResiduallyFiniteNotFinitelyPresented : Prop :=
  ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Finite A] (S : Subshift A ℤ),
    Infinite S.carrier → IsMinimal S → ∀ n : ℕ, 3 ≤ n →
      ¬ IsResiduallyFinite ↥(elementaryGroup (Fin n) (R S)) ∧
        ¬ Group.IsFinitelyPresented ↥(elementaryGroup (Fin n) (R S))

theorem printedGXNotResiduallyFiniteNotFinitelyPresented :
    PrintedGXNotResiduallyFiniteNotFinitelyPresented := by
  intro A _ _ _ S hinf hmin n hn
  exact elementaryGroup_R_not_isResiduallyFinite_not_isFinitelyPresented S hinf hmin hn

/-- **`G_X` is not finitely presented**, closing the corpus statement `PrintedGXNotFinitelyPresented`
(`SimpleKazhdanSofic.QuestionsNotFinitelyPresented`) without hypotheses. -/
theorem printedGXNotFinitelyPresentedClosed : PrintedGXNotFinitelyPresented := by
  intro A _ _ _ S hinf hmin
  exact (elementaryGroup_R_not_isResiduallyFinite_not_isFinitelyPresented S hinf hmin
    (le_refl 3)).2

/-- **No group in `thm:general`(b) is finitely presented** (tex l.730–732), as a closed proposition. -/
def PrintedGeneralNotFinitelyPresented : Prop :=
  ∀ (Λ : Type) [Group Λ] [Group.FG Λ] (Z : Type) [TopologicalSpace Z] [CompactSpace Z]
    [TopologicalSpace.MetrizableSpace Z] [TotallyDisconnectedSpace Z] [PerfectSpace Z] [Nonempty Z]
    [MulAction Λ Z] [ContinuousConstSMul Λ Z], MulAction.IsMinimal Λ Z →
    (∀ ξ : Λ, ξ ≠ 1 → ∀ U : Set Z, IsOpen U → U.Nonempty → ∃ z ∈ U, ξ • z ≠ z) →
    ∀ S : Finset (ClopenGroupCrossedProduct Λ Z (ZMod 2)), 1 ∈ S →
      Subring.closure (S : Set (ClopenGroupCrossedProduct Λ Z (ZMod 2))) = ⊤ →
    ∀ (N : ℕ → ℕ)
      (φ : ∀ k, ClopenGroupCrossedProduct Λ Z (ZMod 2) → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)),
      IsMatricialVia S N φ → ∀ n : ℕ, 3 ≤ n →
        ¬ Group.IsFinitelyPresented ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2)))

theorem printedGeneralNotFinitelyPresented : PrintedGeneralNotFinitelyPresented := by
  intro Λ _ _ Z _ _ _ _ _ _ _ _ hmin hfree S h1 hS N φ hφ n hn
  exact (not_isFinitelyPresented_general Λ Z hmin hfree S h1 hS N φ hφ n hn).2

end GroupApproximation.Full.SK14

#audit_axioms GroupApproximation.Full.SK14.not_isFinitelyPresented_general
#audit_axioms GroupApproximation.Full.SK14.isMatricialLEFRing_R
#audit_axioms GroupApproximation.Full.SK14.isSimpleGroup_elementaryGroup_R
#audit_axioms GroupApproximation.Full.SK14.elementaryGroup_R_not_isResiduallyFinite_not_isFinitelyPresented
#audit_closed_axioms GroupApproximation.Full.SK14.printedGXNotResiduallyFiniteNotFinitelyPresented
#audit_closed_axioms GroupApproximation.Full.SK14.printedGXNotFinitelyPresentedClosed
#audit_closed_axioms GroupApproximation.Full.SK14.printedGeneralNotFinitelyPresented
