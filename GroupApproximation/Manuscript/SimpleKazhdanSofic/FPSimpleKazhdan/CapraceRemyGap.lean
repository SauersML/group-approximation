import GroupApproximation.Endpoint.MainResults
import GroupApproximation.Leavitt.RootDetectionBinary
import GroupApproximation.Manuscript.SimpleKazhdanSofic.AbstractIntro.Questions
import GroupApproximation.Meta.AxiomGuard

/-!
# `simple_kazhdan_sofic_group.tex`, the finitely presented case (tex l.733–737)

Census text (tex l.733–737; the current tex, l.730–734, has the same clauses in the other order):

> Infinite finitely presented simple Kazhdan groups exist~\cite{CapraceRemy}, while no group in
> Theorem~\ref{thm:general}\textup{(b)} is finitely presented: a finitely presented LEF group is
> residually finite~\cite{Stepin,VershikGordon}, and an infinite simple group is not.

The three clauses after "while" are already proved, unconditionally, in
`AbstractIntro.manuscriptSentence_generalLimitsNotFinitelyPresented`.  This module handles the
first clause: there is an infinite, finitely presented, simple group with property (T).

## The mathematics

**The cited proof.**  Caprace and Rémy (*Simplicity and superrigidity of twin building lattices*,
Invent. Math. 176 (2009)) take a 2-spherical, indecomposable generalized Cartan matrix `A` of size
`n`, neither spherical nor affine, and `q > 1764^n`.  The Kac–Moody group `G_A(𝔽_q)` modulo its
centre is then finitely presented, simple and Kazhdan.  It is a lattice in the product of its twin
buildings.  The library has no Kac–Moody groups and no twin buildings, so this route cannot be
followed here.

**Routes that do not help.**
* The groups of Theorem `thm:general`(b) are LEF, so by the second clause they are not finitely
  presented.
* A simple quotient of a finitely presented Kazhdan group is Kazhdan, but it is finitely presented
  only when the kernel is finitely normally generated.  Infinite simple quotients of finitely
  presented groups need not be finitely presented, so no quotient construction in the library
  supplies the missing presentation.
* Thompson's group `V` and the Higman–Thompson groups are finitely presented and simple, but they
  are not Kazhdan.  A Boone–Higman style embedding of a Kazhdan group into a finitely presented
  simple group gives no property (T) for the ambient group.

**The route taken: `EL_5` over the binary Leavitt algebra.**  Let `L = L_{𝔽₂}(1,2)`
(`BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)`) and `Γ = EL_5(L)` (`BinaryLeavittEL (ZMod 2) 4`).
The library proves, with no inputs:
* `Γ` is finitely generated, infinite and Kazhdan (`binaryLeavitt_finiteField_profile`, rank
  `4 + 1`);
* `Γ` is simple (`RootDetectionBinary.isSimpleGroup_elementaryGroup_binaryLeavitt`, since
  `3 ≤ 5`).

This is `manuscriptSentence_binaryLeavittElementaryInfiniteSimpleKazhdan`.  The only missing
property is finite presentability of `Γ`.  It follows from the literature:
* Khanh (arXiv:2609.08428), Lemma 5.3: `GL_m(L) = E_m(L)` for `m ≥ 2`.
* Khanh, Theorem 5.4: the Steinberg map `St_r(L) → GL_r(L)` is an isomorphism for `r ≥ 3`, so
  `St_5(L) ≅ EL_5(L)`.
* Khanh, Theorem 6.1: `L^×` is finitely presented.  It is derived from Theorem 5.4 and the
  Krstić–McCool finite presentability theorem for Steinberg groups (the library records
  `Ring.IsFinitelyPresentedNC L` in `Leavitt/FinitePresentation`).  The prefix-code isomorphism
  `M_5(L) ≅ L` gives `EL_5(L) = GL_5(L) ≅ L^×`.

None of these results is in the library.  In the library's terms,
`BooneHigman.SteinbergBasic.isFinitelyPresented_elementaryGroup_of_K2_eq_bot` reduces the gap to
finite presentability of `St_5(L)` and `K₂ = ⊥`.  The gap is isolated as the single proposition
`BinaryLeavittElementaryFinitelyPresentedStatement`: `EL_5(L)` is finitely presented.

## Declarations

* `manuscriptSentence_binaryLeavittElementaryInfiniteSimpleKazhdan` (closed): `EL_5(L)` is
  finitely generated, infinite, simple and Kazhdan.
* `BinaryLeavittElementaryFinitelyPresentedStatement` (the gap).
* `manuscriptSentence_infiniteFinitelyPresentedSimpleKazhdanGroupsExist_of_binaryLeavittElementaryFinitelyPresented`:
  the first clause, from the gap.
* `manuscriptSentence_finitelyPresentedCase_of_binaryLeavittElementaryFinitelyPresented`: the
  whole sentence, from the gap.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FPSimpleKazhdan

open GroupApproximation.SimpleKazhdanSofic SymbolicDynamics.FullShift

/-- **Closed part of tex l.733–734.**  `EL_5(L_{𝔽₂}(1,2))` is finitely generated, infinite, simple
and Kazhdan. -/
theorem manuscriptSentence_binaryLeavittElementaryInfiniteSimpleKazhdan :
    Group.FG ↥(BinaryLeavittEL (ZMod 2) 4) ∧ Infinite ↥(BinaryLeavittEL (ZMod 2) 4) ∧
      IsSimpleGroup ↥(BinaryLeavittEL (ZMod 2) 4) ∧
      HasKazhdanPropertyT.{0, 0} ↥(BinaryLeavittEL (ZMod 2) 4) := by
  obtain ⟨hfg, hinf, hT, -⟩ := binaryLeavitt_finiteField_profile (ZMod 2) 4 (by norm_num)
  have hsimple : IsSimpleGroup ↥(BinaryLeavittEL (ZMod 2) 4) :=
    RootDetectionBinary.isSimpleGroup_elementaryGroup_binaryLeavitt (ι := Fin (4 + 1)) (by simp)
  exact ⟨hfg, hinf, hsimple, hT⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FPSimpleKazhdan.manuscriptSentence_binaryLeavittElementaryInfiniteSimpleKazhdan

/-- **The gap.**  The elementary group `EL_5(L_{𝔽₂}(1,2))` is finitely presented.  True by Khanh
(arXiv:2609.08428, Lemma 5.3 and Theorem 5.4) and the Krstić–McCool theorem; not proved here. -/
def BinaryLeavittElementaryFinitelyPresentedStatement : Prop :=
  Group.IsFinitelyPresented ↥(BinaryLeavittEL (ZMod 2) 4)

/-- **tex l.733–734**, first clause, from the gap: there is an infinite, finitely presented,
simple group with property (T), namely `EL_5(L_{𝔽₂}(1,2))`. -/
theorem manuscriptSentence_infiniteFinitelyPresentedSimpleKazhdanGroupsExist_of_binaryLeavittElementaryFinitelyPresented
    (hfp : BinaryLeavittElementaryFinitelyPresentedStatement) :
    ∃ (E : Type) (_ : Group E), Infinite E ∧ Group.IsFinitelyPresented E ∧ IsSimpleGroup E ∧
      HasKazhdanPropertyT.{0, 0} E := by
  obtain ⟨-, hinf, hsimple, hT⟩ := manuscriptSentence_binaryLeavittElementaryInfiniteSimpleKazhdan
  exact ⟨↥(BinaryLeavittEL (ZMod 2) 4), inferInstance, hinf, hfp, hsimple, hT⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FPSimpleKazhdan.manuscriptSentence_infiniteFinitelyPresentedSimpleKazhdanGroupsExist_of_binaryLeavittElementaryFinitelyPresented

/-- **tex l.733–737**, the whole sentence, from the gap: infinite finitely presented simple Kazhdan
groups exist; a finitely presented LEF group is residually finite; an infinite simple group is not;
and no group `EL_n(R)`, `n ≥ 3`, of Theorem `thm:general`(b) is finitely presented. -/
theorem manuscriptSentence_finitelyPresentedCase_of_binaryLeavittElementaryFinitelyPresented
    (hfp : BinaryLeavittElementaryFinitelyPresentedStatement) :
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
  ⟨manuscriptSentence_infiniteFinitelyPresentedSimpleKazhdanGroupsExist_of_binaryLeavittElementaryFinitelyPresented
      hfp,
    GroupApproximation.Manuscript.SimpleKazhdanSofic.AbstractIntro.manuscriptSentence_generalLimitsNotFinitelyPresented⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FPSimpleKazhdan.manuscriptSentence_finitelyPresentedCase_of_binaryLeavittElementaryFinitelyPresented

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FPSimpleKazhdan
