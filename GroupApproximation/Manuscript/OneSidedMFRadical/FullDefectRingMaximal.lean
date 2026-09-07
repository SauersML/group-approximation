import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingCountable
import GroupApproximation.Analysis.ReducedGroupCStarMFAlgebra
import GroupApproximation.Analysis.ReducedGroupCStarStablyFinite

/-!
# `cor:one-sided-ring-maximal`, reduced-algebra clause

`non_mf_groups_exist.tex`, Corollary `cor:one-sided-ring-maximal`, second
sentence:

> If `R ≠ 0` also satisfies the hypothesis of Theorem `thm:full-defect-ring`,
> then `C*_r(EL_n(R))` is separable, stably finite, and not MF.

This is the general step the Introduction states for every countable group,
applied to `G = EL_n(R)`: `C*_r(G)` is separable and carries a faithful
canonical trace, hence is stably finite, and if it were MF then restricting an
MF embedding to the canonical group unitaries would make `G` MF.  No analysis
is done here; the three conjuncts are
`reducedGroupCStar_separable_stablyFinite_not_isMFAlgebra`, exactly as
`ReducedCStarConsequence` uses them at the rank-twelve binary Leavitt group.

The first sentence of the corollary — that `C*_max(EL_n(R))` contains a proper
isometry whenever `R` is not directly finite — is a statement about the
compressor rather than about the radical, and lives with the compression
calculation.

## What `R ≠ 0` is for

The printed hypothesis `R ≠ 0` is what makes `EL_n(R)` nontrivial, and
nontriviality is what turns "every homomorphism to an MF group is trivial" into
"`EL_n(R)` is not itself MF": the identity homomorphism of a countable MF group
is such a homomorphism.  `not_isCDEOperatorMF_of_killsMFTargets` is that one
line, and `nontrivial_elementaryGroup` supplies the nontriviality from a single
elementary root `x_{ij}(1) ≠ 1`, which is `elementaryUnit_injective` together
with `x_{ij}(0) = 1`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace FullDefectRing

open scoped BigOperators
open ReducedGroupCStarTrace

/-! ## Two small structural facts -/

/-- **`EL_ι(R)` is nontrivial over a nontrivial ring**, as soon as there are two
distinct indices: the elementary root `x_{ij}(1)` differs from `x_{ij}(0) = 1`
because the coefficient map is injective. -/
theorem nontrivial_elementaryGroup {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [Ring R] [Nontrivial R] {i j : ι} (hij : i ≠ j) :
    Nontrivial (elementaryGroup ι R) := by
  refine ⟨⟨⟨elementaryUnit i j hij 1, elementaryUnit_mem i j hij 1⟩, 1, ?_⟩⟩
  intro h
  have hval : elementaryUnit i j hij (1 : R) = (1 : (Matrix ι ι R)ˣ) :=
    congrArg Subtype.val h
  rw [← elementaryUnit_zero i j hij] at hval
  exact one_ne_zero (elementaryUnit_injective i j hij hval)

/-- **A nontrivial group that kills every MF target is not MF.**  The identity
homomorphism of the group is a homomorphism to an MF group as soon as the group
itself is MF, and it is not trivial. -/
theorem not_isCDEOperatorMF_of_killsMFTargets {G : Type} [Group G] [Countable G]
    [Nontrivial G]
    (h : ∀ (M : Type) [Group M], IsOperatorMF M →
      ∀ (f : G →* M) (x : G), f x = 1) :
    ¬ IsCDEOperatorMF G := by
  intro hMF
  obtain ⟨x, hx⟩ := exists_ne (1 : G)
  exact hx (h G ((isCDEOperatorMF_iff_isOperatorMF G).mp hMF) (MonoidHom.id G) x)

/-! ## The printed reduced-algebra clause -/

/-- **`cor:one-sided-ring-maximal`, second sentence, as one proposition.**  For
a nonzero countable ring `R` satisfying the hypothesis of
`thm:full-defect-ring` and every `n ≥ 4`, the reduced group C⋆-algebra of
`EL_n(R)` is separable, is stably finite, and is not MF.

"Stably finite" is the operator-algebraic reading `IsStablyFiniteCStarAlgebra`
— every isometry in every finite matrix amplification is a unitary — which is
what the Blackadar--Kirchberg literature means; see the module docstring of
`ReducedCStarConsequence` for the passage to Mathlib's `IsStablyFiniteRing`. -/
def PrintedOneSidedRingMaximalReducedCStar : Prop :=
  ∀ (R : Type) [Ring R] [Nontrivial R] [Countable R] (s t : R), t * s = 1 →
    (∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * (1 - s * t) * b k = 1) →
      ∀ (n : ℕ), 4 ≤ n →
        TopologicalSpace.SeparableSpace
            (ReducedGroupCStar (elementaryGroup (Fin n) R)) ∧
          IsStablyFiniteCStarAlgebra
            (ReducedGroupCStar (elementaryGroup (Fin n) R)) ∧
          ¬ IsMFAlgebra (ReducedGroupCStar (elementaryGroup (Fin n) R))

section Proof

variable {R : Type} [Ring R] [Nontrivial R] [Countable R]

/-- The reduced-algebra clause at one ring and one rank, from the conclusion of
`thm:full-defect-ring` at that ring and rank.  Both specializations below are
this lemma with a different source for `hkill`. -/
private theorem reducedCStarClause {n : ℕ} (hn : 4 ≤ n)
    (hkill : ∀ (M : Type) [Group M], IsOperatorMF M →
      ∀ (f : elementaryGroup (Fin n) R →* M)
        (x : elementaryGroup (Fin n) R), f x = 1) :
    TopologicalSpace.SeparableSpace
        (ReducedGroupCStar (elementaryGroup (Fin n) R)) ∧
      IsStablyFiniteCStarAlgebra
        (ReducedGroupCStar (elementaryGroup (Fin n) R)) ∧
      ¬ IsMFAlgebra (ReducedGroupCStar (elementaryGroup (Fin n) R)) := by
  have h0 : 0 < n := by omega
  have h1 : 1 < n := by omega
  have hne : (⟨0, h0⟩ : Fin n) ≠ ⟨1, h1⟩ := by
    intro hcon
    exact absurd (congrArg Fin.val hcon) (by norm_num)
  haveI : Countable (elementaryGroup (Fin n) R) := countable_elementaryGroup
  haveI : Nontrivial (elementaryGroup (Fin n) R) :=
    nontrivial_elementaryGroup (R := R) hne
  exact reducedGroupCStar_separable_stablyFinite_not_isMFAlgebra _
    (not_isCDEOperatorMF_of_killsMFTargets hkill)

end Proof

/-- **The printed reduced-algebra clause, proved.**  The failure of MF-ness for
`C*_r(EL_n(R))` is the failure of MF-ness for `EL_n(R)`, which is
`thm:full-defect-ring` at `M = EL_n(R)` itself. -/
theorem manuscriptOneSidedRingMaximalReducedCStar
    (hfixed : FullDefectAtFixedRing)
    (hEJZ : FinitelyGeneratedRingGeneralRankElementaryPropertyT) :
    PrintedOneSidedRingMaximalReducedCStar := by
  intro R _ _ _ s t hts hfull n hn
  exact reducedCStarClause hn fun M _ hM f x ↦
    manuscriptFullComplementaryIdempotents hfixed hEJZ R s t hts hfull n hn M hM
      f x

/-- **The printed reduced-algebra clause in prime characteristic**, with no
property-`(T)` hypothesis. -/
def PrintedOneSidedRingMaximalReducedCStarPrimeChar : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (R : Type) [Ring R] [Nontrivial R] [Countable R]
    [CharP R p] (s t : R), t * s = 1 →
      (∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * (1 - s * t) * b k = 1) →
        ∀ (n : ℕ), 4 ≤ n →
          TopologicalSpace.SeparableSpace
              (ReducedGroupCStar (elementaryGroup (Fin n) R)) ∧
            IsStablyFiniteCStarAlgebra
              (ReducedGroupCStar (elementaryGroup (Fin n) R)) ∧
            ¬ IsMFAlgebra (ReducedGroupCStar (elementaryGroup (Fin n) R))

theorem manuscriptOneSidedRingMaximalReducedCStarPrimeChar
    (hfixed : FullDefectAtFixedRing) :
    PrintedOneSidedRingMaximalReducedCStarPrimeChar := by
  intro p hp R _ _ _ _ s t hts hfull n hn
  exact reducedCStarClause hn fun M _ hM f x ↦
    manuscriptFullComplementaryIdempotentsPrimeChar hfixed p hp R s t hts hfull
      n hn M hM f x

end FullDefectRing
end OneSidedMFRadical
end Manuscript
end GroupApproximation
