import GroupApproximation.Leavitt.ElementaryNormalGeneration
import GroupApproximation.Leavitt.ElementaryTransvectionExtraction
import GroupApproximation.Leavitt.ElementaryWeylMonomial
import GroupApproximation.Leavitt.RowAnnihilatorTransvection
import GroupApproximation.Meta.AxiomGuard

/-!
# The printed Weyl-matrix route through elementary normal generation

The manuscript does not propagate a unit root by the source/target quotient
argument used elsewhere in the library.  It conjugates by products of the
generalized permutation matrices

`w_uv = e_uv(1) e_vu(-1) e_uv(1)`.

This file composes the entrywise Weyl calculation with the two sandwich
commutators and the final generator argument, retaining the exact printed
route.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open scoped commutatorElement

universe u v

/-- The generalized-permutation sentence, including normality and the
inverse-sign alternative. -/
def PrintedGeneralizedPermutationPropagation : Prop :=
  ∀ (ι : Type u) (S : Type v) [Fintype ι] [DecidableEq ι] [Ring S]
    (N : Subgroup (elementaryGroup ι S)) [N.Normal]
    (j k : ι) (hjk : j ≠ k),
    elGen j k hjk (1 : S) ∈ N →
      ∀ (u v : ι) (huv : u ≠ v), elGen u v huv (1 : S) ∈ N

/-- Products of the printed Weyl words carry one unit root to every ordered
unit-root position; taking inverses absorbs the possible minus sign. -/
theorem manuscriptGeneralizedPermutationPropagation :
    PrintedGeneralizedPermutationPropagation := by
  intro ι S _ _ _ N _ j k hjk hmem u v huv
  exact ElementaryWeyl.elGen_one_mem_of_ne N hjk hmem huv

/-- The full printed proof of normal generation by a sandwiched elementary
transvection. -/
def PrintedNormalGenerationByElementaryTransvectionViaWeyl : Prop :=
  ∀ (ι : Type u) (S : Type v) [Fintype ι] [DecidableEq ι] [Ring S],
    3 ≤ Fintype.card ι →
      ∀ (N : Subgroup (elementaryGroup ι S)) [N.Normal]
        (i j : ι) (hij : i ≠ j) (a x b : S),
        elGen i j hij x ∈ N → a * x * b = 1 → N = ⊤

/-- The proof follows the manuscript line by line: choose a third index, use
two Steinberg commutators to obtain a unit root, move that root by Weyl words,
use one final commutator to obtain every coefficient root, and invoke
generation by elementary roots. -/
theorem manuscriptNormalGenerationByElementaryTransvectionViaWeyl :
    PrintedNormalGenerationByElementaryTransvectionViaWeyl := by
  intro ι S _ _ _ hcard N _ i j hij a x b hx hsandwich
  obtain ⟨k, hki, hkj⟩ := exists_third_index hcard i j
  have hik : i ≠ k := hki.symm
  have hjk : j ≠ k := hkj.symm
  have hxb : elGen i k hik (x * b) ∈ N := by
    have hcomm := commutator_mem_left N hx (elGen j k hjk b)
    rwa [commutatorElement_def,
      elGen_commutator i j k hij hjk hik x b] at hcomm
  have hone : elGen j k hjk (1 : S) ∈ N := by
    have hcomm := RowAnnihilator.commutator_mem_right N
      (elGen j i hij.symm a) hxb
    rw [commutatorElement_def,
      elGen_commutator j i k hij.symm hik hjk a (x * b)] at hcomm
    simpa only [← mul_assoc, hsandwich] using hcomm
  have hunit : ∀ (u v : ι) (huv : u ≠ v),
      elGen u v huv (1 : S) ∈ N := by
    intro u v huv
    exact manuscriptGeneralizedPermutationPropagation
      ι S N j k hjk hone u v huv
  have hroot : ∀ (u v : ι) (huv : u ≠ v) (r : S),
      elGen u v huv r ∈ N := by
    intro u v huv r
    obtain ⟨h, hhu, hhv⟩ := exists_third_index hcard u v
    have huh : u ≠ h := hhu.symm
    have hhv' : h ≠ v := hhv
    have hcomm := RowAnnihilator.commutator_mem_right N
      (elGen u h huh r) (hunit h v hhv')
    rwa [commutatorElement_def,
      elGen_commutator u h v huh hhv' huv r 1, mul_one] at hcomm
  have hquot : ∀ g : elementaryGroup ι S, QuotientGroup.mk' N g = 1 :=
    elementaryGroup_hom_eq_one_of_gens (QuotientGroup.mk' N)
      (fun u v huv r ↦ (QuotientGroup.eq_one_iff _).mpr
        (hroot u v huv r))
  rw [Subgroup.eq_top_iff']
  intro g
  exact (QuotientGroup.eq_one_iff g).mp (hquot g)

#audit_closed_axioms manuscriptGeneralizedPermutationPropagation
#audit_closed_axioms manuscriptNormalGenerationByElementaryTransvectionViaWeyl

end OneSidedMFRadical
end Manuscript
end GroupApproximation
