import GroupApproximation.Sofic.LiteralSignFreeQuotient
import GroupApproximation.Sofic.ManuscriptExactWrappers

/-!
# The two radical reductions, applied to the literal `E/⟨w⟩`

The manuscript's first open question (`\subsection*{Questions}`, item 1) does
not merely cite the two reduction corollaries; it *applies* them to a named
group with a named witness:

> Corollary `\ref{cor:collapsequot}`, applied to `E/⟨w⟩` with the witness of
> that proof, reduces the computation to the quotient by the resulting
> collapse defect `D`, and Corollary `\ref{cor:exactradical}` then identifies
> the radical with the preimage of `D` as soon as that quotient is MF.

`Sofic/ManuscriptExactWrappers` carries both corollaries in their general
form, and `Sofic/LiteralSignFreeQuotient` carries the literal quotient
`E/⟨w⟩` together with the witness of Theorem B's proof — the image `Lbar` of
the base, its property `(T)`, its compression by the stable letter, and the
involutive witness `witness_dee`.  What was missing is the application: the
instantiation of the general theorems at that group and that witness, so that
the printed sentence has a declaration that says it.

Three things are stated here, in the order the manuscript states them.

1. **The collapse reduction, unconditionally.**  `Rad_MF(E/⟨w⟩)` is the full
   preimage of `Rad_MF((E/⟨w⟩)/D)`, where `D` is the involutive collapse
   defect of the witness of Theorem B's proof.
2. **The transfer up to `E`.**  `Rad_MF(E)` is the preimage of
   `Rad_MF(E/⟨w⟩)`, because `⟨w⟩` lies in `Rad_MF(E)` (Theorem A) and the
   radical of a group is the preimage of the radical of any quotient by a
   subgroup of it.  Composing with 1, the computation of `Rad_MF(E)` is
   reduced to `(E/⟨w⟩)/D` exactly as printed.
3. **The exact form.**  As soon as `(E/⟨w⟩)/D` is MF, both radicals are
   pinned: `Rad_MF(E/⟨w⟩) = D` and `Rad_MF(E)` is the preimage of `D`.

Whether `(E/⟨w⟩)/D` is MF is the open question; nothing here decides it, and
the conditional clause is printed as a conditional.  The defect `D` is
recorded as nontrivial (`collapsedCommutator_mem_defect` together with
`LiteralSignFreeQuotient.collapsed_commutator_ne_one`), so the reduction is
not the vacuous one through the trivial defect.
-/

namespace GroupApproximation
namespace LiteralSignFreeRadicalReduction

open LiteralNonMFPresentation LiteralNonMFEndpoint LiteralSignFreeQuotient
open scoped commutatorElement

noncomputable section

/-! ## The collapse defect of the printed witness -/

/-- The collapse defect `D` of the manuscript's sentence: the involutive
compression-collapse defect of the image of the base in `E/⟨w⟩`, compressed by
the image of the stable letter.  This is the defect produced by the witness of
the proof of Theorem B, which is `LiteralSignFreeQuotient.witness_dee`. -/
abbrev signFreeCollapseDefect : Subgroup SignFreeQuotient :=
  CollapseUniverseScope.involutiveCollapseDefect Lbar (proj stable)

instance signFreeCollapseQuotient_countable :
    Countable (SignFreeQuotient ⧸ signFreeCollapseDefect) :=
  Function.Surjective.countable
    (QuotientGroup.mk'_surjective signFreeCollapseDefect)

/-- The involutive witness of Theorem B's proof, read in the
universe-polymorphic vocabulary the exact wrapper is stated in.  The two
predicates are `Iff.rfl` at `Type 0`. -/
theorem witness_dee_universeScope :
    CollapseUniverseScope.IsInvolutiveCompressionWitness Lbar (proj stable)
      (proj dee) :=
  (CollapseUniverseScope.isInvolutiveCompressionWitness_iff Lbar (proj stable)
    (proj dee)).mpr witness_dee

/-- The collapsed commutator of Theorem B lies in the defect: it is the
commutator of an element of `Lbar` with the involutive witness, which is one
of the generators of the defect's normal closure. -/
theorem collapsedCommutator_mem_defect :
    ⁅proj (baseMap (LiteralBaseRelations.v1 : Base)), proj dee⁆ ∈
      signFreeCollapseDefect :=
  CollapseUniverseScope.commutator_mem_involutiveCollapseDefect
    witness_dee_universeScope proj_baseMap_v1_mem

/-- **The defect is not the trivial subgroup**, so the reduction below is not
the vacuous reduction through the trivial quotient. -/
theorem signFreeCollapseDefect_ne_bot : signFreeCollapseDefect ≠ ⊥ := by
  intro hbot
  have hmem := collapsedCommutator_mem_defect
  rw [hbot, Subgroup.mem_bot] at hmem
  exact collapsed_commutator_ne_one hmem

/-! ## The sign lies in the radical of `E` -/

/-- Theorem A in radical form for the literal group: the marked sign lies in
the MF radical of `E`.  This is the hypothesis Corollary `cor:exactradical`
consumes, and it is what makes the passage to `E/⟨w⟩` lossless. -/
theorem mark_mem_actualCoronaMFResidual :
    mark ∈ actualCoronaMFResidual MarkedGroup := by
  rw [← manuscriptCoronaMFResidual_eq_actualCoronaMFResidual]
  exact literal_mark_mem_manuscriptCoronaMFResidual

theorem markSubgroup_le_actualCoronaMFResidual :
    markSubgroup ≤ actualCoronaMFResidual MarkedGroup :=
  Subgroup.zpowers_le.mpr mark_mem_actualCoronaMFResidual

/-- **The radical of `E` is the preimage of the radical of `E/⟨w⟩`.**  This is
the first half of Corollary `cor:exactradical`, at `N = ⟨w⟩`: killing a normal
subgroup of the radical loses nothing, because every homomorphism to `𝒰(𝒬)`
factors through the quotient. -/
theorem actualCoronaMFResidual_markedGroup_eq_comap :
    actualCoronaMFResidual MarkedGroup =
      (actualCoronaMFResidual SignFreeQuotient).comap proj :=
  TorsionCompressionCollapse.actualCoronaMFResidual_eq_comap_quotient
    markSubgroup markSubgroup_le_actualCoronaMFResidual

/-! ## The printed application -/

/-- **The manuscript's first question, in the form it is printed.**  Both
reductions, applied to the literal `E/⟨w⟩` with the witness of the proof of
Theorem B:

* the collapse reduction sends `Rad_MF(E/⟨w⟩)` to the full preimage of
  `Rad_MF((E/⟨w⟩)/D)`;
* the same computation for `Rad_MF(E)` follows, `⟨w⟩` being inside
  `Rad_MF(E)`;
* and if `(E/⟨w⟩)/D` is MF, then `Rad_MF(E/⟨w⟩) = D` and `Rad_MF(E)` is the
  preimage of `D` — which is the sentence "identifies the radical with the
  preimage of `D` as soon as that quotient is MF".

The MF-ness of `(E/⟨w⟩)/D` is not proved here and is not proved anywhere: it
is the open question the manuscript asks. -/
theorem manuscriptSignFreeRadicalReduction :
    actualCoronaMFResidual SignFreeQuotient =
        (actualCoronaMFResidual
          (SignFreeQuotient ⧸ signFreeCollapseDefect)).comap
          (QuotientGroup.mk' signFreeCollapseDefect) ∧
      actualCoronaMFResidual MarkedGroup =
        ((actualCoronaMFResidual
          (SignFreeQuotient ⧸ signFreeCollapseDefect)).comap
          (QuotientGroup.mk' signFreeCollapseDefect)).comap proj ∧
      (IsCDEOperatorMF (SignFreeQuotient ⧸ signFreeCollapseDefect) →
        actualCoronaMFResidual SignFreeQuotient = signFreeCollapseDefect ∧
          actualCoronaMFResidual MarkedGroup =
            signFreeCollapseDefect.comap proj) := by
  obtain ⟨hcomap, hexact⟩ :=
    ManuscriptExactWrappers.manuscriptCollapseRadicalReduction
      Lbar (proj stable) Lbar_hasKazhdanPropertyT Lbar_compressed
  refine ⟨hcomap, ?_, ?_⟩
  · rw [actualCoronaMFResidual_markedGroup_eq_comap, hcomap]
  · intro hMF
    have hquot := hexact hMF
    exact ⟨hquot, by rw [actualCoronaMFResidual_markedGroup_eq_comap, hquot]⟩

end

end LiteralSignFreeRadicalReduction
end GroupApproximation
