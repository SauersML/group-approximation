import GroupApproximation.Sofic.LiteralSignFreeQuotient
import GroupApproximation.Sofic.ManuscriptExactWrappers

/-!
# The two radical reductions, applied to the literal `E/⟨w⟩`

The manuscript's first open question (`\subsection*{Questions}`, item 1) does
not merely cite the two reduction corollaries; it *applies* them to a named
group with a named witness:

> Write `q₁ : E → E/⟨w⟩`, let `D = D_coll(L̄, q₁(t))` for the witness `c̄` of
> that proof, and let `q₂ : E/⟨w⟩ → (E/⟨w⟩)/D`.  By
> Corollary `\ref{cor:collapsequot}` applied to `E/⟨w⟩` and then
> Corollary `\ref{cor:pullback}`,
> `Res_MF(E) = q₁⁻¹ q₂⁻¹ (Res_MF((E/⟨w⟩)/D))`,
> so by Corollary `\ref{cor:exactradical}` the residual equals `q₁⁻¹(D)`
> **exactly when** `(E/⟨w⟩)/D` is MF.

`Sofic/ManuscriptExactWrappers` carries both corollaries in their general
form, and `Sofic/LiteralSignFreeQuotient` carries the literal quotient
`E/⟨w⟩` together with the witness of Theorem B's proof — the image `Lbar` of
the base, its property `(T)`, its compression by the stable letter, and the
involutive witness `witness_dee`.  What was missing is the application: the
instantiation of the general theorems at that group and that witness, so that
the printed sentence has a declaration that says it.

Three things are stated here, matching the three the manuscript states.

1. **The collapse reduction at `E/⟨w⟩`, unconditionally.**  `Res_MF(E/⟨w⟩)` is
   the full preimage under `q₂` of `Res_MF((E/⟨w⟩)/D)`, where `D` is the
   involutive collapse defect of the witness of Theorem B's proof.  This is
   Corollary `cor:collapsequot` at that group.
2. **The displayed identity.**  `Res_MF(E) = q₁⁻¹ q₂⁻¹ (Res_MF((E/⟨w⟩)/D))`,
   obtained by composing 1 with Corollary `cor:pullback` at `N = ⟨w⟩`, which
   applies because `⟨w⟩ ≤ Res_MF(E)` by Theorem A.
3. **The exactness clause, as an iff.**  the residual `Res_MF(E)` equals
   `q₁⁻¹(D)` *exactly when*
   `(E/⟨w⟩)/D` is MF.  The manuscript prints "exactly when", so both
   directions are proved: forwards from Corollary `cor:exactradical`, and
   backwards because `q₁` and `q₂` are surjective — equal preimages force
   equal subgroups, so `Res_MF((E/⟨w⟩)/D)` collapses to the trivial subgroup,
   which is the MF property.

Whether `(E/⟨w⟩)/D` is MF is the open question; nothing here decides it.  The
defect `D` is recorded as nontrivial (`collapsedCommutator_mem_defect` with
`LiteralSignFreeQuotient.collapsed_commutator_ne_one`), so the reduction is
not the vacuous one through the trivial defect.

The manuscript writes `Res_MF` and says "residual" where earlier drafts wrote
`Res_MF` and "radical"; the Lean name `actualCoronaMFResidual` already matched
the new wording and is unaffected.
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

* the collapse reduction sends `Res_MF(E/⟨w⟩)` to the full preimage under `q₂`
  of `Res_MF((E/⟨w⟩)/D)`;
* hence the displayed identity
  `Res_MF(E) = q₁⁻¹ q₂⁻¹ (Res_MF((E/⟨w⟩)/D))`, `⟨w⟩` being inside
  `Res_MF(E)`;
* and the residual `Res_MF(E)` equals `q₁⁻¹(D)` **exactly when**
  `(E/⟨w⟩)/D` is MF.

The third clause is an `Iff` because the manuscript prints "exactly when".
The forward direction is Corollary `cor:exactradical`; the reverse holds
because `q₁` and `q₂` are surjective, so equal preimages force equal
subgroups, and `Res_MF((E/⟨w⟩)/D) = ⊥` is the MF property.

Whether `(E/⟨w⟩)/D` is MF is not decided here and is not decided anywhere: it
is the open question the manuscript asks, and the `Iff` says precisely that
computing `Res_MF(E)` is the same question. -/
theorem manuscriptSignFreeRadicalReduction :
    actualCoronaMFResidual SignFreeQuotient =
        (actualCoronaMFResidual
          (SignFreeQuotient ⧸ signFreeCollapseDefect)).comap
          (QuotientGroup.mk' signFreeCollapseDefect) ∧
      actualCoronaMFResidual MarkedGroup =
        ((actualCoronaMFResidual
          (SignFreeQuotient ⧸ signFreeCollapseDefect)).comap
          (QuotientGroup.mk' signFreeCollapseDefect)).comap proj ∧
      (actualCoronaMFResidual MarkedGroup = signFreeCollapseDefect.comap proj ↔
        IsCDEOperatorMF (SignFreeQuotient ⧸ signFreeCollapseDefect)) := by
  obtain ⟨hcomap, hexact⟩ :=
    ManuscriptExactWrappers.manuscriptCollapseRadicalReduction
      Lbar (proj stable) Lbar_hasKazhdanPropertyT Lbar_compressed
  refine ⟨hcomap, ?_, ?_, ?_⟩
  · rw [actualCoronaMFResidual_markedGroup_eq_comap, hcomap]
  -- `refine` splits the `Iff` into `mp` then `mpr`, so the direction that
  -- *consumes* the radical identity comes first.
  · intro hEq
    -- `proj` is surjective, so the two preimages agree only if the two
    -- subgroups do: this is the reverse direction the manuscript's
    -- "exactly when" asserts.
    have hsign : actualCoronaMFResidual SignFreeQuotient
        = signFreeCollapseDefect := by
      have hpre := actualCoronaMFResidual_markedGroup_eq_comap.symm.trans hEq
      exact Subgroup.comap_injective (QuotientGroup.mk'_surjective markSubgroup)
        hpre
    -- and then the collapse reduction turns that into triviality of the
    -- radical of the second quotient, which is the MF property.
    have hbot : actualCoronaMFResidual
        (SignFreeQuotient ⧸ signFreeCollapseDefect) = ⊥ := by
      have h1 : (actualCoronaMFResidual
          (SignFreeQuotient ⧸ signFreeCollapseDefect)).comap
            (QuotientGroup.mk' signFreeCollapseDefect)
          = signFreeCollapseDefect := hcomap.symm.trans hsign
      have h2 : (⊥ : Subgroup (SignFreeQuotient ⧸ signFreeCollapseDefect)).comap
            (QuotientGroup.mk' signFreeCollapseDefect)
          = signFreeCollapseDefect := by
        -- named rather than left to `simp`: the kernel of `mk'` is the
        -- subgroup itself, and this step should not move when the simp set does
        ext x
        rw [Subgroup.mem_comap, Subgroup.mem_bot, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff]
      exact Subgroup.comap_injective
        (QuotientGroup.mk'_surjective signFreeCollapseDefect)
        (h1.trans h2.symm)
    exact isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot.mpr hbot
  · intro hMF
    have hquot := hexact hMF
    rw [actualCoronaMFResidual_markedGroup_eq_comap, hquot]

end

end LiteralSignFreeRadicalReduction
end GroupApproximation
