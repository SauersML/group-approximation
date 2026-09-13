import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedForms
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefectShadow
import GroupApproximation.Meta.AxiomGuard

/-!
# Producers of `HSVanishes`

`HSVanishes B g` (`PrintedForms.lean`) is the printed `‖V_n(g) − 1‖₂ → 0` for
one operator norm asymptotic representation `B = (V_n)`.  Corollary
`cor:defect-hs` proves it on the intrinsic defect of a property-(T) subgroup,
inside the named proposition `PrintedDefectHS`.  The declarations below conclude
`HSVanishes` itself:

* `hsVanishes_of_mem_opToHSShadowResidual`: every element of the shadow residual
  `R_{∞→2}(G) = ⋂_V K₂(V)`;
* `hsVanishes_of_mem_printedDefect`: every `d ∈ 𝔇_G(L)` for a property-(T)
  subgroup `L`, which is Corollary `cor:defect-hs` for one element;
* `PrintedCompressionCriterionHSHypothesis`: the first sentence of the proof of
  Theorem `thm:compression-criterion`, for the printed `K ≤ 𝔇_G(L)`;
* `PrintedCompressionCriterionCoronaTrivial`: the first clause of the second
  sentence, Theorem `thm:normal-kazhdan` (`manuscriptPrintedNormalKazhdan`)
  applied to that `K`, with its Hilbert--Schmidt hypothesis supplied by the first
  sentence.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

/-- Every element of the shadow residual tends to `1` in normalized
Hilbert--Schmidt norm along every operator norm asymptotic representation, since
`R_{∞→2}(G) = ⋂_V K₂(V)` (`mem_opToHSShadowResidual_iff_forall_hsKernel`). -/
theorem hsVanishes_of_mem_opToHSShadowResidual {G : Type} [Group G]
    (B : OpAlmostRepresentation G) {x : G} (hx : x ∈ opToHSShadowResidual G) :
    HSVanishes B x := by
  rw [HSVanishes, ← isHSNull_iff_tendsto, ← mem_hsKernel_iff]
  exact (mem_opToHSShadowResidual_iff_forall_hsKernel x).1 hx B

/-- **Corollary `cor:defect-hs` (tex line 572), for one element.**

> Let `L ≤ G` have property (T) and let `(V_n)` be an operator norm asymptotic
> representation of `G`.  Then `‖V_n(d) − 1‖₂ → 0` `(d ∈ 𝔇_G(L))`.

The printed defect lies in the shadow residual by the generator-by-generator
proof (`printedDefect_le_opToHSShadowResidual_direct`). -/
theorem hsVanishes_of_mem_printedDefect {G : Type} [Group G] {L : Subgroup G}
    (hL : HasKazhdanPropertyT.{0, 0} ↥L) (B : OpAlmostRepresentation G) {d : G}
    (hd : d ∈ printedDefect L) : HSVanishes B d :=
  hsVanishes_of_mem_opToHSShadowResidual B
    (printedDefect_le_opToHSShadowResidual_direct L hL hd)

/-- **Theorem `thm:compression-criterion`, proof, first sentence (tex line 717).**

> By Corollary `cor:defect-hs`, every operator norm asymptotic representation of
> `G` satisfies `‖V_n(k) − 1‖₂ → 0` for `k ∈ K ≤ 𝔇_G(L)`.

`G` countable, `L ≤ G` with property (T), `K ⊴ G` with property (T) and
`K ≤ 𝔇_G(L)`, as in the theorem. -/
def PrintedCompressionCriterionHSHypothesis : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (L : Subgroup G),
    HasKazhdanPropertyT.{0, 0} ↥L →
      ∀ (K : Subgroup G) [K.Normal], HasKazhdanPropertyT.{0, 0} ↥K →
        K ≤ printedDefect L →
          ∀ (B : OpAlmostRepresentation G), ∀ k ∈ K, HSVanishes B k

theorem manuscriptPrintedCompressionCriterionHSHypothesis :
    PrintedCompressionCriterionHSHypothesis := by
  intro G _ _ L hL K _ _ hKD B k hk
  exact hsVanishes_of_mem_printedDefect hL B (hKD hk)

/-- **Theorem `thm:compression-criterion`, proof, second sentence, first clause
(tex line 717).**

> By Theorem `thm:normal-kazhdan`, every corona homomorphism is then trivial on
> `K`, ...

Theorem `thm:normal-kazhdan` in its printed form (`PrintedNormalKazhdan`), whose
hypothesis "every operator norm asymptotic representation `(V_n)` of `G`
satisfies `‖V_n(k) − 1‖₂ → 0` for all `k ∈ K`" is discharged by the first
sentence. -/
def PrintedCompressionCriterionCoronaTrivial : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (L : Subgroup G),
    HasKazhdanPropertyT.{0, 0} ↥L →
      ∀ (K : Subgroup G) [K.Normal], HasKazhdanPropertyT.{0, 0} ↥K →
        K ≤ printedDefect L → ∀ k ∈ K, ManuscriptCoronaMFInvisible k

theorem manuscriptPrintedCompressionCriterionCoronaTrivial :
    PrintedCompressionCriterionCoronaTrivial := by
  intro G _ _ L hL K _ hT hKD
  exact manuscriptPrintedNormalKazhdan G K hT
    (manuscriptPrintedCompressionCriterionHSHypothesis G L hL K hT hKD)

end OneSidedMFRadical
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_axioms
  Manuscript.OneSidedMFRadical.hsVanishes_of_mem_opToHSShadowResidual
#audit_axioms
  Manuscript.OneSidedMFRadical.hsVanishes_of_mem_printedDefect
#audit_closed_axioms
  Manuscript.OneSidedMFRadical.manuscriptPrintedCompressionCriterionHSHypothesis
#audit_closed_axioms
  Manuscript.OneSidedMFRadical.manuscriptPrintedCompressionCriterionCoronaTrivial
