import GroupApproximation.BooneHigman.Metabelian.EnvelopeFiniteIndexAbel
import GroupApproximation.BooneHigman.Metabelian.EnvelopeSplit
import GroupApproximation.Meta.AxiomGuard

/-!
# Finite index of `[V, V]` for the envelope, reduced to generator data

For `V = envelopeV X H = V_{Fin 2 × X}(K)` the target is `RNCommutatorFiniteIndexStatement`.
This module isolates one generator-level Statement:

* `RNGeneratorTorsionStatement`: there are `m > 0` and a finite `T ⊆ V`, each `t ∈ T` with
  `t ^ m ∈ [V, V]`, such that every generator of `V` (an element of `V_Y` or a localised element
  of `K`) lies in `closure T ⊔ ⁅V, V⁆`;
* `rnFiniteIndex_of_generatorTorsion`: it implies `RNCommutatorFiniteIndexStatement`.

Route: `commutator_finiteIndex_of_gens` with `S = rnGenerators K` and `V = closure S`
(definitionally).

*Why this is strictly smaller.*  The Statement only asks about the generators of `V` and a
finite set `T`; the passage to all of `V` (closure argument through the subtype), to the
abelianisation (its images of `T` generate it and are `m`-torsion) and to finiteness of the
quotient (structure theorem for finitely generated torsion abelian groups,
`CommGroup.finite_of_fg_torsion`) is proved here.

*Truth.*  `|Y| = 2 |X|` is even, so `V_Y` is perfect (Higman) and its elements lie in `[V, V]`.
A localised `k ∈ K` is conjugate in `V_Y` to its localisations at every nonempty word, and splits
as a `V_Y`-element times the localised states at the `2 |X|` letters, whose `Fin 2`-copies
coincide; so the abelianisation `A` of `V` is the image of `K`, and `A = 2 A`.  `H` is finitely
presented, hence `K ≅ H` is finitely generated and so is `A`; a finitely generated abelian group
with `A = 2 A` is finite.  Then `T` = lifts of the elements of `A` and `m = |A|` witness the
Statement.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

/-- Generator data for `V = V_{Fin 2 × X}(K)`: finitely many elements of `V`, torsion modulo
`[V, V]` with one exponent, generate every generator of `V` modulo `⁅V, V⁆`. -/
def RNGeneratorTorsionStatement : Prop :=
  ∀ (X : Type) [Finite X] [Nontrivial X] (H : Subgroup (TreeAut X)), IsSelfSimilar H →
    Group.IsFinitelyPresented H →
      ∃ (m : ℕ) (T : Set ↥(envelopeV X H)), 0 < m ∧ T.Finite ∧
        (∀ g ∈ rnGenerators (envelopeK 2 H),
          g ∈ Subgroup.closure (Subtype.val '' T) ⊔ ⁅envelopeV X H, envelopeV X H⁆) ∧
        ∀ t ∈ T, t ^ m ∈ commutator ↥(envelopeV X H)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.RNGeneratorTorsionStatement

/-- The generator data gives `RNCommutatorFiniteIndexStatement`. -/
theorem rnFiniteIndex_of_generatorTorsion (h : RNGeneratorTorsionStatement) :
    RNCommutatorFiniteIndexStatement := by
  intro X _ _ H hH hHfp
  obtain ⟨m, T, hm, hT, hgen, hTpow⟩ := h X H hH hHfp
  exact commutator_finiteIndex_of_gens (V := envelopeV X H)
    (S := rnGenerators (envelopeK 2 H)) le_rfl hT hgen hm hTpow

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnFiniteIndex_of_generatorTorsion

end GroupApproximation.BooneHigman.Metabelian.Envelope
