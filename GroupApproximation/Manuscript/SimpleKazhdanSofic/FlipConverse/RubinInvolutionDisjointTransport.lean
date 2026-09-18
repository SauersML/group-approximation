import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RubinInvolutionDisjointWitness
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InvolReducePlug
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RubinInvolutionSeparationReduce
import GroupApproximation.Meta.AxiomGuard

/-!
# Group-theoretic definability of disjoint involution supports, part 3: transport

Lane `sk-flip-23c`.  Census row `2e7c7d9ab149` (tex: "for topological full groups the converse
holds"; the row names no sentence of the current tex, so there is no tex line).

For involutions `f, k` of `[[T]]` (`T` minimal on a Cantor-type space), the moved sets are
disjoint iff `RubinInvolutionDisjointFormula f k` holds in the group `[[T]]`
(`rubinInvDisj_formula_iff`).  The formula is first order, so every isomorphism
`[[T]] ≃* [[S]]` preserves it.  Consequences:
* `rubinInvDisj_involutionDisjointnessTransport`: `InvolutionDisjointnessTransportStatement`
  holds unconditionally.
* `rubinInvDisj_rubinInvolutionBasisSeparation`: so does `RubinInvolutionBasisSeparationStatement`.
* `rubinInvDisj_flipConjugateConverse`: the printed converse for topological full groups,
  through `manuscriptSentence_flipConjugateConverse_of_involutionDisjointnessTransport'`.

The `C(f)`-conjugate test of `rubinInvolution_conj_commute_collapse` degenerates.  This one
conjugates `f` by elements of `C(f k)`, and does not.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

/-- For involutions of `[[T]]`, the formula characterises disjoint moved sets. -/
theorem rubinInvDisj_formula_iff {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] {T : X ≃ₜ X} (hT : IsMinimalHomeo T)
    (f k : topologicalFullGroup T) (hff : f * f = 1) (hkk : k * k = 1) :
    RubinInvolutionDisjointFormula f k ↔
      Disjoint (movedSet (f : X ≃ₜ X)) (movedSet (k : X ≃ₜ X)) := by
  constructor
  · rintro ⟨hfk, hform⟩
    refine rubinInvDisj_disjoint_of_formula hT f.2 k.2 (congrArg Subtype.val hff)
      (congrArg Subtype.val hkk) (congrArg Subtype.val hfk) fun g hg hgc => ?_
    exact congrArg Subtype.val (hform ⟨g, hg⟩ (Subtype.ext hgc))
  · intro hd
    obtain ⟨hfk, hform⟩ := rubinInvDisj_formula_of_disjoint hd
    exact ⟨Subtype.ext hfk, fun g hg => Subtype.ext (hform g (congrArg Subtype.val hg))⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinInvDisj_formula_iff

/-- Isomorphisms of topological full groups carry involutions with disjoint moved sets to
involutions with disjoint moved sets. -/
theorem rubinInvDisj_involutionDisjointnessTransport :
    InvolutionDisjointnessTransportStatement :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hT hS Φ f k hff hkk hfk => by
    have hΦff : Φ f * Φ f = 1 := by rw [← map_mul Φ f f, hff, map_one]
    have hΦkk : Φ k * Φ k = 1 := by rw [← map_mul Φ k k, hkk, map_one]
    exact (rubinInvDisj_formula_iff hS (Φ f) (Φ k) hΦff hΦkk).1
      (rubinInvDisj_formula_map Φ ((rubinInvDisj_formula_iff hT f k hff hkk).2 hfk))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinInvDisj_involutionDisjointnessTransport

/-- Involution separation on a clopen neighbourhood basis holds unconditionally. -/
theorem rubinInvDisj_rubinInvolutionBasisSeparation :
    RubinInvolutionBasisSeparationStatement :=
  fun X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ T S hT hS Φ x W hW hxW => by
    obtain ⟨V, hVc, hxV, hVW⟩ := isTopologicalBasis_isClopen.mem_nhds_iff.1 (hW.mem_nhds hxW)
    refine ⟨V, hVc, hxV, hVW, fun f k hff hkk hf hk => ?_⟩
    refine rubinInvDisj_involutionDisjointnessTransport X Y T S hT hS Φ f k hff hkk ?_
    refine Set.disjoint_left.2 fun y hyf hyk => ?_
    exact (Set.mem_compl_iff _ _).1 (supportedIn_iff_movedSet_subset.1 hk hyk)
      (supportedIn_iff_movedSet_subset.1 hf hyf)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinInvDisj_rubinInvolutionBasisSeparation

/-- The printed converse for topological full groups of minimal Cantor-type systems:
`[[T]] ≅ [[S]]` iff `T` is flip conjugate to `S`. -/
theorem rubinInvDisj_flipConjugateConverse {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] [Nonempty X] [TopologicalSpace.MetrizableSpace X] [CompactSpace Y]
    [T2Space Y] [TotallyDisconnectedSpace Y] [PerfectSpace Y] [Nonempty Y]
    [TopologicalSpace.MetrizableSpace Y] {T : X ≃ₜ X} {S : Y ≃ₜ Y}
    (hT : IsMinimalHomeo T) (hS : IsMinimalHomeo S) :
    Nonempty (topologicalFullGroup T ≃* topologicalFullGroup S) ↔ FlipConjugate T S :=
  manuscriptSentence_flipConjugateConverse_of_involutionDisjointnessTransport'
    rubinInvDisj_involutionDisjointnessTransport hT hS

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinInvDisj_flipConjugateConverse

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse
