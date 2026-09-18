import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RigidSplit
import GroupApproximation.Meta.AxiomGuard

/-!
# Involution reduction, part 1: the two statements

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds"; the row is
recorded as absent from the current tex, so there is no tex line).  Lane `sk-flip-10`.

* `InvolutionDisjointnessTransportStatement` is `SupportDisjointnessTransportStatement`
  (`RigidSplit.lean`) with the extra hypotheses `f * f = 1` and `k * k = 1`.  An isomorphism
  `Φ : [[T]] ≃* [[S]]` has to carry pairs of *involutions* with disjoint moved sets to pairs with
  disjoint moved sets.  It is a special case of the support statement
  (`involutionDisjointnessTransport_of_supportDisjointnessTransport`), so it is true whenever
  the support statement is.  By note N1 of the lane map, that holds by spatial realization.
* `InvolutionSplitCoverStatement` is the interface of lane `sk-flip-09`
  (`exists_split_of_involution_disjoint`, not yet on disk).  It is the split cover
  `exists_split_of_disjoint` (`RigidSplitCover.lean`) with both transport hypotheses weakened
  to involutions.  It is stated here at universe `Type`, with the full instance package of the
  corpus statements (including `Nonempty` and `MetrizableSpace`).  That makes it no stronger
  than lane 09's theorem, which gives it directly by
  `fun X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ T S hT hS hTa hSa Φ hΦ hΦs U hU =>
    exists_split_of_involution_disjoint hT hS hTa hSa Φ hΦ hΦs hU`.

Why `InvolutionSplitCoverStatement` is true (proof sketch for lane 09):
1. *Cover.*  Each `x ∈ U` is moved by an involution `f ∈ F_U` (lane 08).  Moved sets are
   clopen and `U` is compact, so finitely many involutions `f_i ∈ F_U` cover `U`.  Put
   `V = ⋃ movedSet (Φ f_i)`.
2. `Φ F_U ⊆ F_V`.  Let `f ∈ F_U` and `N = movedSet (Φ f) \ V`.  Every involution `σ` supported
   in `N` has moved set disjoint from each `movedSet (Φ f_i)`.  The elements `Φ f_i` are
   involutions, so the transport hypothesis for `Φ.symm` puts `Φ.symm σ` in `F_{Uᶜ}`.  Hence
   `σ` commutes with `Φ f`.  The proof of `supportedIn_compl_of_forall_commute` only tests
   against the swap involution of `exists_supportedIn_ne_one`, so `Φ f` fixes `N` pointwise
   and `N = ∅`.
3. `Φ F_{Uᶜ} ⊆ F_{Vᶜ}`.  The corpus argument applies the transport hypothesis to an
   arbitrary `k ∈ F_{Uᶜ}`, which is not allowed here.  Instead, run step 2 for the clopen set
   `Uᶜ`.  It gives involutions `f'_j ∈ F_{Uᶜ}` and `V' = ⋃ movedSet (Φ f'_j)` with
   `Φ F_{Uᶜ} ⊆ F_{V'}`.  Each `f'_j` and `f_i` are involutions with disjoint moved sets, so
   `V' ∩ V = ∅`, and therefore `F_{V'} ⊆ F_{Vᶜ}`.

The conclusion does not mention the transport hypotheses.  It is the conclusion of
`RigidStabilizerSplitStatement`, which is true by N1 (`involutionSplitCover_of_rigidStabilizerSplit`).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

/-- Isomorphisms of topological full groups of Cantor minimal systems carry pairs of involutions
with disjoint moved sets to pairs with disjoint moved sets.  This is
`SupportDisjointnessTransportStatement` restricted to involutions. -/
def InvolutionDisjointnessTransportStatement : Prop :=
  ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] [Nonempty X]
    [TopologicalSpace.MetrizableSpace X] [CompactSpace Y] [T2Space Y]
    [TotallyDisconnectedSpace Y] [PerfectSpace Y] [Nonempty Y]
    [TopologicalSpace.MetrizableSpace Y] (T : X ≃ₜ X) (S : Y ≃ₜ Y),
    IsMinimalHomeo T → IsMinimalHomeo S →
      ∀ Φ : topologicalFullGroup T ≃* topologicalFullGroup S, ∀ f k : topologicalFullGroup T,
        f * f = 1 → k * k = 1 →
        Disjoint (movedSet (f : X ≃ₜ X)) (movedSet (k : X ≃ₜ X)) →
          Disjoint (movedSet ((Φ f : topologicalFullGroup S) : Y ≃ₜ Y))
            (movedSet ((Φ k : topologicalFullGroup S) : Y ≃ₜ Y))

/-- The involution statement is a special case of the support statement. -/
theorem involutionDisjointnessTransport_of_supportDisjointnessTransport
    (hd : SupportDisjointnessTransportStatement) : InvolutionDisjointnessTransportStatement :=
  fun X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ T S hT hS Φ f k _ _ hfk => hd X Y T S hT hS Φ f k hfk

/-- Interface of lane `sk-flip-09` (`exists_split_of_involution_disjoint`, not yet on disk):
the split cover of `exists_split_of_disjoint`, with both transport hypotheses restricted to
involutions.  It is stated at universe `Type` with the instance package of the corpus statements. -/
def InvolutionSplitCoverStatement : Prop :=
  ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] [Nonempty X]
    [TopologicalSpace.MetrizableSpace X] [CompactSpace Y] [T2Space Y]
    [TotallyDisconnectedSpace Y] [PerfectSpace Y] [Nonempty Y]
    [TopologicalSpace.MetrizableSpace Y] (T : X ≃ₜ X) (S : Y ≃ₜ Y),
    IsMinimalHomeo T → IsMinimalHomeo S → IsAperiodic T → IsAperiodic S →
      ∀ Φ : topologicalFullGroup T ≃* topologicalFullGroup S,
        (∀ f k : topologicalFullGroup T, f * f = 1 → k * k = 1 →
          Disjoint (movedSet (f : X ≃ₜ X)) (movedSet (k : X ≃ₜ X)) →
            Disjoint (movedSet ((Φ f : topologicalFullGroup S) : Y ≃ₜ Y))
              (movedSet ((Φ k : topologicalFullGroup S) : Y ≃ₜ Y))) →
        (∀ f k : topologicalFullGroup S, f * f = 1 → k * k = 1 →
          Disjoint (movedSet (f : Y ≃ₜ Y)) (movedSet (k : Y ≃ₜ Y)) →
            Disjoint (movedSet ((Φ.symm f : topologicalFullGroup T) : X ≃ₜ X))
              (movedSet ((Φ.symm k : topologicalFullGroup T) : X ≃ₜ X))) →
        ∀ U : Set X, IsClopen U →
          ∃ V : Set Y, IsClopen V ∧
            (∀ g : topologicalFullGroup T, SupportedIn (g : X ≃ₜ X) U →
              SupportedIn ((Φ g : topologicalFullGroup S) : Y ≃ₜ Y) V) ∧
            ∀ g : topologicalFullGroup T, SupportedIn (g : X ≃ₜ X) Uᶜ →
              SupportedIn ((Φ g : topologicalFullGroup S) : Y ≃ₜ Y) Vᶜ

/-- The involution split cover follows from the split statement.  Its conclusion ignores the
transport hypotheses, so this is a truth check of the interface relative to N1. -/
theorem involutionSplitCover_of_rigidStabilizerSplit
    (hsplit : RigidStabilizerSplitStatement) : InvolutionSplitCoverStatement :=
  fun X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ T S hT hS _ _ Φ _ _ U hU => hsplit X Y T S hT hS Φ U hU

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InvolutionDisjointnessTransportStatement
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.involutionDisjointnessTransport_of_supportDisjointnessTransport
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InvolutionSplitCoverStatement
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.involutionSplitCover_of_rigidStabilizerSplit
