import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RubinTransportLattice
import GroupApproximation.Meta.AxiomGuard

/-!
# Rubin transport, part 2: open transport from a clopen neighbourhood basis

Lane `sk-flip-20`.

**Truth check.** `RigidPolarOpenTransportStatement` is TRUE, not false.  Isomorphisms of
topological full groups of Cantor minimal systems are spatial (Rubin), so `Φ F_U = F_{hU}` for a
homeomorphism `h`.  The `sk-flip-19` counterexample (`RubinRecognitionFalse.lean`,
`P = F_A × D`) is a rigid polar that is not of the form `F_O`.  It shows only that the
rigid-polar clauses cannot RECOGNISE rigid stabilisers (`RigidPolarRecognitionStatement` is false).
It is not the image of any `F_U`, so it does not refute open transport.  Nothing below uses
Recognition or any other false statement.

**Manuscript.** The FlipConverse chain serves census row `2e7c7d9ab149` ("for topological full
groups the converse holds").  That row is dropped in `metadata/SK_SENTENCE_OVERRIDES.tsv`: it names
no sentence of the current `simple_kazhdan_sofic_group.tex`, which has no flip-conjugacy sentence.
So the endpoint below serves the recorded printed converse, and no live tex sentence.

**Isolated gap.** `RigidPolarBasisOpenTransportStatement` asks for open transport only for SOME
clopen neighbourhood `V ⊆ W` of each point `x` in each open `W`, i.e. on a neighbourhood basis
chosen by the prover.  It does not ask for every clopen set.

* It is TRUE: `rigidPolarBasisOpenTransport_of_rigidPolarOpenTransport`, using the clopen basis
  of a Stone space.
* It is strictly smaller in proof content.  The reduction
  `rigidPolarOpenTransport_of_rigidPolarBasisOpenTransport` carries the whole global part of the
  argument:
  - compactness of a clopen `U` gives a finite cover by basis sets inside `U`;
  - finite induction uses `rubinTransport_rigid_empty` and `rubinTransport_rigid_union`, the
    centraliser lattice calculus `F_{U₁ ∪ U₂} = C(C F_{U₁} ⊓ C F_{U₂})`.

  What is left is purely local: arbitrarily small clopen pieces must be transported.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

/-- Open transport of rigid stabilisers, required only on a clopen neighbourhood basis. For every
isomorphism `Φ`, every point `x` and every open `W ∋ x`, SOME clopen `V` with `x ∈ V ⊆ W` has
`Φ F_V = F_O` for an open `O`.  TRUE (`rigidPolarBasisOpenTransport_of_rigidPolarOpenTransport`). -/
def RigidPolarBasisOpenTransportStatement : Prop :=
  ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] [Nonempty X]
    [TopologicalSpace.MetrizableSpace X] [CompactSpace Y] [T2Space Y]
    [TotallyDisconnectedSpace Y] [PerfectSpace Y] [Nonempty Y]
    [TopologicalSpace.MetrizableSpace Y] (T : X ≃ₜ X) (S : Y ≃ₜ Y),
    IsMinimalHomeo T → IsMinimalHomeo S →
      ∀ Φ : topologicalFullGroup T ≃* topologicalFullGroup S, ∀ (x : X) (W : Set X),
        IsOpen W → x ∈ W →
          ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ W ∧
            ∃ O : Set Y, IsOpen O ∧
              rubinTransport Φ (rubinRigidSubgroup T V) = rubinRigidSubgroup S O

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RigidPolarBasisOpenTransportStatement

/-- Truth check: full open transport implies the basis version (clopen sets form a basis). -/
theorem rigidPolarBasisOpenTransport_of_rigidPolarOpenTransport
    (h : RigidPolarOpenTransportStatement) : RigidPolarBasisOpenTransportStatement :=
  fun X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ T S hT hS Φ x W hW hxW => by
    obtain ⟨V, hVc, hxV, hVW⟩ := isTopologicalBasis_isClopen.exists_subset_of_mem_open hxW hW
    exact ⟨V, hVc, hxV, hVW, h X Y T S hT hS Φ V hVc⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rigidPolarBasisOpenTransport_of_rigidPolarOpenTransport

/-- The reduction: open transport on a clopen neighbourhood basis gives open transport for every
clopen set.  A clopen `U` is compact, so it is a finite union of basis pieces `V_x ⊆ U`.  Open
transport is closed under finite unions (`rubinTransport_rigid_empty`,
`rubinTransport_rigid_union`). -/
theorem rigidPolarOpenTransport_of_rigidPolarBasisOpenTransport
    (h : RigidPolarBasisOpenTransportStatement) : RigidPolarOpenTransportStatement :=
  fun X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ T S hT hS Φ U hU => by
    classical
    have hb : ∀ x : U, ∃ V : Set X, IsClopen V ∧ (x : X) ∈ V ∧ V ⊆ U ∧
        ∃ O : Set Y, IsOpen O ∧
          rubinTransport Φ (rubinRigidSubgroup T V) = rubinRigidSubgroup S O :=
      fun x => h X Y T S hT hS Φ x U hU.isOpen x.2
    choose V hVc hxV hVU hVO using hb
    obtain ⟨t, ht⟩ := hU.isClosed.isCompact.elim_finite_subcover V (fun i => (hVc i).isOpen)
      (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
    have hUt : U = ⋃ i ∈ t, V i :=
      Set.Subset.antisymm ht (Set.iUnion₂_subset fun i _ => hVU i)
    have key : ∀ s : Finset U, IsClopen (⋃ i ∈ s, V i) ∧ ∃ O : Set Y, IsOpen O ∧
        rubinTransport Φ (rubinRigidSubgroup T (⋃ i ∈ s, V i)) = rubinRigidSubgroup S O := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        have e : (⋃ i ∈ (∅ : Finset U), V i) = ∅ := by simp
        rw [e]
        exact ⟨isClopen_empty, rubinTransport_rigid_empty hT hS Φ⟩
      | insert a s _ ih =>
        rw [Finset.set_biUnion_insert]
        obtain ⟨hc, O₂, hO₂, e₂⟩ := ih
        obtain ⟨O₁, hO₁, e₁⟩ := hVO a
        exact ⟨(hVc a).union hc, rubinTransport_rigid_union hT hS Φ (hVc a) hc hO₁ hO₂ e₁ e₂⟩
    rw [hUt]
    exact (key t).2

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rigidPolarOpenTransport_of_rigidPolarBasisOpenTransport

/-- The printed converse for topological full groups, reduced to the basis statement.  It routes
through `RigidPolarOpenTransportStatement` and `SupportDisjointnessTransportStatement`, never
through Recognition. -/
theorem manuscriptSentence_flipConjugateConverse_of_rigidPolarBasisOpenTransport
    (h : RigidPolarBasisOpenTransportStatement) {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] [Nonempty X] [TopologicalSpace.MetrizableSpace X] [CompactSpace Y]
    [T2Space Y] [TotallyDisconnectedSpace Y] [PerfectSpace Y] [Nonempty Y]
    [TopologicalSpace.MetrizableSpace Y] {T : X ≃ₜ X} {S : Y ≃ₜ Y}
    (hT : IsMinimalHomeo T) (hS : IsMinimalHomeo S) :
    Nonempty (topologicalFullGroup T ≃* topologicalFullGroup S) ↔ FlipConjugate T S :=
  manuscriptSentence_flipConjugateConverse_of_rigidPolarOpenTransport
    (rigidPolarOpenTransport_of_rigidPolarBasisOpenTransport h) hT hS

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.manuscriptSentence_flipConjugateConverse_of_rigidPolarBasisOpenTransport

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse
