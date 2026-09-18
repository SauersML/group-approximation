import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RubinTransportBasis
import GroupApproximation.Meta.AxiomGuard

/-!
# Rubin transport, part 3: basis open transport from generator support separation

Lane `sk-flip-21`.  Target: `RigidPolarBasisOpenTransportStatement` (RubinTransportBasis.lean).

**Truth check.** The target is TRUE, not false.  Isomorphisms of topological full groups of Cantor
minimal systems are spatial (Rubin; note N1 of the cartography), and the proved reductions of
lanes `sk-flip-16/20` make it equivalent to `RigidPolarOpenTransportStatement`.  The gap isolated
below is TRUE: `rubinBasisGeneratorSeparation_of_rigidPolarBasisOpenTransport` derives it.

**Why the target is not closed here.** The Rubin-type algebraic input in the corpus,
`exists_commutator_witness_of_not_disjoint` (InfraWitFinal.lean), goes in one direction only.
Overlapping supports give a nontrivial iterated commutator.  The converse is false (note N4),
and rigid polars cannot recognise rigid stabilisers (`RigidPolarRecognitionStatement` is FALSE,
RubinRecognitionFalse.lean).  So pulling commutator identities back through `Φ` does not give
disjointness on the image side.  The local, first-order definability of `F_V` is the remaining
content of Rubin's theorem.

**Isolated gap.** `RubinBasisGeneratorSeparationStatement`: for each `x` in an open `W` there is a
clopen `V` with `x ∈ V ⊆ W`, together with sets `G₁, G₂` whose generated subgroups contain `F_V`
and `F_{Vᶜ}`, such that `Φ f` and `Φ k` have disjoint moved sets for all `f ∈ G₁`, `k ∈ G₂`.

It is strictly smaller in proof content.  It asks for no open set `O` and no subgroup equality,
only pointwise disjointness of image supports on chosen generators.  The reduction
`rigidPolarBasisOpenTransport_of_rubinBasisGeneratorSeparation` carries the rest:

* closure induction: `rubinTransport_le_rigid_of_closure` passes from generators to `F_V`, `F_{Vᶜ}`;
* the open set `O = ⋃_{f ∈ G₁} movedSet (Φ f)`;
* the double-centraliser identity `Φ F_V = C(Φ F_{Vᶜ})` together with `C(F_O) = F_{Oᶜ}`
  (`rubinTransport_rigid_eq_of_le_compl`).

It is no restatement of `SupportDisjointnessTransportStatement`, which needs every support-disjoint
pair.  Here only pairs from the chosen generators of one basis clopen per point are needed.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

/-- Generator support separation on a clopen neighbourhood basis.  For every isomorphism `Φ`, every
point `x` and every open `W ∋ x`, there are SOME clopen `V` with `x ∈ V ⊆ W` and SOME sets `G₁`,
`G₂` with `F_V ≤ ⟨G₁⟩` and `F_{Vᶜ} ≤ ⟨G₂⟩`, such that `Φ f`, `Φ k` have disjoint moved sets for
all `f ∈ G₁`, `k ∈ G₂`.  TRUE (`rubinBasisGeneratorSeparation_of_rigidPolarBasisOpenTransport`). -/
def RubinBasisGeneratorSeparationStatement : Prop :=
  ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] [Nonempty X]
    [TopologicalSpace.MetrizableSpace X] [CompactSpace Y] [T2Space Y]
    [TotallyDisconnectedSpace Y] [PerfectSpace Y] [Nonempty Y]
    [TopologicalSpace.MetrizableSpace Y] (T : X ≃ₜ X) (S : Y ≃ₜ Y),
    IsMinimalHomeo T → IsMinimalHomeo S →
      ∀ Φ : topologicalFullGroup T ≃* topologicalFullGroup S, ∀ (x : X) (W : Set X),
        IsOpen W → x ∈ W →
          ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ W ∧
            ∃ G₁ G₂ : Set (topologicalFullGroup T),
              rubinRigidSubgroup T V ≤ Subgroup.closure G₁ ∧
              rubinRigidSubgroup T Vᶜ ≤ Subgroup.closure G₂ ∧
              ∀ f ∈ G₁, ∀ k ∈ G₂,
                Disjoint (movedSet ((Φ f : topologicalFullGroup S) : Y ≃ₜ Y))
                  (movedSet ((Φ k : topologicalFullGroup S) : Y ≃ₜ Y))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RubinBasisGeneratorSeparationStatement

section RubinBasisSeparation

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {T : X ≃ₜ X} {S : Y ≃ₜ Y}

/-- Closure induction through `Φ`: if every generator in `G` is sent into `F_A`, then so is every
subgroup `H ≤ ⟨G⟩`. -/
theorem rubinTransport_le_rigid_of_closure {G : Set (topologicalFullGroup T)}
    {H : Subgroup (topologicalFullGroup T)} (Φ : topologicalFullGroup T ≃* topologicalFullGroup S)
    (hH : H ≤ Subgroup.closure G) {A : Set Y}
    (hA : ∀ g ∈ G, SupportedIn ((Φ g : topologicalFullGroup S) : Y ≃ₜ Y) A) :
    rubinTransport Φ H ≤ rubinRigidSubgroup S A := by
  have hcl : Subgroup.closure G ≤ (rubinRigidSubgroup S A).comap Φ.toMonoidHom := by
    rw [Subgroup.closure_le]
    intro g hg
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, mem_rubinRigidSubgroup]
    exact hA g hg
  intro p hp
  rw [mem_rubinTransport] at hp
  have hp2 : Φ.toMonoidHom (Φ.symm p) ∈ rubinRigidSubgroup S A :=
    Subgroup.mem_comap.1 (hcl (hH hp))
  rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at hp2
  exact hp2

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinTransport_le_rigid_of_closure

variable [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] [PerfectSpace X]
  [CompactSpace Y] [T2Space Y] [TotallyDisconnectedSpace Y] [PerfectSpace Y]

/-- Separation gives equality.  If `V` is clopen, `O` is open, `Φ F_V ≤ F_O` and
`Φ F_{Vᶜ} ≤ F_{Oᶜ}`, then `Φ F_V = F_O`.  Proof: `Φ F_V = C(Φ F_{Vᶜ})`, and every
`q ∈ Φ F_{Vᶜ}` lies in `F_{Oᶜ} = C(F_O)`. -/
theorem rubinTransport_rigid_eq_of_le_compl (hT : IsMinimalHomeo T) (hS : IsMinimalHomeo S)
    (Φ : topologicalFullGroup T ≃* topologicalFullGroup S) {V : Set X} (hV : IsClopen V)
    {O : Set Y} (hO : IsOpen O)
    (h₁ : rubinTransport Φ (rubinRigidSubgroup T V) ≤ rubinRigidSubgroup S O)
    (h₂ : rubinTransport Φ (rubinRigidSubgroup T Vᶜ) ≤ rubinRigidSubgroup S Oᶜ) :
    rubinTransport Φ (rubinRigidSubgroup T V) = rubinRigidSubgroup S O := by
  refine le_antisymm h₁ fun k hk => ?_
  have hV' : rubinTransport Φ (rubinRigidSubgroup T V) =
      Subgroup.centralizer (rubinTransport Φ (rubinRigidSubgroup T Vᶜ) :
        Set (topologicalFullGroup S)) := by
    rw [rubinTransport_centralizer, centralizer_rubinRigidSubgroup hT hV.compl.isOpen,
      compl_compl]
  rw [hV', Subgroup.mem_centralizer_iff]
  intro q hq
  have hqC : q ∈ Subgroup.centralizer (rubinRigidSubgroup S O : Set (topologicalFullGroup S)) := by
    rw [centralizer_rubinRigidSubgroup hS hO]
    exact h₂ hq
  exact (Subgroup.mem_centralizer_iff.1 hqC k hk).symm

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinTransport_rigid_eq_of_le_compl

/-- Generator separation gives open transport of `F_V`, with
`O = ⋃_{f ∈ G₁} movedSet (Φ f)`. -/
theorem rubinTransport_rigid_of_generatorSeparation (hT : IsMinimalHomeo T)
    (hS : IsMinimalHomeo S) (Φ : topologicalFullGroup T ≃* topologicalFullGroup S) {V : Set X}
    (hV : IsClopen V) {G₁ G₂ : Set (topologicalFullGroup T)}
    (hG₁ : rubinRigidSubgroup T V ≤ Subgroup.closure G₁)
    (hG₂ : rubinRigidSubgroup T Vᶜ ≤ Subgroup.closure G₂)
    (hsep : ∀ f ∈ G₁, ∀ k ∈ G₂,
      Disjoint (movedSet ((Φ f : topologicalFullGroup S) : Y ≃ₜ Y))
        (movedSet ((Φ k : topologicalFullGroup S) : Y ≃ₜ Y))) :
    ∃ O : Set Y, IsOpen O ∧
      rubinTransport Φ (rubinRigidSubgroup T V) = rubinRigidSubgroup S O := by
  have hO : IsOpen (⋃ f : G₁, movedSet ((Φ (f : topologicalFullGroup T) :
      topologicalFullGroup S) : Y ≃ₜ Y)) :=
    isOpen_iUnion fun _ => isOpen_movedSet_of_t2Space _
  refine ⟨_, hO, rubinTransport_rigid_eq_of_le_compl hT hS Φ hV hO
    (rubinTransport_le_rigid_of_closure Φ hG₁ fun f hf => ?_)
    (rubinTransport_le_rigid_of_closure Φ hG₂ fun k hk => ?_)⟩
  · exact supportedIn_iff_movedSet_subset.2 fun y hy => Set.mem_iUnion.2 ⟨⟨f, hf⟩, hy⟩
  · refine supportedIn_iff_movedSet_subset.2 fun y hy => Set.mem_compl fun hyO => ?_
    obtain ⟨f, hfy⟩ := Set.mem_iUnion.1 hyO
    exact Set.disjoint_left.1 (hsep f f.2 k hk) hfy hy

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinTransport_rigid_of_generatorSeparation

end RubinBasisSeparation

/-- The reduction: generator support separation on a clopen basis gives basis open transport. -/
theorem rigidPolarBasisOpenTransport_of_rubinBasisGeneratorSeparation
    (h : RubinBasisGeneratorSeparationStatement) : RigidPolarBasisOpenTransportStatement :=
  fun X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ T S hT hS Φ x W hW hxW => by
    obtain ⟨V, hVc, hxV, hVW, G₁, G₂, hG₁, hG₂, hsep⟩ := h X Y T S hT hS Φ x W hW hxW
    exact ⟨V, hVc, hxV, hVW,
      rubinTransport_rigid_of_generatorSeparation hT hS Φ hVc hG₁ hG₂ hsep⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rigidPolarBasisOpenTransport_of_rubinBasisGeneratorSeparation

/-- Truth check: basis open transport gives generator separation, with `G₁ = F_V` and
`G₂ = F_{Vᶜ}`.  If `Φ F_V = F_O`, then `Φ F_{Vᶜ} = Φ C(F_V) = C(F_O) = F_{Oᶜ}`. -/
theorem rubinBasisGeneratorSeparation_of_rigidPolarBasisOpenTransport
    (h : RigidPolarBasisOpenTransportStatement) : RubinBasisGeneratorSeparationStatement :=
  fun X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ T S hT hS Φ x W hW hxW => by
    obtain ⟨V, hVc, hxV, hVW, O, hO, hPO⟩ := h X Y T S hT hS Φ x W hW hxW
    refine ⟨V, hVc, hxV, hVW, (rubinRigidSubgroup T V : Set (topologicalFullGroup T)),
      (rubinRigidSubgroup T Vᶜ : Set (topologicalFullGroup T)),
      fun g hg => Subgroup.subset_closure hg, fun g hg => Subgroup.subset_closure hg,
      fun f hf k hk => ?_⟩
    have hΦf : Φ f ∈ rubinRigidSubgroup S O := by
      rw [← hPO, mem_rubinTransport, MulEquiv.symm_apply_apply]
      exact hf
    have hΦk : Φ k ∈ rubinRigidSubgroup S Oᶜ := by
      rw [← centralizer_rubinRigidSubgroup hS hO, ← hPO, rubinTransport_centralizer,
        mem_rubinTransport, MulEquiv.symm_apply_apply, centralizer_rubinRigidSubgroup hT hVc.isOpen]
      exact hk
    refine Set.disjoint_left.2 fun y hy1 hy2 => ?_
    exact (Set.mem_compl_iff _ _).1
      (supportedIn_iff_movedSet_subset.1 (mem_rubinRigidSubgroup.1 hΦk) hy2)
      (supportedIn_iff_movedSet_subset.1 (mem_rubinRigidSubgroup.1 hΦf) hy1)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinBasisGeneratorSeparation_of_rigidPolarBasisOpenTransport

/-- The printed converse for topological full groups, reduced to generator separation. -/
theorem manuscriptSentence_flipConjugateConverse_of_rubinBasisGeneratorSeparation
    (h : RubinBasisGeneratorSeparationStatement) {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] [Nonempty X] [TopologicalSpace.MetrizableSpace X] [CompactSpace Y]
    [T2Space Y] [TotallyDisconnectedSpace Y] [PerfectSpace Y] [Nonempty Y]
    [TopologicalSpace.MetrizableSpace Y] {T : X ≃ₜ X} {S : Y ≃ₜ Y}
    (hT : IsMinimalHomeo T) (hS : IsMinimalHomeo S) :
    Nonempty (topologicalFullGroup T ≃* topologicalFullGroup S) ↔ FlipConjugate T S :=
  manuscriptSentence_flipConjugateConverse_of_rigidPolarBasisOpenTransport
    (rigidPolarBasisOpenTransport_of_rubinBasisGeneratorSeparation h) hT hS

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.manuscriptSentence_flipConjugateConverse_of_rubinBasisGeneratorSeparation

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse
