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
point `x` and every open `W ∋ x`, SOME clopen `V` with `x ∈ V ⊆ W` and SOME generating sets
`G₁ ⊇`-generating `F_V`, `G₂`-generating `F_{Vᶜ}` have `Φ`-images with pairwise disjoint moved
sets.  TRUE (`rubinBasisGeneratorSeparation_of_rigidPolarBasisOpenTransport`). -/
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
