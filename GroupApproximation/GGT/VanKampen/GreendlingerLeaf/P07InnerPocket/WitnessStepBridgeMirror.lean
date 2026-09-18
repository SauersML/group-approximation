import GroupApproximation.GGT.VanKampen.PermOrbitTransport
import GroupApproximation.GGT.VanKampen.FaceCycle
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-61: the mirror of a combinatorial map

Lane gl-p07-61.  Certifies no printed sentence on its own.  NOT COMPILED.

The mirror of `M = (α, σ)` is `(α, σ⁻¹)`: the same darts with the opposite rotation.
* `witnessStepBridge_mirror_planar`: the mirror of a planar map is planar.  Edges are unchanged,
  vertices are `σ⁻¹`-orbits (`Perm.sameCycle_inv`), and the face permutation `σ⁻¹ α` is inverse to
  the `α`-conjugate of `σ α` (`witnessStepBridge_mirror_permCongr`).
* `witnessStepBridge_mirror_isFaceCycle`: if `L` is a face cycle of `M`, then `L.reverse.map α` is
  a face cycle of the mirror.  The mirror face permutation sends `α (σ α d)` to `α d`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u

namespace FourPieceWitness

/-- The orbits of the inverse of a permutation are its orbits. -/
noncomputable def witnessStepBridge_orbitInvEquiv {D : Type u} (p : Equiv.Perm D) :
    CombMap.Orbit p⁻¹ ≃ CombMap.Orbit p :=
  Quotient.congr (Equiv.refl D) fun x y =>
    Equiv.Perm.sameCycle_inv (f := p) (x := x) (y := y)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepBridge_orbitInvEquiv

/-- **The mirror** `(α, σ⁻¹)` of a combinatorial map. -/
def witnessStepBridge_mirror (M : CombMap.{u}) : CombMap.{u} where
  Dart := M.Dart
  dartFintype := M.dartFintype
  alpha := M.alpha
  sigma := M.sigma⁻¹
  alpha_involutive := M.alpha_involutive
  alpha_fixedPointFree := M.alpha_fixedPointFree

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepBridge_mirror

/-- Connectivity steps of a map are connectivity steps of its mirror. -/
theorem witnessStepBridge_mirror_reachable (M : CombMap.{u}) {d e : M.Dart}
    (h : Relation.EqvGen M.Adjacent d e) :
    Relation.EqvGen (witnessStepBridge_mirror M).Adjacent d e := by
  induction h with
  | rel d e h =>
      rcases h with h | h
      · exact Relation.EqvGen.rel _ _ (Or.inl h)
      · refine Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inr ?_))
        change M.sigma⁻¹ e = d
        rw [← h]
        exact Equiv.Perm.inv_eq_iff_eq.mpr rfl
  | refl d => exact Relation.EqvGen.refl _
  | symm d e _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans d e f _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepBridge_mirror_reachable

/-- The mirror of a connected map is connected. -/
theorem witnessStepBridge_mirror_connected (M : CombMap.{u}) (h : M.IsConnected) :
    (witnessStepBridge_mirror M).IsConnected :=
  fun d e => witnessStepBridge_mirror_reachable M (h d e)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepBridge_mirror_connected

/-- The mirror has the vertices of the map. -/
theorem witnessStepBridge_mirror_vertexCount (M : CombMap.{u}) :
    (witnessStepBridge_mirror M).vertexCount = M.vertexCount := by
  change Nat.card (CombMap.Orbit M.sigma⁻¹) = Nat.card (CombMap.Orbit M.sigma)
  exact Nat.card_congr (witnessStepBridge_orbitInvEquiv M.sigma)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepBridge_mirror_vertexCount

/-- The mirror has the edges of the map. -/
theorem witnessStepBridge_mirror_edgeCount (M : CombMap.{u}) :
    (witnessStepBridge_mirror M).edgeCount = M.edgeCount := rfl

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepBridge_mirror_edgeCount

/-- The `α`-conjugate of the face permutation is the inverse mirror face permutation. -/
theorem witnessStepBridge_mirror_permCongr (M : CombMap.{u}) :
    M.alpha.permCongr M.facePerm = (witnessStepBridge_mirror M).facePerm⁻¹ := by
  apply Equiv.ext
  intro x
  symm
  rw [Equiv.Perm.inv_eq_iff_eq]
  change x = M.sigma.symm (M.alpha (M.alpha (M.sigma (M.alpha (M.alpha.symm x)))))
  rw [Equiv.apply_symm_apply, M.alpha_involutive, Equiv.symm_apply_apply]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepBridge_mirror_permCongr

/-- The mirror has the faces of the map. -/
theorem witnessStepBridge_mirror_faceCount (M : CombMap.{u}) :
    (witnessStepBridge_mirror M).faceCount = M.faceCount := by
  change Nat.card (CombMap.Orbit (witnessStepBridge_mirror M).facePerm) =
    Nat.card (CombMap.Orbit M.facePerm)
  rw [Nat.card_congr (orbitPermCongr M.alpha M.facePerm), witnessStepBridge_mirror_permCongr M]
  exact (Nat.card_congr (witnessStepBridge_orbitInvEquiv _)).symm

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepBridge_mirror_faceCount

/-- The mirror has the Euler characteristic of the map. -/
theorem witnessStepBridge_mirror_euler (M : CombMap.{u}) :
    (witnessStepBridge_mirror M).eulerCharacteristic = M.eulerCharacteristic := by
  rw [CombMap.eulerCharacteristic, CombMap.eulerCharacteristic,
    witnessStepBridge_mirror_vertexCount, witnessStepBridge_mirror_edgeCount,
    witnessStepBridge_mirror_faceCount]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepBridge_mirror_euler

/-- **The mirror of a planar map is planar.** -/
theorem witnessStepBridge_mirror_planar (M : CombMap.{u}) (h : M.IsPlanar) :
    (witnessStepBridge_mirror M).IsPlanar :=
  ⟨witnessStepBridge_mirror_connected M h.1, (witnessStepBridge_mirror_euler M).trans h.2⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepBridge_mirror_planar

/-- The mirror face permutation undoes one face step of the map, read through `α`. -/
theorem witnessStepBridge_mirror_facePerm_alpha (M : CombMap.{u}) (d : M.Dart) :
    (witnessStepBridge_mirror M).facePerm (M.alpha (M.facePerm d)) = M.alpha d := by
  change M.sigma⁻¹ (M.alpha (M.alpha (M.sigma (M.alpha d)))) = M.alpha d
  rw [M.alpha_involutive]
  exact Equiv.Perm.inv_eq_iff_eq.mpr rfl

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepBridge_mirror_facePerm_alpha

/-- **A face cycle of a map, reversed and read through `α`, is a face cycle of its mirror.** -/
theorem witnessStepBridge_mirror_isFaceCycle (M : CombMap.{u}) {L : List M.Dart}
    (hL : M.IsFaceCycle L) :
    (witnessStepBridge_mirror M).IsFaceCycle (L.reverse.map M.alpha) := by
  have hne : L ≠ [] := hL.ne_nil
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hne
  · exact List.Nodup.map M.alpha.injective (List.nodup_reverse.mpr hL.nodup)
  · rw [List.isChain_map, List.isChain_reverse]
    refine List.IsChain.imp ?_ hL.chain
    intro a b hab
    subst hab
    exact witnessStepBridge_mirror_facePerm_alpha M a
  · simp only [List.getLast_map, List.getLast_reverse, List.head_map, List.head_reverse]
    rw [← hL.closes]
    exact witnessStepBridge_mirror_facePerm_alpha M _

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepBridge_mirror_isFaceCycle

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
