import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessPlanarOrbit
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-23: the successor outside walk of a connected face set

See the module docstring of `FourPieceWitnessPlanarOrbit.lean` for the statement and the proof.
Hypothesis (A) is `hA`, and hypothesis (B) is `hB`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open SimpleClosedWalkSides

namespace FourPieceWitness

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **The successor outside walk of a face set** whose complement is connected through edges
(`hA`) and whose boundary map is connected (`hB`).  It has no bridges. -/
theorem exists_enclosedFaceSetSucc_of_connected {X : DiscDiagram.{u, w, v} W}
    {F : Finset X.toCombMap.Face} (hout : X.outerFace ∉ F) (hne : F.Nonempty)
    (hA : ∀ f, f ∉ F →
      f ∈ PocketNoncrossing.faceClass X.toCombMap (boundaryKeep X.toCombMap F) X.outerFace)
    (hB : (PocketOrbit.keepMap X.toCombMap (boundaryKeep X.toCombMap F)
      (boundaryKeep_alpha X.toCombMap F)).IsConnected) :
    ∃ outerWalk : List X.toCombMap.Dart, EnclosedFaceSetSucc X F outerWalk ∧
      ∀ d ∈ outerWalk, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ F := by
  obtain ⟨d₀, hd₀⟩ := exists_boundaryKeep (X.toCombMap.connected_of_planar X.planar) hout hne
  obtain ⟨L, hL, hnext⟩ := PocketOrbit.exists_pocketOrbit_of_connected
    (boundaryKeep_alpha X.toCombMap F) X.planar hB hd₀ X.outerFace
  have hcls : ∀ d, X.toCombMap.faceOf d ∈
      PocketNoncrossing.faceClass X.toCombMap (boundaryKeep X.toCombMap F) X.outerFace ↔
      X.toCombMap.faceOf d ∉ F :=
    fun d => ⟨not_mem_of_mem_faceClass_boundaryKeep hout, hA _⟩
  have hmem : ∀ d, d ∈ L ↔
      X.toCombMap.faceOf d ∉ F ∧ X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ F := by
    intro d
    rw [hL.mem_iff d, hcls d]
    constructor
    · rintro ⟨hk, hd⟩
      refine ⟨hd, ?_⟩
      by_contra hα
      exact hd (hk.mpr hα)
    · rintro ⟨hd, hα⟩
      exact ⟨⟨fun h => absurd h hd, fun h => absurd hα h⟩, hd⟩
  have hwk : ∀ x, walkKeep X.toCombMap L x ↔ boundaryKeep X.toCombMap F x := by
    intro x
    refine ⟨PocketNoncrossing.keep_of_walkKeep (boundaryKeep_alpha X.toCombMap F) hL.mem_iff x,
      fun hk => ?_⟩
    by_cases hx : X.toCombMap.faceOf x ∈ F
    · refine Or.inr ((hmem _).mpr ⟨hk.mp hx, ?_⟩)
      rw [X.toCombMap.alpha_involutive x]
      exact hx
    · refine Or.inl ((hmem x).mpr ⟨hx, ?_⟩)
      by_contra hα
      exact hx (hk.mpr hα)
  refine ⟨L,
    { outerFace_not_mem := hout
      ne_nil := hL.ne_nil
      nodup := hL.nodup
      chain := hL.chain
      closes := hL.closes
      mem_iff := fun d => ⟨fun hd => ⟨((hmem d).mp hd).1, Or.inl ((hmem d).mp hd).2⟩, ?_⟩
      turn_mem := fun d hd m hm hk hfirst =>
        hL.turn d hd m hm ((hwk _).mp hk) fun k hk₀ hkm hkk => hfirst k hk₀ hkm ((hwk _).mpr hkk)
      turn_next := fun i hi m hm hk hfirst =>
        hnext i hi m hm ((hwk _).mp hk) fun k hk₀ hkm hkk =>
          hfirst k hk₀ hkm ((hwk _).mpr hkk) },
    fun d hd => ((hmem d).mp hd).2⟩
  rintro ⟨hd, hα | hα⟩
  · exact (hmem d).mpr ⟨hd, hα⟩
  · have h₂ := ((hmem _).mp hα).2
    rw [X.toCombMap.alpha_involutive d] at h₂
    exact absurd h₂ hd

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.exists_enclosedFaceSetSucc_of_connected

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
