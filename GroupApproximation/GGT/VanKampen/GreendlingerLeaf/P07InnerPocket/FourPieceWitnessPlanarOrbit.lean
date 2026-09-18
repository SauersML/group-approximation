import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketOrbitWalk
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSucc
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-23: the outside walk of a face set from connectivity

This module is generic infrastructure for the planar part of lane gl-p07-21a
(`FourPieceWitnessStatement.lean`), from Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).
It certifies no printed sentence on its own.

## Statement

Take a disc diagram `X` and a face set `F` with `o ∉ F` and `F` nonempty.  The boundary edges of
`F` are `boundaryKeep M F`: the two faces of the edge lie on different sides of `F`.  Assume:
* **(A)** every face off `F` is in the class of `o` for `boundaryKeep M F`, i.e. the complement of
  `F` is connected through edges;
* **(B)** the map on the boundary edges of `F` is connected.

Then `F` has an outside walk that turns to its successor, and has no bridges
(`exists_enclosedFaceSetSucc_of_connected`).

## The proof

`PocketOrbit.exists_pocketOrbit_of_connected` for `keep = boundaryKeep M F` and `c = o` gives `L`.
* The class of `o` is the complement of `F`: crossing an edge that is not kept preserves
  membership in `F` (`not_mem_of_mem_faceClass_boundaryKeep`), and (A) gives the other inclusion.
* So `d ∈ L ↔ faceOf d ∉ F ∧ faceOf (α d) ∈ F`.  This is `mem_iff`, and it gives no bridges.
* `walkKeep M L x ↔ boundaryKeep M F x`, so the orbit's turn clauses are `turn_mem` and
  `turn_next`.
* A kept dart exists because `M` is connected and `F` separates `o` from a face of `F`
  (`exists_boundaryKeep`).

**Orientation.**  `EnclosedFaceSet.mem_iff` puts the own face of a walk dart outside the face set.
Its reverse face is inside, or the reverse dart is on the walk (a bridge).  The walk built here
has `faceOf (α d) ∈ F` for every walk dart, so it has no bridges.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open SimpleClosedWalkSides

namespace FourPieceWitness

/-- **The boundary edges of a face set**: the two faces of the edge lie on different sides. -/
def boundaryKeep (M : CombMap.{v}) (F : Finset M.Face) (d : M.Dart) : Prop :=
  (M.faceOf d ∈ F ↔ M.faceOf (M.alpha d) ∉ F)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.boundaryKeep

theorem boundaryKeep_alpha (M : CombMap.{v}) (F : Finset M.Face) (d : M.Dart) :
    boundaryKeep M F (M.alpha d) ↔ boundaryKeep M F d := by
  unfold boundaryKeep
  rw [M.alpha_involutive d]
  tauto

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.boundaryKeep_alpha

/-- **The class of a face off `F` stays off `F`.** -/
theorem not_mem_of_mem_faceClass_boundaryKeep {M : CombMap.{v}} {F : Finset M.Face}
    {c f : M.Face} (hc : c ∉ F) (hf : f ∈ PocketNoncrossing.faceClass M (boundaryKeep M F) c) :
    f ∉ F := by
  obtain ⟨x, rfl, y, rfl, h⟩ :=
    (PocketNoncrossing.mem_faceClass_iff M (boundaryKeep M F) c f).mp hf
  have hQ := PocketNoncrossing.invariant_of_eqvGen M (fun z => M.faceOf z ∈ F)
    (keep := boundaryKeep M F)
    (fun z => by
      show M.faceOf (M.facePerm z) ∈ F ↔ M.faceOf z ∈ F
      rw [M.faceOf_facePerm])
    (fun z hz => by
      show M.faceOf (M.alpha z) ∈ F ↔ M.faceOf z ∈ F
      unfold boundaryKeep at hz
      tauto) h
  exact fun hx => hc (hQ.mpr hx)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.not_mem_of_mem_faceClass_boundaryKeep

/-- **A boundary edge exists** when a connected map has a face off `F` and a face in `F`. -/
theorem exists_boundaryKeep {M : CombMap.{v}} (hM : M.IsConnected) {F : Finset M.Face}
    {c : M.Face} (hc : c ∉ F) (hne : F.Nonempty) : ∃ d, boundaryKeep M F d := by
  by_contra hE
  have hiff : ∀ x, M.faceOf (M.alpha x) ∈ F ↔ M.faceOf x ∈ F := by
    intro x
    have hx : ¬ boundaryKeep M F x := fun h => hE ⟨x, h⟩
    unfold boundaryKeep at hx
    tauto
  have hstep : ∀ x y, M.Adjacent x y → (M.faceOf x ∈ F ↔ M.faceOf y ∈ F) := by
    rintro x y (rfl | rfl)
    · exact (hiff x).symm
    · have hsig : M.sigma x = M.facePerm (M.alpha x) := by
        show M.sigma x = M.sigma (M.alpha (M.alpha x))
        rw [M.alpha_involutive x]
      rw [hsig, M.faceOf_facePerm]
      exact (hiff x).symm
  have hall : ∀ x y, Relation.EqvGen M.Adjacent x y → (M.faceOf x ∈ F ↔ M.faceOf y ∈ F) := by
    intro x y h
    induction h with
    | rel a b hab => exact hstep a b hab
    | refl _ => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  obtain ⟨f, hf⟩ := hne
  obtain ⟨x₀, hx₀⟩ := Quotient.exists_rep c
  obtain ⟨y₀, hy₀⟩ := Quotient.exists_rep f
  have hc₀ : M.faceOf x₀ = c := hx₀
  have hf₀ : M.faceOf y₀ = f := hy₀
  have h₁ : M.faceOf y₀ ∈ F := by
    rw [hf₀]
    exact hf
  have h₂ := (hall x₀ y₀ (hM x₀ y₀)).mpr h₁
  rw [hc₀] at h₂
  exact hc h₂

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.exists_boundaryKeep

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
