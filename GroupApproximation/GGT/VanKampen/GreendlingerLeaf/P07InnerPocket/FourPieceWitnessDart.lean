import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessDef
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSucc
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-21a: the per-dart clause for the cut-down witness

This module proves clause 2 of `PocketFourPieceInputProofResidualStatement`
(`FourPieceInputProofStatement.lean`) for `FourPieceWitness.witnessFaces`
(`FourPieceWitnessDef.lean`).  The context is Osin, arXiv:math/0411039v3, §9, proof of Lemma
9.7(b).  Write `F` for the witness, `P` for the blocking set and `f = faceOf (α d)`,
`g = faceOf d` for a dart `d` with `g ∉ F` and `f ∈ F`.

## Proof route

1. `not_mem_left_of_mem_witnessFaces`: let `f ∈ F ∩ a.1`.  If `f` is in the `Q₀`-class of `c`, this
   contradicts `PocketClass.not_mem_left_of_mem_pocketClass`.  Otherwise `f ∉ P`, since `f` is on
   the side of `K`.  Then `f` lies in its own piece (`self_mem_component`), so `f` is cut, a
   contradiction.  The right version is the same.
2. `pocketKeep_alpha_of_boundary`, by cases on `g`.
   * `g ∉ sideFaces K`: `α d` is a boundary dart of `sideFaces K`, so it is on `K`
     (`isBoundaryDart_sideFaces_iff`).
   * `g` is cut, in the piece of `h`: `g ∉ P` (`not_mem_of_mem_component`).  If `f ∉ P`, then the
     edge of `d` can be crossed (`eqvGen_alpha`), so `f` is in the piece of `h` and is cut, a
     contradiction.  So `f ∈ P`, and `f` is in the `Q₀`-class.  If `α d` were not kept, then `g`
     would be in the class too (`faceOf_alpha_mem_faceClass`), hence in `P`, a contradiction.
   * `g` is open: `g` shares the edge of `d` with `f`, so it is reached by one more step and lies
     in `F`, a contradiction.
3. `dart_clause`: collect clause 1, step 1 and step 2 for a walk without bridges.  A walk dart has
   `g ∉ F` by `mem_iff`, and `f ∈ F` by hypothesis.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- A face on the side of `K` and off the `Q₀`-class of `c` is off the blocking set. -/
theorem not_mem_block_of_not_mem_keepClass {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {c f : X.toCombMap.Face}
    (hfs : f ∈ sideFaces X.toCombMap K.walk) (hfk : f ∉ keepClass a b K c) :
    f ∉ block a b K c := by
  intro hP
  rcases mem_block_iff.mp hP with hk | ho
  · exact hfk hk
  · exact (SimpleClosedWalkSides.mem_sideOutside_iff X.toCombMap K.walk f).mp ho hfs

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.not_mem_block_of_not_mem_keepClass

/-- **A witness face is off `a`.** -/
theorem not_mem_left_of_mem_witnessFaces {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {c f : X.toCombMap.Face} (hca : c ∉ a.1)
    (hf : f ∈ witnessFaces a b K c) : f ∉ a.1 := by
  intro hfa
  obtain ⟨⟨hfs, hfcut⟩, _⟩ := mem_witnessFaces_iff.mp hf
  by_cases hfk : f ∈ keepClass a b K c
  · exact PocketClass.not_mem_left_of_mem_pocketClass hca (PocketClass.mem_pocketClass_iff.mpr
      ((PocketNoncrossing.mem_faceClass_iff X.toCombMap (PocketClass.pocketKeep a b K) c f).mp
        hfk)) hfa
  · exact hfcut (mem_cut_iff.mpr ⟨f, Or.inl hfa, not_mem_block_of_not_mem_keepClass hfs hfk,
      ExteriorComponent.self_mem_component f⟩)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.not_mem_left_of_mem_witnessFaces

/-- **A witness face is off `b`.** -/
theorem not_mem_right_of_mem_witnessFaces {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {c f : X.toCombMap.Face} (hcb : c ∉ b.1)
    (hf : f ∈ witnessFaces a b K c) : f ∉ b.1 := by
  intro hfb
  obtain ⟨⟨hfs, hfcut⟩, _⟩ := mem_witnessFaces_iff.mp hf
  by_cases hfk : f ∈ keepClass a b K c
  · exact PocketClass.not_mem_right_of_mem_pocketClass hcb (PocketClass.mem_pocketClass_iff.mpr
      ((PocketNoncrossing.mem_faceClass_iff X.toCombMap (PocketClass.pocketKeep a b K) c f).mp
        hfk)) hfb
  · exact hfcut (mem_cut_iff.mpr ⟨f, Or.inr hfb, not_mem_block_of_not_mem_keepClass hfs hfk,
      ExteriorComponent.self_mem_component f⟩)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.not_mem_right_of_mem_witnessFaces

/-- **The inside dart of a boundary edge of the witness is kept.** -/
theorem pocketKeep_alpha_of_boundary {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {c : X.toCombMap.Face}
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk) {d : X.toCombMap.Dart}
    (hd : X.toCombMap.faceOf d ∉ witnessFaces a b K c)
    (hαd : X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ witnessFaces a b K c) :
    PocketClass.pocketKeep a b K (X.toCombMap.alpha d) := by
  obtain ⟨⟨hfs, hfcut⟩, hreach⟩ := mem_witnessFaces_iff.mp hαd
  by_cases hgs : X.toCombMap.faceOf d ∈ sideFaces X.toCombMap K.walk
  · by_cases hgcut : X.toCombMap.faceOf d ∈ cut a b K c
    · obtain ⟨h, hab, hh, hg⟩ := mem_cut_iff.mp hgcut
      have hgP : X.toCombMap.faceOf d ∉ block a b K c :=
        ExteriorComponent.not_mem_of_mem_component hh hg
      have hfP : X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ block a b K c := by
        by_contra hfP
        obtain ⟨y, hy, hreachy⟩ := ExteriorComponent.mem_component_iff.mp hg
        obtain ⟨x, hx, hxd⟩ := ExteriorComponent.Reach.of_faceOf_eq hreachy hy
        exact hfcut (mem_cut_iff.mpr ⟨h, hab, hh, ExteriorComponent.mem_component_iff.mpr
          ⟨X.toCombMap.alpha d, rfl, x, hx,
            Relation.EqvGen.trans _ _ _ hxd (P07InnerPocket.eqvGen_alpha hgP hfP)⟩⟩)
      have hfk : X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ keepClass a b K c := by
        rcases mem_block_iff.mp hfP with hk | ho
        · exact hk
        · exact absurd hfs ((SimpleClosedWalkSides.mem_sideOutside_iff X.toCombMap K.walk _).mp ho)
      by_contra hk
      have hgk := PocketNoncrossing.faceOf_alpha_mem_faceClass X.toCombMap
        (PocketClass.pocketKeep a b K) c hk hfk
      rw [X.toCombMap.alpha_involutive d] at hgk
      exact hgP (mem_block_iff.mpr (Or.inl hgk))
    · exact (hd (mem_witnessFaces_iff.mpr ⟨⟨hgs, hgcut⟩, Relation.ReflTransGen.tail hreach
        ⟨⟨hfs, hfcut⟩, ⟨hgs, hgcut⟩,
          Or.inl ⟨X.toCombMap.alpha d, rfl, by rw [X.toCombMap.alpha_involutive d]⟩⟩⟩)).elim
  · have hB : X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ sideFaces X.toCombMap K.walk ∧
        X.toCombMap.faceOf (X.toCombMap.alpha (X.toCombMap.alpha d)) ∉
          sideFaces X.toCombMap K.walk := by
      rw [X.toCombMap.alpha_involutive d]
      exact ⟨hfs, hgs⟩
    exact Or.inl (Or.inl ((hw.isBoundaryDart_sideFaces_iff X.planar (X.toCombMap.alpha d)).mp hB))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.pocketKeep_alpha_of_boundary

/-- **Clause 2 of the residual** for an outside walk of the witness without bridges. -/
theorem dart_clause {a b : RegionCandidate D eps X} {K : CellPocketWalk D eps X i j}
    {c : X.toCombMap.Face} (hw : IsNoncrossingClosedWalk X.toCombMap K.walk) (hca : c ∉ a.1)
    (hcb : c ∉ b.1) {outerWalk : List X.toCombMap.Dart}
    (E : EnclosedFaceSetSucc X (witnessFaces a b K c) outerWalk)
    (hnb : ∀ d ∈ outerWalk, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ witnessFaces a b K c) :
    ∀ d ∈ outerWalk,
      X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ sideFaces X.toCombMap K.walk ∧
        X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ a.1 ∧
        X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ b.1 ∧
        (walkKeep X.toCombMap K.walk (X.toCombMap.alpha d) ∨
          walkKeep X.toCombMap a.2.boundary.cycle (X.toCombMap.alpha d) ∨
          walkKeep X.toCombMap b.2.boundary.cycle (X.toCombMap.alpha d)) := by
  intro d hd
  have hf := hnb d hd
  have hg : X.toCombMap.faceOf d ∉ witnessFaces a b K c := ((E.mem_iff d).mp hd).1
  exact ⟨witnessFaces_subset_sideFaces hf, not_mem_left_of_mem_witnessFaces hca hf,
    not_mem_right_of_mem_witnessFaces hcb hf, pocketKeep_alpha_of_boundary hw hg hf⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.dart_clause

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
