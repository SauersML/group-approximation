import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketLabelBasic
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket: the label of one pocket dart

Lane `gl-p07-08` (`lanes/carto-gl-p07.md`), Osin, arXiv:math/0411039v3, §9, proof of
Lemma 9.7(b).  Certifies no printed sentence on its own.

Notation: `M = X.toCombMap`, `K` the pocket walk
`s_b ++ invDarts(A_i G₁ B_i) ++ s_a ++ invDarts(B_j G₂ A_j)` with `s_b = b.sideFrom j`,
`s_a = a.sideFrom i`, `A_k = a.cellArcList k`, `B_k = b.cellArcList k`, and
`Q₀ d := walkKeep K d ∨ walkKeep ∂a d ∨ walkKeep ∂b d`.

## `pocket_faceOf` (the part of lane 03 used here)

A face in the `Q₀`-class of a face `o` with `o ∈ sideFaces K`, `o ∉ a`, `o ∉ b` has the same three
properties.  Face moves keep the face.  A crossing at a dart `z` with `¬ Q₀ z` crosses an edge off
`K`, off `∂a` and off `∂b`; for each of the three face sets `sideFaces K`, `a`, `b` the walk or cycle
is exactly its set of boundary darts (`isBoundaryDart_sideFaces_iff`, `cycle_mem_iff`), so the
crossing does not change membership (`faceOf_alpha_mem_iff_of_not_walkKeep`).

## `label_of_pocket`

Let `d` satisfy `Q₀ d` with `f = faceOf d ∈ sideFaces K`, `f ∉ a`, `f ∉ b`.
* `α d ∉ K`: otherwise `α d` is a boundary dart of `sideFaces K`, so `faceOf d ∉ sideFaces K`.
* `d ∈ ∂a` or `d ∈ ∂b`: then `f ∈ a` or `f ∈ b`; impossible.
* `d ∈ K`.  On `s_b ⊆ ∂b` or `s_a ⊆ ∂a` the face is in `b` or `a`.  On `invDarts(A_i G₁ B_i)`,
  `α d ∈ A_i` gives `f = faceOf (α (α d)) ∈ a` and `α d ∈ B_i` gives `f ∈ b`; so `α d ∈ G₁`, that
  is `d ∈ invDarts G₁`.  The second arc gives `d ∈ invDarts G₂` the same way.
* `α d ∈ ∂a = invDarts A_i ++ s_a ++ invDarts A_j ++ a.sideFrom j`.  The first three pieces lie on
  `K` (`A_i` inside the first arc, `s_a` the second side, `A_j` inside the second arc), against
  `α d ∉ K`.  So `α d ∈ a.sideFrom j`.
* `α d ∈ ∂b = invDarts B_i ++ b.sideFrom i ++ invDarts B_j ++ s_b`: likewise `α d ∈ b.sideFrom i`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketLabel

universe u w v

open Embedded SimpleClosedWalkSides

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **Faces of the pocket class.**  A face in the `Q₀`-class of a face on the side of `K` and off
`a` and `b` is on the side of `K` and off `a` and `b`. -/
theorem pocket_faceOf {a b : RegionCandidate D eps X} {K : CellPocketWalk D eps X i j}
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk) {o : X.toCombMap.Face}
    (hoK : o ∈ sideFaces X.toCombMap K.walk) (hoa : o ∉ a.1) (hob : o ∉ b.1)
    {d : X.toCombMap.Dart}
    (hd : ∃ x, X.toCombMap.faceOf x = X.toCombMap.faceOf d ∧ ∃ y, X.toCombMap.faceOf y = o ∧
      Relation.EqvGen (CombMap.FaceClassStep X.toCombMap (fun z =>
        walkKeep X.toCombMap K.walk z ∨ walkKeep X.toCombMap a.2.boundary.cycle z ∨
          walkKeep X.toCombMap b.2.boundary.cycle z)) y x) :
    X.toCombMap.faceOf d ∈ sideFaces X.toCombMap K.walk ∧ X.toCombMap.faceOf d ∉ a.1 ∧
      X.toCombMap.faceOf d ∉ b.1 := by
  obtain ⟨x, hx, y, hy, hyx⟩ := hd
  subst hy
  have hK := faceClass_mem_iff hyx (sideFaces X.toCombMap K.walk) fun z hz =>
    faceOf_alpha_mem_iff_of_not_walkKeep (c := K.walk)
      (fun e => (hw.isBoundaryDart_sideFaces_iff X.planar e).symm) fun hk => hz (Or.inl hk)
  have ha := faceClass_mem_iff hyx a.1 fun z hz =>
    faceOf_alpha_mem_iff_of_not_walkKeep (c := a.2.boundary.cycle) a.2.boundary.cycle_mem_iff
      fun hk => hz (Or.inr (Or.inl hk))
  have hb := faceClass_mem_iff hyx b.1 fun z hz =>
    faceOf_alpha_mem_iff_of_not_walkKeep (c := b.2.boundary.cycle) b.2.boundary.cycle_mem_iff
      fun hk => hz (Or.inr (Or.inr hk))
  rw [hx] at hK ha hb
  exact ⟨hK.mp hoK, fun h => hoa (ha.mpr h), fun h => hob (hb.mpr h)⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketLabel.pocket_faceOf

/-- **The label of a pocket dart.**  A dart on an edge of `K`, `∂a` or `∂b`, based on the side of
`K` and off `a` and `b`, is on a gap `invDarts G₁`, `invDarts G₂`, or reverses a far side. -/
theorem label_of_pocket {a b : RegionCandidate D eps X} {K : CellPocketWalk D eps X i j}
    (hij : i ≠ j) (hai : a.JoinsCells i j) (hbi : b.JoinsCells i j)
    (hfirst : K.firstSide = b.sideFrom j) (hsecond : K.secondSide = a.sideFrom i)
    {G₁ : CyclicArc (cellDarts X i)}
    (h₁ : K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    {G₂ : CyclicArc (cellDarts X j)}
    (h₂ : K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j)
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk) {d : X.toCombMap.Dart}
    (hQ : walkKeep X.toCombMap K.walk d ∨ walkKeep X.toCombMap a.2.boundary.cycle d ∨
      walkKeep X.toCombMap b.2.boundary.cycle d)
    (hK : X.toCombMap.faceOf d ∈ sideFaces X.toCombMap K.walk) (ha : X.toCombMap.faceOf d ∉ a.1)
    (hb : X.toCombMap.faceOf d ∉ b.1) :
    d ∈ invDarts X G₁.darts ∨ d ∈ invDarts X G₂.darts ∨
      X.toCombMap.alpha d ∈ a.sideFrom j ∨ X.toCombMap.alpha d ∈ b.sideFrom i := by
  have hαK : X.toCombMap.alpha d ∉ K.walk := by
    intro h
    have h' := And.right ((hw.isBoundaryDart_sideFaces_iff X.planar _).mpr h)
    rw [X.toCombMap.alpha_involutive d] at h'
    exact h' hK
  have hsub₁ : ∀ e, X.toCombMap.alpha e ∈ K.firstArc.darts → e ∈ K.walk := fun e he =>
    (mem_walk_iff K e).mpr (Or.inr (Or.inl (mem_invDarts_of_alpha_mem he)))
  have hsub₂ : ∀ e, X.toCombMap.alpha e ∈ K.secondArc.darts → e ∈ K.walk := fun e he =>
    (mem_walk_iff K e).mpr (Or.inr (Or.inr (Or.inr (mem_invDarts_of_alpha_mem he))))
  have hnota : X.toCombMap.alpha d ∉ a.cellArcList i ∧ X.toCombMap.alpha d ∉ a.cellArcList j := by
    refine ⟨fun h => ha ?_, fun h => ha ?_⟩
    · have h' := RegionCandidate.faceOf_alpha_mem_of_mem_cellArcList hai h
      rwa [X.toCombMap.alpha_involutive d] at h'
    · have h' := RegionCandidate.faceOf_alpha_mem_of_mem_cellArcList hai h
      rwa [X.toCombMap.alpha_involutive d] at h'
  have hnotb : X.toCombMap.alpha d ∉ b.cellArcList i ∧ X.toCombMap.alpha d ∉ b.cellArcList j := by
    refine ⟨fun h => hb ?_, fun h => hb ?_⟩
    · have h' := RegionCandidate.faceOf_alpha_mem_of_mem_cellArcList hbi h
      rwa [X.toCombMap.alpha_involutive d] at h'
    · have h' := RegionCandidate.faceOf_alpha_mem_of_mem_cellArcList hbi h
      rwa [X.toCombMap.alpha_involutive d] at h'
  rcases hQ with (hd | hd) | (hd | hd) | (hd | hd)
  · rcases (mem_walk_iff K d).mp hd with hd | hd | hd | hd
    · rw [hfirst] at hd
      exact absurd (faceOf_mem_of_mem_boundary_cycle b
        ((mem_boundary_cycle_iff hij hbi d).mpr (Or.inr (Or.inr (Or.inr hd))))) hb
    · have hα := alpha_mem_of_mem_invDarts hd
      rw [h₁] at hα
      rcases List.mem_append.mp hα with hα | hα
      · rcases List.mem_append.mp hα with hα | hα
        · exact absurd hα hnota.1
        · exact Or.inl (mem_invDarts_of_alpha_mem hα)
      · exact absurd hα hnotb.1
    · rw [hsecond] at hd
      exact absurd (faceOf_mem_of_mem_boundary_cycle a
        ((mem_boundary_cycle_iff hij hai d).mpr (Or.inr (Or.inl hd)))) ha
    · have hα := alpha_mem_of_mem_invDarts hd
      rw [h₂] at hα
      rcases List.mem_append.mp hα with hα | hα
      · rcases List.mem_append.mp hα with hα | hα
        · exact absurd hα hnotb.2
        · exact Or.inr (Or.inl (mem_invDarts_of_alpha_mem hα))
      · exact absurd hα hnota.2
  · exact absurd hd hαK
  · exact absurd (faceOf_mem_of_mem_boundary_cycle a hd) ha
  · rcases (mem_boundary_cycle_iff hij hai _).mp hd with hd | hd | hd | hd
    · refine absurd (hsub₁ _ ?_) hαK
      rw [h₁]
      exact List.mem_append_left _ (List.mem_append_left _ (alpha_mem_of_mem_invDarts hd))
    · rw [← hsecond] at hd
      exact absurd ((mem_walk_iff K _).mpr (Or.inr (Or.inr (Or.inl hd)))) hαK
    · refine absurd (hsub₂ _ ?_) hαK
      rw [h₂]
      exact List.mem_append_right _ (alpha_mem_of_mem_invDarts hd)
    · exact Or.inr (Or.inr (Or.inl hd))
  · exact absurd (faceOf_mem_of_mem_boundary_cycle b hd) hb
  · rcases (mem_boundary_cycle_iff hij hbi _).mp hd with hd | hd | hd | hd
    · refine absurd (hsub₁ _ ?_) hαK
      rw [h₁]
      exact List.mem_append_right _ (alpha_mem_of_mem_invDarts hd)
    · exact Or.inr (Or.inr (Or.inr hd))
    · refine absurd (hsub₂ _ ?_) hαK
      rw [h₂]
      exact List.mem_append_left _ (List.mem_append_left _ (alpha_mem_of_mem_invDarts hd))
    · rw [← hfirst] at hd
      exact absurd ((mem_walk_iff K _).mpr (Or.inl hd)) hαK

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketLabel.label_of_pocket

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketLabel
