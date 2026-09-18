import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFillArc
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketCellOffComponent
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane `PocketCellOff`: the exterior reaches a cell through a region

Lane gl-p07-07.  Take a face set `P` inside the side faces of the pocket walk `K`, off the regions
`a`, `b` and off the cells `Π_i`, `Π_j`.  Write `C = component P o` for the piece of the outer face.

* `mem_component_of_alpha_mem_boundary`: say the region `a` joins `Π_i` to `Π_j`, misses `P`, and
  has a nonempty arc on `Π_i`.  If `C` holds a face whose dart reverses a boundary dart of `a`,
  then `C` holds `Π_i`.
  * Cross that edge into `a`, whose faces are off `P`.
  * Walk along the boundary cycle of `a` to the reverse of an arc dart of `Π_i`
    (`eqvGen_of_mem_boundary_cycle`), then cross back into `Π_i`, which is off `P`.
* `pocketCellOff_nondegenerate`: the piece of the exterior for the side faces holds a face whose
  dart reverses a dart of `K` (`exists_alpha_mem_component`).  The piece for `P` is larger
  (`component_mono`).  Split on that dart.
  * On a side `s_1 = sideFrom b j` or `s_2 = sideFrom a i`, the step above gives `Π_i`.  This uses
    the nonempty arcs of `a`, `b` on `Π_i`.
  * On an arc `t_1` or `t_2`, the face is `Π_i` or `Π_j` itself.
* `not_mem_absorbed_of_alpha_mem_invDarts`: a face of `C` whose dart reverses a dart of `Π_k` has
  that dart on `Π_k`.  So `Π_k` lies in `C` and not in `absorbed P o`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded SimpleClosedWalkSides Surgery.MapCollapse Surgery.MapCollapse.ExteriorComponent

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **The piece reaches `Π_i` through a region joining `Π_i` to `Π_j`.** -/
theorem mem_component_of_alpha_mem_boundary {a : RegionCandidate D eps X} (hij : i ≠ j)
    (hai : a.JoinsCells i j) {P : Finset X.toCombMap.Face} {o : X.toCombMap.Face} (ho : o ∉ P)
    (haP : ∀ f ∈ a.1, f ∉ P) (hiP : (cell X i).face ∉ P) (hpos : 0 < (a.cellArcList i).length)
    {d : X.toCombMap.Dart} (hd : X.toCombMap.alpha d ∈ a.2.boundary.cycle)
    (hc : X.toCombMap.faceOf d ∈ component X.toCombMap P o) :
    (cell X i).face ∈ component X.toCombMap P o := by
  obtain ⟨e, he⟩ := List.exists_mem_of_length_pos hpos
  obtain ⟨A, hA⟩ := RegionCandidate.exists_cellArc a hai.source_or_target_left
  have hef : X.toCombMap.faceOf e = (cell X i).face :=
    P07LakeExclusion.LakeFill.arcFaceOf_eq A (by rw [hA]; exact he)
  obtain ⟨n, hn⟩ := RegionCandidate.boundary_cycle_rotate_of_joinsCells hij hai
  have hαe : X.toCombMap.alpha e ∈ a.2.boundary.cycle := by
    have hmem : X.toCombMap.alpha e ∈ a.2.boundary.cycle.rotate n := by
      rw [hn]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map_of_mem (List.mem_reverse.mpr he))))
    exact List.mem_rotate.mp hmem
  obtain ⟨y, hy, hry⟩ := mem_component_iff.mp hc
  obtain ⟨x₁, hx₁, h₁⟩ := ExteriorComponent.Reach.of_faceOf_eq hry hy
  refine mem_component_iff.mpr ⟨e, hef, x₁, hx₁, ?_⟩
  have hdP : X.toCombMap.faceOf d ∉ P := not_mem_of_mem_component ho hc
  have hαd : X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ P :=
    haP _ ((a.2.boundary.cycle_mem_iff _).mp hd).1
  have hαe' : X.toCombMap.faceOf (X.toCombMap.alpha e) ∉ P :=
    haP _ ((a.2.boundary.cycle_mem_iff _).mp hαe).1
  have heP : X.toCombMap.faceOf e ∉ P := by
    rw [hef]
    exact hiP
  exact Relation.EqvGen.trans _ _ _ h₁
    (Relation.EqvGen.trans _ _ _ (eqvGen_alpha hdP hαd)
      (Relation.EqvGen.trans _ _ _ (eqvGen_of_mem_boundary_cycle a.2.boundary haP hd hαe)
        (Relation.EqvGen.symm _ _ (eqvGen_alpha heP hαe'))))

/-- **With nonempty contact arcs on `Π_i`, the exterior piece of the pocket reaches `Π_i` or
`Π_j`.** -/
theorem pocketCellOff_nondegenerate {a b : RegionCandidate D eps X}
    (K : CellPocketWalk D eps X i j) (hij : i ≠ j) (hai : a.JoinsCells i j)
    (hbi : b.JoinsCells i j) (hfirst : K.firstSide = b.sideFrom j)
    (hsecond : K.secondSide = a.sideFrom i) (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk) {P : Finset X.toCombMap.Face}
    (hP : ∀ f ∈ P, f ∈ sideFaces X.toCombMap K.walk ∧ f ∉ a.1 ∧ f ∉ b.1 ∧
      f ≠ (cell X i).face ∧ f ≠ (cell X j).face)
    (hapos : 0 < (a.cellArcList i).length) (hbpos : 0 < (b.cellArcList i).length) :
    (cell X i).face ∈ component X.toCombMap P X.outerFace ∨
      (cell X j).face ∈ component X.toCombMap P X.outerFace := by
  have hPQ : P ⊆ sideFaces X.toCombMap K.walk := fun f hf => (hP f hf).1
  have ho : X.outerFace ∉ P := fun h => hout (hPQ h)
  have hiP : (cell X i).face ∉ P := fun h => (hP _ h).2.2.2.1 rfl
  have haP : ∀ f ∈ a.1, f ∉ P := fun f hf h => (hP f h).2.1 hf
  have hbP : ∀ f ∈ b.1, f ∉ P := fun f hf h => (hP f h).2.2.1 hf
  obtain ⟨d, hαd, hc⟩ := P07LakeExclusion.LakeFill.exists_alpha_mem_component hw X.planar hout
  have hcP : X.toCombMap.faceOf d ∈ component X.toCombMap P X.outerFace :=
    component_mono hPQ hout hc
  rcases (P07LakeExclusion.LakeFill.pocketWalk_mem_iff K _).mp hαd with
    hs | ⟨x, hx, hxd⟩ | hs | ⟨x, hx, hxd⟩
  · rw [hfirst] at hs
    obtain ⟨n, hn⟩ := RegionCandidate.boundary_cycle_rotate_of_joinsCells hij hbi
    have hmem : X.toCombMap.alpha d ∈ b.2.boundary.cycle.rotate n := by
      rw [hn]
      exact List.mem_append_right _ hs
    exact Or.inl (mem_component_of_alpha_mem_boundary hij hbi ho hbP hiP hbpos
      (List.mem_rotate.mp hmem) hcP)
  · have hdx : d = x := (X.toCombMap.alpha.injective hxd).symm
    rw [hdx] at hcP
    left
    rw [← P07LakeExclusion.LakeFill.arcFaceOf_eq K.firstArc hx]
    exact hcP
  · rw [hsecond] at hs
    obtain ⟨n, hn⟩ := RegionCandidate.boundary_cycle_rotate_of_joinsCells hij hai
    have hmem : X.toCombMap.alpha d ∈ a.2.boundary.cycle.rotate n := by
      rw [hn]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hs))
    exact Or.inl (mem_component_of_alpha_mem_boundary hij hai ho haP hiP hapos
      (List.mem_rotate.mp hmem) hcP)
  · have hdx : d = x := (X.toCombMap.alpha.injective hxd).symm
    rw [hdx] at hcP
    right
    rw [← P07LakeExclusion.LakeFill.arcFaceOf_eq K.secondArc hx]
    exact hcP

/-- **A cell reversed by a dart of the exterior piece is not absorbed.** -/
theorem not_mem_absorbed_of_alpha_mem_invDarts {P : Finset X.toCombMap.Face}
    {o : X.toCombMap.Face} {k : Fin X.rCellCount} {d : X.toCombMap.Dart}
    (hd : X.toCombMap.faceOf d ∈ component X.toCombMap P o)
    (hk : X.toCombMap.alpha d ∈ invDarts X (cellDarts X k)) :
    (cell X k).face ∉ absorbed X.toCombMap P o := by
  rw [mem_absorbed_iff, not_not]
  obtain ⟨e, he, hed⟩ := List.mem_map.mp hk
  have hde : d = e := X.toCombMap.alpha.injective hed.symm
  rw [hde] at hd
  rw [← ((X.faceBoundary (cell X k).face).mem_iff e).mp (List.mem_reverse.mp he)]
  exact hd

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.mem_component_of_alpha_mem_boundary
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pocketCellOff_nondegenerate
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.not_mem_absorbed_of_alpha_mem_invDarts
