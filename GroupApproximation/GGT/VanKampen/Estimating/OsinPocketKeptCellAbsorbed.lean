import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketKeptCell
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionPieces
import GroupApproximation.Meta.AxiomGuard

/-!
# The regions meeting a pocket lie inside it

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(a): "otherwise one can include the
ε-contiguity subdiagrams corresponding to the edges `e` and `f` of `Φ'_M` into a single
ε-contiguity subdiagram in the obvious way, contrary to the definition of `M`."

`GloballyDistinguishedSectionFamily.exists_kept_of_pocketRegion` needs every selected region other
than `x` and `y` to avoid the pocket.  Here that premise is replaced by what the pocket walk gives:
its sides are the left side of `y` and the right side of `x`, and no relator word has value one.
Every selected region meeting the pocket lies inside it, and the collapse absorbs all of them.

* `Embedded.FaceSetBoundary.subset_or_disjoint`: a face set with a boundary cycle that no edge of
  it leaves `Q` across lies inside `Q` or misses it.  The boundary cycle keeps the part of the
  face set in `Q` edge-connected to the part outside, and planarity leaves no closed part.
* `RealizedRegionFamily.subset_of_not_disjoint_pocketRegion`, and the named proposition
  `PocketMeetsContainedStatement` with its proof `pocketMeetsContained`: a selected region meeting
  a pocket region whose cycle is the pocket walk lies inside it.  A dart of the region leaving the
  pocket lies on the walk.  On a side it lies on the boundary of `y` or `x`; on `t_1` it crosses
  into the cell `i`, whose word does not have value one; on `t_2` it crosses into the exterior.
* `GloballyDistinguishedSectionFamily.exists_kept_of_pocketRegion_of_value` and
  `exists_kept_of_simple_of_value`: the kept cell without `havoid`.  If the pocket held no relator
  cell, it would absorb the regions meeting it.  Their arc darts lie on `t_1` and `t_2`, so their
  weights add up to at most `|t_1| + |t_2|`.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, through Osin's Lemma 9.7); certifies no printed sentence
on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

namespace Embedded.FaceSetBoundary

variable {Delta : DiscDiagram.{u, w, v} W} {faces : Finset Delta.toCombMap.Face}

/-- **A face set on one side of `Q`.**  Let `faces` have a boundary cycle, and suppose no edge
with both sides in `faces` runs from a face in `Q` to a face outside `Q`.  Then `faces` lies
inside `Q` or misses it.  Along the boundary cycle membership in `Q` does not change.  The faces
on the other side have no boundary dart, so they are closed under the edge and vertex rotations
and hold every dart, the exterior included. -/
theorem subset_or_disjoint (B : FaceSetBoundary Delta faces) (Q : Finset Delta.toCombMap.Face)
    (hcross : ∀ d, Delta.toCombMap.faceOf d ∈ faces → Delta.toCombMap.faceOf d ∈ Q →
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ∈ faces →
        Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ∈ Q) :
    faces ⊆ Q ∨ Disjoint faces Q := by
  have hA : ∀ u, Delta.toCombMap.faceOf u ∈ faces →
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha u) ∈ faces →
        (Delta.toCombMap.faceOf u ∈ Q ↔
          Delta.toCombMap.faceOf (Delta.toCombMap.alpha u) ∈ Q) := by
    intro u hu ha
    refine ⟨fun hq => hcross u hu hq ha, fun hq => ?_⟩
    have h := hcross (Delta.toCombMap.alpha u) ha hq
    rw [Delta.toCombMap.alpha_involutive u] at h
    exact h hu
  have hmove : ∀ d e, Relation.ReflTransGen (InternalBoundaryMove Delta faces) d e →
      (Delta.toCombMap.faceOf d ∈ Q ↔ Delta.toCombMap.faceOf e ∈ Q) := by
    intro d e h
    induction h with
    | refl => exact Iff.rfl
    | tail _ hbc ih =>
      obtain ⟨hb, hab, rfl⟩ := hbc
      rw [Delta.toCombMap.faceOf_facePerm]
      exact ih.trans (hA _ hb hab)
  have hstep : ∀ d e, BoundaryStep Delta faces d e →
      (Delta.toCombMap.faceOf d ∈ Q ↔ Delta.toCombMap.faceOf e ∈ Q) := by
    intro d e h
    have h' := hmove _ _ h.2.2
    rwa [Delta.toCombMap.faceOf_facePerm] at h'
  obtain ⟨c, hcyc⟩ : ∃ c : Prop, ∀ u ∈ B.cycle, (Delta.toCombMap.faceOf u ∈ Q ↔ c) :=
    ⟨Delta.toCombMap.faceOf (B.cycle.head B.cycle_nonempty) ∈ Q,
      List.IsChain.induction
        (fun u => Delta.toCombMap.faceOf u ∈ Q ↔
          Delta.toCombMap.faceOf (B.cycle.head B.cycle_nonempty) ∈ Q)
        B.cycle B.cycle_chain (by intro a b h ha; exact (hstep a b h).symm.trans ha)
        (fun _ => Iff.rfl)⟩
  have hclose : ∀ u, (Delta.toCombMap.faceOf u ∈ faces ∧ ¬(Delta.toCombMap.faceOf u ∈ Q ↔ c)) →
      (Delta.toCombMap.faceOf (Delta.toCombMap.alpha u) ∈ faces ∧
        ¬(Delta.toCombMap.faceOf (Delta.toCombMap.alpha u) ∈ Q ↔ c)) := by
    rintro u ⟨hu, hne⟩
    by_cases ha : Delta.toCombMap.faceOf (Delta.toCombMap.alpha u) ∈ faces
    · exact ⟨ha, fun hiff => hne ((hA u hu ha).trans hiff)⟩
    · exact (hne (hcyc u ((B.cycle_mem_iff u).mpr ⟨hu, ha⟩))).elim
  have hadj : ∀ u, (Delta.toCombMap.faceOf (Delta.toCombMap.alpha u) ∈ faces ∧
        ¬(Delta.toCombMap.faceOf (Delta.toCombMap.alpha u) ∈ Q ↔ c)) ↔
      (Delta.toCombMap.faceOf u ∈ faces ∧ ¬(Delta.toCombMap.faceOf u ∈ Q ↔ c)) := by
    intro u
    refine ⟨fun h => ?_, hclose u⟩
    have h' := hclose (Delta.toCombMap.alpha u) h
    rwa [Delta.toCombMap.alpha_involutive u] at h'
  have hsig : ∀ u, Delta.toCombMap.faceOf (Delta.toCombMap.sigma u) =
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha u) := by
    intro u
    have h : Delta.toCombMap.sigma u = Delta.toCombMap.facePerm (Delta.toCombMap.alpha u) := by
      show Delta.toCombMap.sigma u =
        (Delta.toCombMap.sigma * Delta.toCombMap.alpha) (Delta.toCombMap.alpha u)
      rw [Equiv.Perm.mul_apply, Delta.toCombMap.alpha_involutive u]
    rw [h, Delta.toCombMap.faceOf_facePerm]
  have heqv : ∀ x y, Relation.EqvGen Delta.toCombMap.Adjacent x y →
      ((Delta.toCombMap.faceOf x ∈ faces ∧ ¬(Delta.toCombMap.faceOf x ∈ Q ↔ c)) ↔
        (Delta.toCombMap.faceOf y ∈ faces ∧ ¬(Delta.toCombMap.faceOf y ∈ Q ↔ c))) := by
    intro x y h
    induction h with
    | rel x y hxy =>
      rcases hxy with rfl | rfl
      · exact (hadj x).symm
      · rw [hsig x]
        exact (hadj x).symm
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have hall : ∀ d, Delta.toCombMap.faceOf d ∈ faces → (Delta.toCombMap.faceOf d ∈ Q ↔ c) := by
    intro d hd
    by_contra hne
    obtain ⟨d0, hd0⟩ : ∃ d0, d0 ∈ (Delta.faceBoundary Delta.outerFace).darts :=
      ⟨_, List.head_mem (Delta.faceBoundary Delta.outerFace).nonempty⟩
    have h := (heqv d d0 (Delta.toCombMap.connected_of_planar Delta.planar d d0)).mp ⟨hd, hne⟩
    rw [((Delta.faceBoundary Delta.outerFace).mem_iff d0).mp hd0] at h
    exact (B.all_gCells _ h.1).1 rfl
  by_cases hc : c
  · left
    intro f
    refine Quotient.inductionOn' f ?_
    intro d hd
    exact (hall d hd).mpr hc
  · right
    refine Finset.disjoint_left.mpr ?_
    intro f
    refine Quotient.inductionOn' f ?_
    intro d hd hq
    exact hc ((hall d hd).mp hq)

end Embedded.FaceSetBoundary

namespace RealizedRegionFamily

variable {D : RelGenSet G Lambda} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}

/-- **A selected region meeting the pocket lies inside it.**  Let `K` be a pocket walk of the
diagram of a family whose first side is the left side of the selected region `y` and whose second
side is the right side of the selected region `x`, and let `P` be a pocket region whose cycle is
the walk.  If no relator word has value one, every selected region meeting `P` lies in `P`. -/
theorem subset_of_not_disjoint_pocketRegion (S : RealizedRegionFamily D eps Delta) {lo hi : ℕ}
    (K : PocketWalk D eps S.diagram lo hi) {x y : RegionCandidate D eps S.diagram}
    (hxS : x ∈ S.family) (hyS : y ∈ S.family) (hfirst : K.firstSide = y.2.leftSide)
    (hsecond : K.secondSide = x.2.rightSide)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
    (P : PocketRegion S.diagram) (hinner : P.inner.cycle = K.walk)
    {z : RegionCandidate D eps S.diagram} (hzS : z ∈ S.family)
    (hmeet : ¬ Disjoint z.1 P.faces) : z.1 ⊆ P.faces := by
  have hside : ∀ a ∈ S.family, ∀ d, d ∈ a.2.boundary.cycle →
      S.diagram.toCombMap.faceOf d ∈ z.1 →
        S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ z.1 → False := by
    intro a haS d hda hdz haz
    have hb := (a.2.boundary.cycle_mem_iff d).mp hda
    by_cases hza : z = a
    · subst hza
      exact hb.2 haz
    · exact Finset.disjoint_left.mp (S.pairwise z hzS a haS hza) hdz hb.1
  have hcross : ∀ d, S.diagram.toCombMap.faceOf d ∈ z.1 →
      S.diagram.toCombMap.faceOf d ∈ P.faces →
        S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ z.1 →
          S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ P.faces := by
    intro d hdz hdP haz
    by_contra haP
    have hdw : d ∈ K.firstSide ++ invDarts S.diagram K.sourceArc.darts ++ K.secondSide ++
        K.targetArc.darts := by
      show d ∈ K.walk
      rw [← hinner]
      exact (P.inner.cycle_mem_iff d).mpr ⟨hdP, haP⟩
    rcases List.mem_append.mp hdw with h123 | h4
    · rcases List.mem_append.mp h123 with h12 | h3
      · rcases List.mem_append.mp h12 with h1 | h2
        · rw [hfirst] at h1
          refine hside y hyS d ?_ hdz haz
          rw [y.2.boundary_decomposition]
          exact List.mem_append_right _ h1
        · simp only [invDarts, List.mem_map, List.mem_reverse] at h2
          obtain ⟨e, he, rfl⟩ := h2
          rw [S.diagram.toCombMap.alpha_involutive e,
            ((S.diagram.faceBoundary (cell S.diagram K.source).face).mem_iff e).mp
              (K.sourceArc.mem_cycle_of_mem_darts he)] at haz
          have h := (z.2.boundary.all_gCells _ haz).2
          rw [DiscDiagram.faceWord,
            ← S.diagram.relatorCell_word _ (cell_mem S.diagram K.source)] at h
          exact hvalue _ (cell_mem S.diagram K.source) h
      · rw [hsecond] at h3
        refine hside x hxS d ?_ hdz haz
        rw [x.2.boundary_decomposition]
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h3))
    · have hdo := K.targetArc.mem_cycle_of_mem_darts h4
      simp only [outerDarts, List.mem_map, List.mem_reverse] at hdo
      obtain ⟨e, he, rfl⟩ := hdo
      rw [S.diagram.toCombMap.alpha_involutive e,
        ((S.diagram.faceBoundary S.diagram.outerFace).mem_iff e).mp he] at haz
      exact (z.2.boundary.all_gCells _ haz).1 rfl
  rcases z.2.boundary.subset_or_disjoint P.faces hcross with h | h
  · exact h
  · exact (hmeet h).elim

end RealizedRegionFamily

/-- **Meets implies contained.**  For a pocket walk `K` of the diagram of a family, with first side
the left side of the selected region `y` and second side the right side of the selected region
`x`, and a pocket region `P` whose cycle is the walk: if no relator word has value one, every
selected region meeting `P` lies in `P`. -/
def PocketMeetsContainedStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (Delta : DiscDiagram.{u, w, v} W)
    (S : RealizedRegionFamily D eps Delta) (lo hi : ℕ) (K : PocketWalk D eps S.diagram lo hi)
    (x y : RegionCandidate D eps S.diagram), x ∈ S.family → y ∈ S.family →
      K.firstSide = y.2.leftSide → K.secondSide = x.2.rightSide →
        (∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) →
          ∀ P : PocketRegion S.diagram, P.inner.cycle = K.walk →
            ∀ z ∈ S.family, ¬ Disjoint z.1 P.faces → z.1 ⊆ P.faces

theorem pocketMeetsContained : PocketMeetsContainedStatement.{u, w, v} := by
  intro _ _ _ _ _ _ _ S _ _ K _ _ hxS hyS hfirst hsecond hvalue P hinner _ hzS hmeet
  exact RealizedRegionFamily.subset_of_not_disjoint_pocketRegion S K hxS hyS hfirst hsecond hvalue
    P hinner hzS hmeet

/-- Three disjointness facts of a duplicate-free list `A ++ B ++ C ++ E`. -/
private theorem nodup_four {α : Type*} {A B C E : List α} (h : (A ++ B ++ C ++ E).Nodup) :
    (A ++ C).Nodup ∧ (∀ d ∈ A ++ C, d ∉ B) ∧ (∀ d ∈ A ++ C, d ∉ E) := by
  obtain ⟨h3, -, hE⟩ := List.nodup_append.mp h
  obtain ⟨h2, hC, hBC⟩ := List.nodup_append.mp h3
  obtain ⟨hA, -, hAB⟩ := List.nodup_append.mp h2
  refine ⟨List.nodup_append.mpr ⟨hA, hC, fun a ha b hb =>
    hBC a (List.mem_append_left _ ha) b hb⟩, ?_, ?_⟩
  · intro d hd hdB
    rcases List.mem_append.mp hd with hdA | hdC
    · exact hAB d hdA d hdB rfl
    · exact hBC d (List.mem_append_right _ hdB) d hdC rfl
  · intro d hd hdE
    rcases List.mem_append.mp hd with hdA | hdC
    · exact hE d (List.mem_append_left _ (List.mem_append_left _ hdA)) d hdE rfl
    · exact hE d (List.mem_append_right _ hdC) d hdE rfl

/-- A dart of a target arc on the boundary of a region crosses into the exterior or a cell. -/
private theorem faceOf_alpha_of_mem_targetBoundaryDarts {X : DiscDiagram.{u, w, v} W}
    {target : Option (Fin X.rCellCount)} (arc : CyclicArc (targetDarts X target))
    {d : X.toCombMap.Dart} (hd : d ∈ targetBoundaryDarts X target arc) :
    X.toCombMap.faceOf (X.toCombMap.alpha d) = X.outerFace ∨
      ∃ k : Fin X.rCellCount, X.toCombMap.faceOf (X.toCombMap.alpha d) = (cell X k).face := by
  cases target with
  | none =>
    left
    have hdo : d ∈ outerDarts X := arc.mem_cycle_of_mem_darts hd
    simp only [outerDarts, List.mem_map, List.mem_reverse] at hdo
    obtain ⟨e, he, rfl⟩ := hdo
    rw [X.toCombMap.alpha_involutive e]
    exact ((X.faceBoundary X.outerFace).mem_iff e).mp he
  | some k =>
    right
    refine ⟨k, ?_⟩
    have hs : d ∈ arc.reverseDarts := hd
    simp only [CyclicArc.reverseDarts, List.mem_map, List.mem_reverse] at hs
    obtain ⟨e, he, rfl⟩ := hs
    rw [X.toCombMap.alpha_involutive e]
    exact ((X.faceBoundary (cell X k).face).mem_iff e).mp (arc.mem_cycle_of_mem_darts he)

namespace GloballyDistinguishedSectionFamily

variable {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **The collapse of a disc region absorbing selected regions, section form.**  As
`false_of_disc_collapse_singleton`, with the section condition on the merged face stated on its
target arc. -/
theorem false_of_disc_absorbed_section
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (R : Surgery.InnerDiscRegion S.diagram)
    (absorbed : Finset (RegionCandidate D eps S.diagram)) (hsub : absorbed ⊆ S.family)
    (hcard : 2 ≤ absorbed.card)
    (havoid : ∀ a ∈ S.family, a ∉ absorbed → Disjoint a.1 R.faces)
    (H : ContiguityGeometry D eps R.diagram ({R.merged} : Finset R.diagram.toCombMap.Face))
    (hloop : H.target ≠ some H.source)
    (hsection : H.target = none → ∃ j : Fin cuts.count,
      cuts.cut j.castSucc ≤ H.targetArc.start.1 ∧
        H.targetArc.start.1 + H.targetArc.length ≤ cuts.cut j.succ)
    (hsource : 0 < H.sourceArc.length) (htarget : 0 < H.targetArc.length)
    (hweight : EstimatingSelection.familyWeight RegionCandidate.weight absorbed ≤
      H.sourceArc.length + H.targetArc.length) : False := by
  refine S.false_of_disc_collapse_singleton R absorbed hsub hcard havoid H ⟨hloop, ?_⟩ hsource
    htarget hweight
  intro hnone
  obtain ⟨j, hlo, hhi⟩ := hsection hnone
  exact ⟨j, hnone, hlo, hhi⟩

/-- **The kept cell of a pocket region, from the values of the relator words.**  Let `x ≠ y` be
selected regions and `K` a pocket walk to section `j` whose source arc spans those of `x`, a gap
and `y`, whose first side is the left side of `y` and whose second side is the right side of `x`.
Let `P` be a pocket region whose cycle is the walk.  If no relator word has value one, a relator
cell lies in `P`.  Otherwise `P` absorbs the selected regions meeting it, `x` and `y` among them,
into one contiguity region to section `j`.  Their source and target arc darts lie on `t_1` and
`t_2` and are pairwise distinct, so their weights add up to at most `|t_1| + |t_2|`. -/
theorem exists_kept_of_pocketRegion_of_value
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {i : Fin S.diagram.rCellCount} {j : Fin cuts.count} {x y : RegionCandidate D eps S.diagram}
    (hxS : x ∈ S.family) (hyS : y ∈ S.family) (hxy : x ≠ y)
    (K : PocketWalk D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ))
    (hgap : ∃ Gap : CyclicArc (cellDarts S.diagram i),
      K.sourceArc.darts = x.2.sourceArc.darts ++ Gap.darts ++ y.2.sourceArc.darts)
    (hfirst : K.firstSide = y.2.leftSide) (hsecond : K.secondSide = x.2.rightSide)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
    (P : PocketRegion S.diagram) (hinner : P.inner.cycle = K.walk) :
    ∃ kept : Fin S.diagram.rCellCount, (cell S.diagram kept).face ∈ P.faces := by
  classical
  by_contra hno
  have hcells : ∀ C ∈ S.diagram.relatorCells, C.face ∉ P.faces := by
    intro C hC hmem
    obtain ⟨n, rfl⟩ := List.mem_iff_get.mp hC
    exact hno ⟨n, hmem⟩
  obtain ⟨Gap, hGap⟩ := hgap
  have hcontained : ∀ a ∈ S.family, ¬ Disjoint a.1 P.faces → a.1 ⊆ P.faces :=
    fun a haS hameet => RealizedRegionFamily.subset_of_not_disjoint_pocketRegion
      S.toRealizedRegionFamily K hxS hyS hfirst hsecond hvalue P hinner haS hameet
  have hmeet : ∀ a ∈ S.family, (∀ e ∈ a.2.sourceArc.darts, e ∈ K.sourceArc.darts) →
      ¬ Disjoint a.1 P.faces := by
    intro a haS hsub
    obtain ⟨e, he⟩ := a.2.sourceArc.exists_mem_darts (S.nondegenerate a haS).1
    have hea : S.diagram.toCombMap.alpha e ∈ a.2.boundary.cycle := by
      rw [a.2.boundary_decomposition]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.mpr ⟨e, List.mem_reverse.mpr he, rfl⟩)))
    have hew : S.diagram.toCombMap.alpha e ∈ P.inner.cycle := by
      rw [hinner]
      show S.diagram.toCombMap.alpha e ∈ K.firstSide ++ invDarts S.diagram K.sourceArc.darts ++
        K.secondSide ++ K.targetArc.darts
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨e, List.mem_reverse.mpr (hsub e he), rfl⟩)))
    exact Finset.not_disjoint_iff.mpr ⟨_, ((a.2.boundary.cycle_mem_iff _).mp hea).1,
      ((P.inner.cycle_mem_iff _).mp hew).1⟩
  obtain ⟨A, hA⟩ : ∃ A : Finset (RegionCandidate D eps S.diagram),
      ∀ a, a ∈ A ↔ a ∈ S.family ∧ ¬ Disjoint a.1 P.faces :=
    ⟨S.family.filter fun a => ¬ Disjoint a.1 P.faces, fun _ => Finset.mem_filter⟩
  have hxA : x ∈ A := (hA x).mpr ⟨hxS, hmeet x hxS fun e he => by
    rw [hGap]
    exact List.mem_append_left _ (List.mem_append_left _ he)⟩
  have hyA : y ∈ A := (hA y).mpr ⟨hyS, hmeet y hyS fun e he => by
    rw [hGap]
    exact List.mem_append_right _ he⟩
  have hcard : 2 ≤ A.card :=
    (Finset.card_pair_eq_two_iff.mpr hxy).ge.trans (Finset.card_le_card
      (Finset.insert_subset_iff.mpr ⟨hxA, Finset.singleton_subset_iff.mpr hyA⟩))
  have hmemcyc : ∀ a : RegionCandidate D eps S.diagram, ∀ d ∈ a.2.sourceArc.reverseDarts ++
      targetBoundaryDarts S.diagram a.2.target a.2.targetArc, d ∈ a.2.boundary.cycle := by
    intro a d hd
    rw [a.2.boundary_decomposition]
    rcases List.mem_append.mp hd with h | h
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))
    · exact List.mem_append_left _ (List.mem_append_right _ h)
  have hbdcard : ∀ a : RegionCandidate D eps S.diagram,
      (a.2.sourceArc.reverseDarts ++
        targetBoundaryDarts S.diagram a.2.target a.2.targetArc).toFinset.card = a.weight := by
    intro a
    have hnd := a.2.boundary.cycle_nodup
    rw [a.2.boundary_decomposition] at hnd
    rw [List.toFinset_card_of_nodup (nodup_four hnd).1, List.length_append,
      ContiguityGeometry.targetBoundaryDarts_length a.2]
    simp only [CyclicArc.reverseDarts, List.length_map, List.length_reverse,
      CyclicArc.darts_length, RegionCandidate.weight]
  have hdisj : (A : Set (RegionCandidate D eps S.diagram)).PairwiseDisjoint fun a =>
      (a.2.sourceArc.reverseDarts ++
        targetBoundaryDarts S.diagram a.2.target a.2.targetArc).toFinset := by
    intro a ha b hb hab
    refine Finset.disjoint_left.mpr ?_
    intro d hda hdb
    exact Finset.disjoint_left.mp
      (S.pairwise a ((hA a).mp (Finset.mem_coe.mp ha)).1 b ((hA b).mp (Finset.mem_coe.mp hb)).1
        hab)
      ((a.2.boundary.cycle_mem_iff d).mp (hmemcyc a d (List.mem_toFinset.mp hda))).1
      ((b.2.boundary.cycle_mem_iff d).mp (hmemcyc b d (List.mem_toFinset.mp hdb))).1
  have hsubT : A.biUnion (fun a => (a.2.sourceArc.reverseDarts ++
        targetBoundaryDarts S.diagram a.2.target a.2.targetArc).toFinset) ⊆
      (invDarts S.diagram K.sourceArc.darts ++ K.targetArc.darts).toFinset := by
    intro d hd
    obtain ⟨a, ha, hda⟩ := Finset.mem_biUnion.mp hd
    have hda' := List.mem_toFinset.mp hda
    obtain ⟨haS, hameet⟩ := (hA a).mp ha
    have hb := (a.2.boundary.cycle_mem_iff d).mp (hmemcyc a d hda')
    have hdP : S.diagram.toCombMap.faceOf d ∈ P.faces := hcontained a haS hameet hb.1
    have haP : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∉ P.faces := by
      rcases List.mem_append.mp hda' with hs | ht
      · simp only [CyclicArc.reverseDarts, List.mem_map, List.mem_reverse] at hs
        obtain ⟨e, he, rfl⟩ := hs
        rw [S.diagram.toCombMap.alpha_involutive e,
          ((S.diagram.faceBoundary (cell S.diagram a.2.source).face).mem_iff e).mp
            (a.2.sourceArc.mem_cycle_of_mem_darts he)]
        exact hcells _ (cell_mem S.diagram a.2.source)
      · rcases faceOf_alpha_of_mem_targetBoundaryDarts a.2.targetArc ht with h | ⟨k, h⟩
        · rw [h]
          exact P.outerFace_not_mem
        · rw [h]
          exact hcells _ (cell_mem S.diagram k)
    have hdw : d ∈ K.firstSide ++ invDarts S.diagram K.sourceArc.darts ++ K.secondSide ++
        K.targetArc.darts := by
      show d ∈ K.walk
      rw [← hinner]
      exact (P.inner.cycle_mem_iff d).mpr ⟨hdP, haP⟩
    have hnd := a.2.boundary.cycle_nodup
    rw [a.2.boundary_decomposition] at hnd
    rcases List.mem_append.mp hdw with h123 | h4
    · rcases List.mem_append.mp h123 with h12 | h3
      · rcases List.mem_append.mp h12 with h1 | h2
        · rw [hfirst] at h1
          by_cases hay : a = y
          · rw [← hay] at h1
            exact ((nodup_four hnd).2.2 d hda' h1).elim
          · have hdy : d ∈ y.2.boundary.cycle := by
              rw [y.2.boundary_decomposition]
              exact List.mem_append_right _ h1
            exact (Finset.disjoint_left.mp (S.pairwise a haS y hyS hay) hb.1
              ((y.2.boundary.cycle_mem_iff d).mp hdy).1).elim
        · exact List.mem_toFinset.mpr (List.mem_append_left _ h2)
      · rw [hsecond] at h3
        by_cases hax : a = x
        · rw [← hax] at h3
          exact ((nodup_four hnd).2.1 d hda' h3).elim
        · have hdx : d ∈ x.2.boundary.cycle := by
            rw [x.2.boundary_decomposition]
            exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h3))
          exact (Finset.disjoint_left.mp (S.pairwise a haS x hxS hax) hb.1
            ((x.2.boundary.cycle_mem_iff d).mp hdx).1).elim
    · exact List.mem_toFinset.mpr (List.mem_append_right _ h4)
  have hweight : EstimatingSelection.familyWeight RegionCandidate.weight A ≤
      K.sourceArc.length + K.targetArc.length := by
    unfold EstimatingSelection.familyWeight
    calc ∑ a ∈ A, a.weight
        = ∑ a ∈ A, (a.2.sourceArc.reverseDarts ++
            targetBoundaryDarts S.diagram a.2.target a.2.targetArc).toFinset.card :=
          Finset.sum_congr rfl fun a _ => (hbdcard a).symm
      _ = (A.biUnion fun a => (a.2.sourceArc.reverseDarts ++
            targetBoundaryDarts S.diagram a.2.target a.2.targetArc).toFinset).card :=
          (Finset.card_biUnion hdisj).symm
      _ ≤ (invDarts S.diagram K.sourceArc.darts ++ K.targetArc.darts).toFinset.card :=
          Finset.card_le_card hsubT
      _ ≤ (invDarts S.diagram K.sourceArc.darts ++ K.targetArc.darts).length :=
          List.toFinset_card_le _
      _ = K.sourceArc.length + K.targetArc.length := by
          simp only [List.length_append, invDarts, List.length_map, List.length_reverse,
            CyclicArc.darts_length]
  have hrot : (Surgery.InnerDiscRegion.ofPocketRegion P hcells).region.cycle.rotate
      K.firstSide.length = K.sourceArc.reverseDarts ++ K.secondSide ++
        targetBoundaryDarts S.diagram none K.targetArc ++ K.firstSide := by
    rw [Surgery.InnerDiscRegion.ofPocketRegion_region_cycle, hinner]
    show (K.firstSide ++ invDarts S.diagram K.sourceArc.darts ++ K.secondSide ++
        K.targetArc.darts).rotate K.firstSide.length =
      invDarts S.diagram K.sourceArc.darts ++ K.secondSide ++ K.targetArc.darts ++ K.firstSide
    simp only [List.append_assoc, List.rotate_append_length_eq]
  refine S.false_of_disc_absorbed_section (Surgery.InnerDiscRegion.ofPocketRegion P hcells) A
    (fun a ha => ((hA a).mp ha).1) hcard
    (fun a haS haA => by
      by_contra h
      exact haA ((hA a).mpr ⟨haS, h⟩))
    ((Surgery.InnerDiscRegion.ofPocketRegion P hcells).mergedGeometry (target := none)
      K.sourceArc K.targetArc hrot K.secondSide_length_le K.firstSide_length_le
      K.secondSide_norm_le K.firstSide_norm_le) ?_ ?_ ?_ ?_ ?_
  · rw [Surgery.InnerDiscRegion.mergedGeometry_target]
    simp
  · rw [Surgery.InnerDiscRegion.mergedGeometry_targetArc_start,
      Surgery.InnerDiscRegion.mergedGeometry_targetArc_length]
    exact fun _ => ⟨j, K.lo_le, K.le_hi⟩
  · rw [Surgery.InnerDiscRegion.mergedGeometry_sourceArc_length]
    exact K.sourceArc_pos
  · rw [Surgery.InnerDiscRegion.mergedGeometry_targetArc_length]
    exact K.targetArc_pos
  · rw [Surgery.InnerDiscRegion.mergedGeometry_sourceArc_length,
      Surgery.InnerDiscRegion.mergedGeometry_targetArc_length]
    exact hweight

/-- **The kept cell of a simple pocket walk, from the values of the relator words.**  With `x`,
`y` and `K` as in `exists_kept_of_pocketRegion_of_value`, if the pocket walk is a simple closed
walk, a relator cell lies on its side. -/
theorem exists_kept_of_simple_of_value
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {i : Fin S.diagram.rCellCount} {j : Fin cuts.count} {x y : RegionCandidate D eps S.diagram}
    (hxS : x ∈ S.family) (hyS : y ∈ S.family) (hxy : x ≠ y)
    (K : PocketWalk D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ))
    (hgap : ∃ Gap : CyclicArc (cellDarts S.diagram i),
      K.sourceArc.darts = x.2.sourceArc.darts ++ Gap.darts ++ y.2.sourceArc.darts)
    (hfirst : K.firstSide = y.2.leftSide) (hsecond : K.secondSide = x.2.rightSide)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
    (hw : IsSimpleClosedWalk S.diagram.toCombMap K.walk) :
    ∃ kept : Fin S.diagram.rCellCount,
      (cell S.diagram kept).face ∈ sideFaces S.diagram.toCombMap K.walk := by
  obtain ⟨d, hd⟩ := K.targetArc.exists_mem_darts K.targetArc_pos
  have hdw : d ∈ K.walk := by
    show d ∈ K.firstSide ++ invDarts S.diagram K.sourceArc.darts ++ K.secondSide ++
      K.targetArc.darts
    exact List.mem_append_right _ hd
  have hout := PocketFaceSet.outerFace_not_mem_sideFaces_of_mem_outerDarts hw hdw
    (K.targetArc.mem_cycle_of_mem_darts hd)
  exact S.exists_kept_of_pocketRegion_of_value hxS hyS hxy K hgap hfirst hsecond hvalue
    (PocketRegion.ofSimpleClosedWalk hw hout) (PocketRegion.ofSimpleClosedWalk_inner_cycle hw hout)

end GloballyDistinguishedSectionFamily

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.FaceSetBoundary.subset_or_disjoint
#audit_axioms GroupApproximation.GGT.VanKampen.RealizedRegionFamily.subset_of_not_disjoint_pocketRegion
#audit_closed_axioms GroupApproximation.GGT.VanKampen.pocketMeetsContained
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.false_of_disc_absorbed_section
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.exists_kept_of_pocketRegion_of_value
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.exists_kept_of_simple_of_value
