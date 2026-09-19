import GroupApproximation.Manuscript.NonMF.Full.GL06p.Assembly
import GroupApproximation.Manuscript.NonMF.Full.GL06p.Geodesic
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06p: the slit pocket core and its windows

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), the all-cells case.  Infrastructure for
`thm:hull` (non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's
Lemma 9.7).  Step 4 of lane nm-gl06e's construction, and the interface for steps 2 and 3.

`GL06h4.gl06h4Nearest_Pocket` bundles the cut of `Δ` along a minimal path with two window
bounds on the slit sides.  This module separates them.

* `SlitPocketCore`: every field of the slit pocket except the two windows.  It adds the minimality
  of both slit sides against every walk from `∂Δ` to a relator cell.  This is what steps 2 (the
  ribbon copy) and 3 (the pocket region) deliver.  `GL06p.slit_minimal_of_geodesic` gives the
  minimality fields for geodesic spellings of the minimal path.
* `slitPocketCoreStatement`: steps 2 and 3, a core for every diagram with a nearest path.
* `longSlitWindowsStatement`: step 4, the window bound on a slit side longer than `ε + ε`.
* `nearOrShort_of_le`: a slit side of length at most `ε + ε` needs no window bound.  This covers
  Osin's degenerate cases, including the empty slit of a nearest cell touching `∂Δ`.
* `slitPocketOfNearestPath_of_core`: the two statements give `slitPocketOfNearestPathStatement`.
* `allCellsShort_of_core`: and so GL06e's residual
  `AllCellsShortEnclosedRefutedBelowSectionStatement`.

## Truth of `longSlitWindowsStatement`

It is Osin's gluing argument, recorded in GL06h4's module docstring.  Take a region of an
`O`-equivalent copy of the pocket to the slit side `s₁`, with target arc at offset `k`, of length
`L`, and right side `e ≤ ε`.  Gluing it back gives a walk from `∂Δ` to another relator cell of
length `k + e`.  So `|s₁| ≤ k + e` by `slitIn_minimal`, and `L ≤ ε + ε`.  Lane gl-p07-86's
Python models found no counterexample (GL06h4's docstring); this lane did not re-check them.
The gluing step is the transport of such a region along the pocket (`pocketCellTransport`,
`OsinPocketGlueCarriers`).

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121); certifies no printed sentence on
its own.  `slitPocketCoreStatement` and `longSlitWindowsStatement` are combinatorial clauses of
Osin's proof, not literature statements.
-/

namespace GroupApproximation.Full.GL06p

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.WordMetric

section Core

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **The slit pocket core** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121): every field of `GL06h4.gl06h4Nearest_Pocket` except the two
windows, together with the minimality of both slit sides. -/
structure SlitPocketCore (D : RelGenSet G Lambda) (Delta : DiscDiagram.{u, w, v} W) where
  copy : DiscDiagram.{u, w, v} W
  equiv : OEquivalentDiscDiagram Delta copy
  pocket : PocketRegion copy
  follows : pocket.outer.FollowsBoundary
  inner : RelatorCell copy.toCombMap copy.outerFace W
  inner_mem : inner ∈ copy.relatorCells
  inner_face : inner.face ∈ pocket.faces
  nearest : Fin copy.rCellCount
  nearest_face : (cell copy nearest).face ∉ pocket.faces
  arc : CyclicArc (cellDarts copy nearest)
  outerPart : List copy.toCombMap.Dart
  slitIn : List copy.toCombMap.Dart
  slitOut : List copy.toCombMap.Dart
  decomposition : invDarts copy pocket.outer.cycle =
    outerPart ++ slitIn ++ invDarts copy arc.darts ++ slitOut
  outer_geodesic : GGT.OsinComponents.IsGeodesicWord D 1
    (RelLetter.listVal (dartWord copy outerPart)) (dartWord copy outerPart)
  slitIn_geodesic : GGT.OsinComponents.IsGeodesicWord D 1
    (RelLetter.listVal (dartWord copy slitIn)) (dartWord copy slitIn)
  slitOut_geodesic : GGT.OsinComponents.IsGeodesicWord D 1
    (RelLetter.listVal (dartWord copy slitOut)) (dartWord copy slitOut)
  outer_length_le : outerPart.length ≤ Delta.boundaryWord.length
  /-- The slit side `s₁` is no longer than any walk from `∂Δ` to a relator cell. -/
  slitIn_minimal : ∀ (j : Fin Delta.rCellCount) (q : List Delta.toCombMap.Dart),
    IsBoundaryToCellWalk Delta j q → slitIn.length ≤ q.length
  /-- The slit side `s₂` is no longer than any walk from `∂Δ` to a relator cell. -/
  slitOut_minimal : ∀ (j : Fin Delta.rCellCount) (q : List Delta.toCombMap.Dart),
    IsBoundaryToCellWalk Delta j q → slitOut.length ≤ q.length

namespace SlitPocketCore

variable {D : RelGenSet G Lambda} {Delta : DiscDiagram.{u, w, v} W}

/-- **The slit pocket from its core and two windows.** -/
def toPocket (C : SlitPocketCore D Delta) {eps : ℕ}
    (hin : GL06h4.gl06h4Nearest_NearOrShort D eps C.pocket C.outerPart.length
      (C.outerPart.length + C.slitIn.length))
    (hout : GL06h4.gl06h4Nearest_NearOrShort D eps C.pocket
      (C.outerPart.length + C.slitIn.length + C.arc.length)
      (C.outerPart.length + C.slitIn.length + C.arc.length + C.slitOut.length)) :
    GL06h4.gl06h4Nearest_Pocket D eps Delta where
  copy := C.copy
  equiv := C.equiv
  pocket := C.pocket
  follows := C.follows
  inner := C.inner
  inner_mem := C.inner_mem
  inner_face := C.inner_face
  nearest := C.nearest
  nearest_face := C.nearest_face
  arc := C.arc
  outerPart := C.outerPart
  slitIn := C.slitIn
  slitOut := C.slitOut
  decomposition := C.decomposition
  outer_geodesic := C.outer_geodesic
  slitIn_geodesic := C.slitIn_geodesic
  slitOut_geodesic := C.slitOut_geodesic
  outer_length_le := C.outer_length_le
  near_in := hin
  near_out := hout

end SlitPocketCore

/-- **A short window needs no bound** (Osin, proof of Lemma 9.7(b)): a window of width at most
`ε + ε` satisfies the first disjunct of `GL06h4.gl06h4Nearest_NearOrShort`. -/
theorem nearOrShort_of_le (D : RelGenSet G Lambda) (eps : ℕ) {X : DiscDiagram.{u, w, v} W}
    (P : PocketRegion X) (lo len : ℕ) (h : len ≤ eps + eps) :
    GL06h4.gl06h4Nearest_NearOrShort D eps P lo (lo + len) :=
  Or.inl (by omega)

#audit_axioms GroupApproximation.Full.GL06p.nearOrShort_of_le

end Core

/-- **Steps 2 and 3: a slit pocket core for every diagram with a nearest path** (Osin, proof of
Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121). -/
def slitPocketCoreStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W),
    Delta.LeastArea → (∀ d, (symmetricLabelAlphabet D).IsLetter (Delta.label d)) →
      (∀ word ∈ W, 1 < word.length) → 2 ≤ Delta.rCellCount →
        NearestCellPath Delta → Nonempty (SlitPocketCore D Delta)

#audit_axioms GroupApproximation.Full.GL06p.slitPocketCoreStatement

/-- **Step 4: the window on a long slit side** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121): on a slit side longer than `ε + ε`, every region of a copy of
the pocket has target arc at most `ε + ε`. -/
def longSlitWindowsStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W),
    Delta.LeastArea → (∀ d, (symmetricLabelAlphabet D).IsLetter (Delta.label d)) →
      (∀ word ∈ W, 1 < word.length) → 2 ≤ Delta.rCellCount →
        Delta.boundaryWord.length ≤ eps + eps →
          ∀ C : SlitPocketCore D Delta,
            (eps + eps < C.slitIn.length →
              GL06h4.NearWindow D eps C.pocket C.outerPart.length
                (C.outerPart.length + C.slitIn.length)) ∧
            (eps + eps < C.slitOut.length →
              GL06h4.NearWindow D eps C.pocket
                (C.outerPart.length + C.slitIn.length + C.arc.length)
                (C.outerPart.length + C.slitIn.length + C.arc.length + C.slitOut.length))

#audit_axioms GroupApproximation.Full.GL06p.longSlitWindowsStatement

/-- **The slit pocket of a nearest path from the core and the long windows** (Osin, proof of
Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121): a short slit side needs no window. -/
theorem slitPocketOfNearestPath_of_core (hcore : slitPocketCoreStatement.{u, w, v})
    (hwin : longSlitWindowsStatement.{u, w, v}) :
    slitPocketOfNearestPathStatement.{u, w, v} := by
  intro _G _ _Lambda D eps W Delta hlea hletters hW hcells hboundary N
  obtain ⟨C⟩ := hcore D W Delta hlea hletters hW hcells N
  obtain ⟨hin, hout⟩ := hwin D eps W Delta hlea hletters hW hcells hboundary C
  refine ⟨C.toPocket ?_ ?_⟩
  · by_cases h : C.slitIn.length ≤ eps + eps
    · exact nearOrShort_of_le D eps C.pocket _ _ h
    · exact Or.inr (hin (by omega))
  · by_cases h : C.slitOut.length ≤ eps + eps
    · exact nearOrShort_of_le D eps C.pocket _ _ h
    · exact Or.inr (hout (by omega))

#audit_axioms GroupApproximation.Full.GL06p.slitPocketOfNearestPath_of_core

/-- **GL06e's all-cells residual from the core and the long windows** (Osin, proof of
Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem allCellsShort_of_core (hcore : slitPocketCoreStatement.{u, w, v})
    (hwin : longSlitWindowsStatement.{u, w, v}) :
    GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{u, w, v} :=
  allCellsShort_of_slitPocketOfNearestPath (slitPocketOfNearestPath_of_core hcore hwin)

#audit_axioms GroupApproximation.Full.GL06p.allCellsShort_of_core

end GroupApproximation.Full.GL06p
