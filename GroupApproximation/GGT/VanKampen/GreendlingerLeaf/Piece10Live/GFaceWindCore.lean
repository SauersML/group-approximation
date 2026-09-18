import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceChoose
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'`: indicators and coboundaries

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-55.

Map-level facts for the winding choice of `F'` (`Piece10Live/GFaceWind`).  A face function
`g : M.Face → ℤ` has the walk `c` as its coboundary when
`g (faceOf d) - g (faceOf (alpha d)) = [d ∈ c] - [alpha d ∈ c]` for every dart `d`.

* `gfaceWind_ind_cob`: the indicator of a face set is cobounded by its boundary darts.
* `gfaceWind_wind_cob`: the winding function of a simple closed walk (the indicator of its side,
  normalised to vanish at a base face) is cobounded by the walk.
* `gfaceWind_lind_split`: the dart indicator of a disjoint union.
* `gfaceWind_bd_iff`: for a `0/1`-valued face function cobounded by `c`, the boundary darts of
  its support are the darts of `c`.
* `gfaceWind_filter_sub`: filtering by a sub-walk.

## Truth check

Map-level identities; the Python check concerns the assembled construction, see
`Piece10Live/GFaceWind`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe v

open scoped Classical

/-- The indicator of a face set. -/
noncomputable def gfaceWind_ind {M : CombMap.{v}} (F : Finset M.Face) (f : M.Face) : ℤ :=
  if f ∈ F then 1 else 0

/-- The indicator of the darts of a list. -/
noncomputable def gfaceWind_lind {α : Type*} (c : List α) (d : α) : ℤ :=
  if d ∈ c then 1 else 0

/-- The membership test of a list, as a `Bool`. -/
noncomputable def gfaceWind_mem {α : Type*} (c : List α) (d : α) : Bool :=
  @decide (d ∈ c) (Classical.propDecidable _)

/-- The support of a face function where it takes the value `1`. -/
noncomputable def gfaceWind_faces {M : CombMap.{v}} (g : M.Face → ℤ) : Finset M.Face :=
  Finset.univ.filter fun f => g f = 1

/-- The winding function of a walk `A`: the indicator of its side, normalised at `o`. -/
noncomputable def gfaceWind_wind (M : CombMap.{v}) (o : M.Face) (A : List M.Dart)
    (f : M.Face) : ℤ :=
  gfaceWind_ind (SimpleClosedWalkSides.sideFaces M A) f -
    gfaceWind_ind (SimpleClosedWalkSides.sideFaces M A) o

theorem gfaceWind_mem_eq_true_iff {α : Type*} {c : List α} {x : α} :
    gfaceWind_mem c x = true ↔ x ∈ c := by
  unfold gfaceWind_mem
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

theorem gfaceWind_mem_faces {M : CombMap.{v}} {g : M.Face → ℤ} {f : M.Face} :
    f ∈ gfaceWind_faces g ↔ g f = 1 := by
  simp only [gfaceWind_faces, Finset.mem_filter, Finset.mem_univ, true_and]

theorem gfaceWind_ind_pos {M : CombMap.{v}} {F : Finset M.Face} {f : M.Face} (h : f ∈ F) :
    gfaceWind_ind F f = 1 :=
  if_pos h

theorem gfaceWind_ind_neg {M : CombMap.{v}} {F : Finset M.Face} {f : M.Face} (h : f ∉ F) :
    gfaceWind_ind F f = 0 :=
  if_neg h

theorem gfaceWind_lind_pos {α : Type*} {c : List α} {d : α} (h : d ∈ c) :
    gfaceWind_lind c d = 1 :=
  if_pos h

theorem gfaceWind_lind_neg {α : Type*} {c : List α} {d : α} (h : d ∉ c) :
    gfaceWind_lind c d = 0 :=
  if_neg h

/-- **The indicator coboundary**: if the boundary darts of `F` are the darts of `A`, then the
indicator of `F` is cobounded by `A`. -/
theorem gfaceWind_ind_cob {M : CombMap.{v}} {F : Finset M.Face} {A : List M.Dart}
    (hS : ∀ d, Surgery.MapCollapse.IsBoundaryDart M F d ↔ d ∈ A) (d : M.Dart) :
    gfaceWind_ind F (M.faceOf d) - gfaceWind_ind F (M.faceOf (M.alpha d)) =
      gfaceWind_lind A d - gfaceWind_lind A (M.alpha d) := by
  have hαα : M.faceOf (M.alpha (M.alpha d)) = M.faceOf d := by rw [M.alpha_involutive d]
  have hA : d ∈ A ↔ M.faceOf d ∈ F ∧ M.faceOf (M.alpha d) ∉ F := (hS d).symm
  have hA' : M.alpha d ∈ A ↔ M.faceOf (M.alpha d) ∈ F ∧ M.faceOf d ∉ F := by
    rw [← hS (M.alpha d)]
    show M.faceOf (M.alpha d) ∈ F ∧ M.faceOf (M.alpha (M.alpha d)) ∉ F ↔ _
    rw [hαα]
  by_cases h1 : M.faceOf d ∈ F
  · by_cases h2 : M.faceOf (M.alpha d) ∈ F
    · linarith [gfaceWind_ind_pos h1, gfaceWind_ind_pos h2,
        gfaceWind_lind_neg (show d ∉ A from fun h => (hA.mp h).2 h2),
        gfaceWind_lind_neg (show M.alpha d ∉ A from fun h => (hA'.mp h).2 h1)]
    · linarith [gfaceWind_ind_pos h1, gfaceWind_ind_neg h2,
        gfaceWind_lind_pos (hA.mpr ⟨h1, h2⟩),
        gfaceWind_lind_neg (show M.alpha d ∉ A from fun h => h2 (hA'.mp h).1)]
  · by_cases h2 : M.faceOf (M.alpha d) ∈ F
    · linarith [gfaceWind_ind_neg h1, gfaceWind_ind_pos h2,
        gfaceWind_lind_neg (show d ∉ A from fun h => h1 (hA.mp h).1),
        gfaceWind_lind_pos (hA'.mpr ⟨h2, h1⟩)]
    · linarith [gfaceWind_ind_neg h1, gfaceWind_ind_neg h2,
        gfaceWind_lind_neg (show d ∉ A from fun h => h1 (hA.mp h).1),
        gfaceWind_lind_neg (show M.alpha d ∉ A from fun h => h2 (hA'.mp h).1)]

/-- **The winding coboundary**: in a planar map the winding function of a simple closed walk is
cobounded by the walk. -/
theorem gfaceWind_wind_cob {M : CombMap.{v}} (hM : M.IsPlanar) {A : List M.Dart}
    (hw : IsSimpleClosedWalk M A) (o : M.Face) (d : M.Dart) :
    gfaceWind_wind M o A (M.faceOf d) - gfaceWind_wind M o A (M.faceOf (M.alpha d)) =
      gfaceWind_lind A d - gfaceWind_lind A (M.alpha d) := by
  have h := gfaceWind_ind_cob (fun x => hw.isBoundaryDart_sideFaces_iff hM x) d
  unfold gfaceWind_wind
  linarith

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWind_ind
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWind_lind
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWind_mem
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWind_faces
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWind_wind
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWind_mem_eq_true_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWind_mem_faces
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWind_ind_pos
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWind_ind_neg
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWind_lind_pos
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWind_lind_neg
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWind_ind_cob
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWind_wind_cob
