import GroupApproximation.GGT.SystolicDiscMirrorFoldCases
import GroupApproximation.GGT.VanKampen.CactusTopology
import GroupApproximation.GGT.VanKampen.CactusBoundary
import GroupApproximation.Meta.AxiomGuard

/-!
# Mirror fold models on the 2-simplex

Two triangulated discs in the 2-simplex on `Fin 3` meet the premises of the two cases of HC6,
and each has a disc with the same boundary and two fewer triangles.  These are nonvacuity
fixtures for `MirrorFoldDistinctStatement` and `MirrorFoldPinchedStatement`; they prove
neither statement.

* `Distinct.disc`: ten darts, triangles `[u, v, w]` and `[v, u, w']` glued along `u v`, with
  `w ≠ w'` both labelled `2`.  The outer face reads `[0, 2, 1, 2, 0]`.  `DistinctFold.disc` is
  the path `0 2 1`.
* `Pinched.disc`: eight darts, triangles `[u, v, w]` and `[v, u, w]` glued along `u v` and
  `u w`, with one third vertex `w`.  The outer face is the digon `[1, 2, 1]`.
  `PinchedFold.disc` is the edge `1 2`.
* `mirrorFoldDistinct_nonvacuous`, `mirrorFoldPinched_nonvacuous`: the premises of each case
  hold at the dart `u v`, and a disc with the same boundary has two fewer triangles.

## Manuscript status

Infrastructure for the torsion-free hyperbolic property (T) witness on the
Kotowski--Ollivier route; certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace Systolic
namespace MirrorFoldModel

open Equiv GGT.VanKampen

/-- The 2-simplex on `Fin 3`: the complete graph, with every triple of distinct vertices a
triangle. -/
def simplex : TriangleComplex (Fin 3) where
  G := ⊤
  Tri x y z := x ≠ y ∧ y ≠ z ∧ x ≠ z
  tri_swap12 h := ⟨h.1.symm, h.2.2, h.2.1⟩
  tri_swap23 h := ⟨h.2.2, h.2.1.symm, h.1⟩
  tri_adj h := ⟨(SimpleGraph.top_adj _ _).mpr h.1, (SimpleGraph.top_adj _ _).mpr h.2.1,
    (SimpleGraph.top_adj _ _).mpr h.2.2⟩

/-! ## Distinct third vertices -/

namespace Distinct

/-- Darts `0 : u → v`, `1 : v → w`, `2 : w → u`, `3 : u → w'`, `4 : w' → v`; dart `i + 5`
reverses dart `i`. -/
def dartAlpha : Perm (Fin 10) where
  toFun := ![5, 6, 7, 8, 9, 0, 1, 2, 3, 4]
  invFun := ![5, 6, 7, 8, 9, 0, 1, 2, 3, 4]
  left_inv := by decide
  right_inv := by decide

/-- Faces `[0, 1, 2]`, `[5, 3, 4]` and the outer face `[7, 6, 9, 8]`. -/
def faceRot : Perm (Fin 10) where
  toFun := ![1, 2, 0, 4, 5, 3, 9, 6, 7, 8]
  invFun := ![2, 0, 1, 5, 3, 4, 7, 8, 9, 6]
  left_inv := by decide
  right_inv := by decide

def M : CombMap where
  Dart := Fin 10
  dartFintype := inferInstance
  alpha := dartAlpha
  sigma := faceRot * dartAlpha
  alpha_involutive := by intro d; fin_cases d <;> rfl
  alpha_fixedPointFree := by decide

instance : DecidableEq M.Dart := inferInstanceAs (DecidableEq (Fin 10))
instance (n : ℕ) : OfNat M.Dart n := inferInstanceAs (OfNat (Fin 10) n)

def faceClass : Fin 10 → Fin 3 := ![0, 0, 0, 1, 1, 1, 2, 2, 2, 2]
def faceRep : Fin 3 → Fin 10 := ![0, 5, 7]

noncomputable def faceEquiv : M.Face ≃ Fin 3 :=
  OrbitClassifier.orbitEquiv M.facePerm faceClass faceRep
    (by decide) (by decide) (by decide)

/-- Vertices `u, v, w, w'` are the classes `0, 1, 2, 3`. -/
def vertexClass : Fin 10 → Fin 4 := ![0, 1, 2, 0, 3, 1, 2, 0, 3, 1]
def vertexRep : Fin 4 → Fin 10 := ![0, 1, 2, 4]

noncomputable def vertexEquiv : M.Vertex ≃ Fin 4 :=
  OrbitClassifier.orbitEquiv M.sigma vertexClass vertexRep
    (by decide) (by decide) (by decide)

theorem faceOf_eq {d e : Fin 10} (h : faceClass d = faceClass e) :
    M.faceOf d = M.faceOf e := by
  apply faceEquiv.injective
  exact h

theorem faceOf_ne {d e : Fin 10} (h : faceClass d ≠ faceClass e) :
    M.faceOf d ≠ M.faceOf e :=
  fun hde => h (congrArg faceEquiv hde)

theorem vertexOf_ne {d e : Fin 10} (h : vertexClass d ≠ vertexClass e) :
    M.vertexOf d ≠ M.vertexOf e :=
  fun hde => h (congrArg vertexEquiv hde)

theorem planar : M.IsPlanar := by
  constructor
  · have trans {d e f : M.Dart} (hde : Relation.EqvGen M.Adjacent d e)
        (hef : Relation.EqvGen M.Adjacent e f) : Relation.EqvGen M.Adjacent d f :=
      .trans _ _ _ hde hef
    have h05 : Relation.EqvGen M.Adjacent 0 5 := .rel _ _ (Or.inl rfl)
    have h03 : Relation.EqvGen M.Adjacent 0 3 := .rel _ _ (Or.inr rfl)
    have h51 : Relation.EqvGen M.Adjacent 5 1 := .rel _ _ (Or.inr rfl)
    have h19 : Relation.EqvGen M.Adjacent 1 9 := .rel _ _ (Or.inr rfl)
    have h16 : Relation.EqvGen M.Adjacent 1 6 := .rel _ _ (Or.inl rfl)
    have h94 : Relation.EqvGen M.Adjacent 9 4 := .rel _ _ (Or.inl rfl)
    have h37 : Relation.EqvGen M.Adjacent 3 7 := .rel _ _ (Or.inr rfl)
    have h38 : Relation.EqvGen M.Adjacent 3 8 := .rel _ _ (Or.inl rfl)
    have h72 : Relation.EqvGen M.Adjacent 7 2 := .rel _ _ (Or.inl rfl)
    have h01 := trans h05 h51
    have h09 := trans h01 h19
    have h07 := trans h03 h37
    have hstep : ∀ d : Fin 10, Relation.EqvGen M.Adjacent 0 d := by
      intro d
      fin_cases d
      · exact .refl _
      · exact h01
      · exact trans h07 h72
      · exact h03
      · exact trans h09 h94
      · exact h05
      · exact trans h01 h16
      · exact h07
      · exact trans h03 h38
      · exact h09
    intro d e
    exact .trans _ _ _ (.symm _ _ (hstep d)) (hstep e)
  · have hv : M.vertexCount = 4 := (Nat.card_congr vertexEquiv).trans (by simp)
    have hf : M.faceCount = 3 := (Nat.card_congr faceEquiv).trans (by simp)
    have hd : M.dartCount = 10 := by simp [CombMap.dartCount, M]
    have he := M.dartCount_eq_two_mul_edgeCount
    unfold CombMap.eulerCharacteristic
    rw [hv, hf]
    have heq : M.edgeCount = 5 := by omega
    rw [heq]
    norm_num

/-- The labels `u ↦ 0`, `v ↦ 1`, `w ↦ 2`, `w' ↦ 2`. -/
def vertexLabel : Fin 4 → Fin 3 := ![0, 1, 2, 2]

/-- The label of the start of a dart. -/
def label (d : Fin 10) : Fin 3 := vertexLabel (vertexClass d)

theorem adj_of_class : ∀ d : Fin 10, label d ≠ label (M.alpha d) := by
  intro d
  fin_cases d <;> decide

theorem tri_of_class : ∀ d : Fin 10, faceClass d ≠ faceClass 7 →
    (M.facePerm ^ 3) d = d ∧
      (label d ≠ label (M.facePerm d) ∧ label (M.facePerm d) ≠ label ((M.facePerm ^ 2) d) ∧
        label d ≠ label ((M.facePerm ^ 2) d)) := by
  intro d
  fin_cases d <;> decide

theorem outer_degree : M.faceDegree (M.faceOf 7) = 4 := by
  have h := closedOrbitList.length_eq_orbitDegree M.facePerm (7 : Fin 10)
  have hl : closedOrbitList M.facePerm (7 : Fin 10) = [7, 6, 9, 8] := by decide
  rw [hl] at h
  exact h.symm

/-- **The distinct model.** -/
noncomputable def disc : TriangulatedDisc simplex [0, 2, 1, 2, 0] where
  map := M
  planar := planar
  outer := M.faceOf 7
  vtx v := vertexLabel (vertexEquiv v)
  adj d := (SimpleGraph.top_adj _ _).mpr (adj_of_class d)
  tri d hd := tri_of_class d fun h => hd (faceOf_eq h)
  base := 7
  base_outer := rfl
  boundary := by
    rw [outer_degree]
    decide

theorem disc_innerFaceCount : disc.innerFaceCount = 2 := by
  have hf : M.faceCount = 3 := (Nat.card_congr faceEquiv).trans (by simp)
  change M.faceCount - 1 = 2
  omega

/-- The premises of `MirrorFoldDistinctStatement` at the dart `u v`. -/
theorem hypotheses :
    disc.map.faceOf (0 : Fin 10) ≠ disc.outer ∧
      disc.map.faceOf (disc.map.alpha (0 : Fin 10)) ≠ disc.outer ∧
      disc.vtx (disc.third (0 : Fin 10)) =
        disc.vtx (disc.third (disc.map.alpha (0 : Fin 10))) ∧
      disc.third (0 : Fin 10) ≠ disc.third (disc.map.alpha (0 : Fin 10)) :=
  ⟨faceOf_ne (d := 0) (e := 7) (by decide), faceOf_ne (d := M.alpha 0) (e := 7) (by decide),
    by decide,
    vertexOf_ne (d := (M.facePerm ^ 2) 0) (e := (M.facePerm ^ 2) (M.alpha 0)) (by decide)⟩

end Distinct

namespace DistinctFold

/-- Darts `0 : u → w`, `1 : w → v`; dart `i + 2` reverses dart `i`. -/
def dartAlpha : Perm (Fin 4) where
  toFun := ![2, 3, 0, 1]
  invFun := ![2, 3, 0, 1]
  left_inv := by decide
  right_inv := by decide

/-- The single face `[0, 1, 3, 2]`. -/
def faceRot : Perm (Fin 4) where
  toFun := ![1, 3, 0, 2]
  invFun := ![2, 0, 3, 1]
  left_inv := by decide
  right_inv := by decide

def M : CombMap where
  Dart := Fin 4
  dartFintype := inferInstance
  alpha := dartAlpha
  sigma := faceRot * dartAlpha
  alpha_involutive := by intro d; fin_cases d <;> rfl
  alpha_fixedPointFree := by decide

instance : DecidableEq M.Dart := inferInstanceAs (DecidableEq (Fin 4))
instance (n : ℕ) : OfNat M.Dart n := inferInstanceAs (OfNat (Fin 4) n)

def faceClass : Fin 4 → Fin 1 := fun _ => 0
def faceRep : Fin 1 → Fin 4 := ![0]

noncomputable def faceEquiv : M.Face ≃ Fin 1 :=
  OrbitClassifier.orbitEquiv M.facePerm faceClass faceRep
    (by decide) (by decide) (by decide)

/-- Vertices `u, w, v` are the classes `0, 1, 2`. -/
def vertexClass : Fin 4 → Fin 3 := ![0, 1, 1, 2]
def vertexRep : Fin 3 → Fin 4 := ![0, 1, 3]

noncomputable def vertexEquiv : M.Vertex ≃ Fin 3 :=
  OrbitClassifier.orbitEquiv M.sigma vertexClass vertexRep
    (by decide) (by decide) (by decide)

theorem faceOf_eq {d e : Fin 4} (h : faceClass d = faceClass e) :
    M.faceOf d = M.faceOf e := by
  apply faceEquiv.injective
  exact h

theorem planar : M.IsPlanar := by
  constructor
  · have h02 : Relation.EqvGen M.Adjacent 0 2 := .rel _ _ (Or.inl rfl)
    have h21 : Relation.EqvGen M.Adjacent 2 1 := .rel _ _ (Or.inr rfl)
    have h13 : Relation.EqvGen M.Adjacent 1 3 := .rel _ _ (Or.inl rfl)
    have h01 : Relation.EqvGen M.Adjacent 0 1 := .trans _ _ _ h02 h21
    have hstep : ∀ d : Fin 4, Relation.EqvGen M.Adjacent 0 d := by
      intro d
      fin_cases d
      · exact .refl _
      · exact h01
      · exact h02
      · exact .trans _ _ _ h01 h13
    intro d e
    exact .trans _ _ _ (.symm _ _ (hstep d)) (hstep e)
  · have hv : M.vertexCount = 3 := (Nat.card_congr vertexEquiv).trans (by simp)
    have hf : M.faceCount = 1 := (Nat.card_congr faceEquiv).trans (by simp)
    have hd : M.dartCount = 4 := by simp [CombMap.dartCount, M]
    have he := M.dartCount_eq_two_mul_edgeCount
    unfold CombMap.eulerCharacteristic
    rw [hv, hf]
    have heq : M.edgeCount = 2 := by omega
    rw [heq]
    norm_num

/-- The labels `u ↦ 0`, `w ↦ 2`, `v ↦ 1`. -/
def vertexLabel : Fin 3 → Fin 3 := ![0, 2, 1]

/-- The label of the start of a dart. -/
def label (d : Fin 4) : Fin 3 := vertexLabel (vertexClass d)

theorem adj_of_class : ∀ d : Fin 4, label d ≠ label (M.alpha d) := by
  intro d
  fin_cases d <;> decide

theorem outer_degree : M.faceDegree (M.faceOf 0) = 4 := by
  have h := closedOrbitList.length_eq_orbitDegree M.facePerm (0 : Fin 4)
  have hl : closedOrbitList M.facePerm (0 : Fin 4) = [0, 1, 3, 2] := by decide
  rw [hl] at h
  exact h.symm

/-- **The distinct fold**: the path `0 2 1`, with no triangle. -/
noncomputable def disc : TriangulatedDisc simplex [0, 2, 1, 2, 0] where
  map := M
  planar := planar
  outer := M.faceOf 0
  vtx v := vertexLabel (vertexEquiv v)
  adj d := (SimpleGraph.top_adj _ _).mpr (adj_of_class d)
  tri d hd := (hd (faceOf_eq (d := d) (e := 0) rfl)).elim
  base := 0
  base_outer := rfl
  boundary := by
    rw [outer_degree]
    decide

theorem disc_innerFaceCount : disc.innerFaceCount = 0 := by
  have hf : M.faceCount = 1 := (Nat.card_congr faceEquiv).trans (by simp)
  change M.faceCount - 1 = 0
  omega

end DistinctFold

/-! ## A common third vertex -/

namespace Pinched

/-- Darts `0 : u → v`, `1 : v → w`, `2 : w → u`, `3 : w → v`; dart `i + 4` reverses dart
`i`. -/
def dartAlpha : Perm (Fin 8) where
  toFun := ![4, 5, 6, 7, 0, 1, 2, 3]
  invFun := ![4, 5, 6, 7, 0, 1, 2, 3]
  left_inv := by decide
  right_inv := by decide

/-- Faces `[0, 1, 2]`, `[4, 6, 3]` and the outer digon `[7, 5]`. -/
def faceRot : Perm (Fin 8) where
  toFun := ![1, 2, 0, 4, 6, 7, 3, 5]
  invFun := ![2, 0, 1, 6, 3, 7, 4, 5]
  left_inv := by decide
  right_inv := by decide

def M : CombMap where
  Dart := Fin 8
  dartFintype := inferInstance
  alpha := dartAlpha
  sigma := faceRot * dartAlpha
  alpha_involutive := by intro d; fin_cases d <;> rfl
  alpha_fixedPointFree := by decide

instance : DecidableEq M.Dart := inferInstanceAs (DecidableEq (Fin 8))
instance (n : ℕ) : OfNat M.Dart n := inferInstanceAs (OfNat (Fin 8) n)

def faceClass : Fin 8 → Fin 3 := ![0, 0, 0, 1, 1, 2, 1, 2]
def faceRep : Fin 3 → Fin 8 := ![0, 4, 7]

noncomputable def faceEquiv : M.Face ≃ Fin 3 :=
  OrbitClassifier.orbitEquiv M.facePerm faceClass faceRep
    (by decide) (by decide) (by decide)

/-- Vertices `u, v, w` are the classes `0, 1, 2`, which are also their labels. -/
def vertexClass : Fin 8 → Fin 3 := ![0, 1, 2, 2, 1, 2, 0, 1]
def vertexRep : Fin 3 → Fin 8 := ![0, 1, 2]

noncomputable def vertexEquiv : M.Vertex ≃ Fin 3 :=
  OrbitClassifier.orbitEquiv M.sigma vertexClass vertexRep
    (by decide) (by decide) (by decide)

theorem faceOf_eq {d e : Fin 8} (h : faceClass d = faceClass e) :
    M.faceOf d = M.faceOf e := by
  apply faceEquiv.injective
  exact h

theorem faceOf_ne {d e : Fin 8} (h : faceClass d ≠ faceClass e) :
    M.faceOf d ≠ M.faceOf e :=
  fun hde => h (congrArg faceEquiv hde)

theorem vertexOf_eq {d e : Fin 8} (h : vertexClass d = vertexClass e) :
    M.vertexOf d = M.vertexOf e := by
  apply vertexEquiv.injective
  exact h

theorem planar : M.IsPlanar := by
  constructor
  · have trans {d e f : M.Dart} (hde : Relation.EqvGen M.Adjacent d e)
        (hef : Relation.EqvGen M.Adjacent e f) : Relation.EqvGen M.Adjacent d f :=
      .trans _ _ _ hde hef
    have h04 : Relation.EqvGen M.Adjacent 0 4 := .rel _ _ (Or.inl rfl)
    have h06 : Relation.EqvGen M.Adjacent 0 6 := .rel _ _ (Or.inr rfl)
    have h41 : Relation.EqvGen M.Adjacent 4 1 := .rel _ _ (Or.inr rfl)
    have h17 : Relation.EqvGen M.Adjacent 1 7 := .rel _ _ (Or.inr rfl)
    have h15 : Relation.EqvGen M.Adjacent 1 5 := .rel _ _ (Or.inl rfl)
    have h62 : Relation.EqvGen M.Adjacent 6 2 := .rel _ _ (Or.inl rfl)
    have h23 : Relation.EqvGen M.Adjacent 2 3 := .rel _ _ (Or.inr rfl)
    have h01 := trans h04 h41
    have h02 := trans h06 h62
    have hstep : ∀ d : Fin 8, Relation.EqvGen M.Adjacent 0 d := by
      intro d
      fin_cases d
      · exact .refl _
      · exact h01
      · exact h02
      · exact trans h02 h23
      · exact h04
      · exact trans h01 h15
      · exact h06
      · exact trans h01 h17
    intro d e
    exact .trans _ _ _ (.symm _ _ (hstep d)) (hstep e)
  · have hv : M.vertexCount = 3 := (Nat.card_congr vertexEquiv).trans (by simp)
    have hf : M.faceCount = 3 := (Nat.card_congr faceEquiv).trans (by simp)
    have hd : M.dartCount = 8 := by simp [CombMap.dartCount, M]
    have he := M.dartCount_eq_two_mul_edgeCount
    unfold CombMap.eulerCharacteristic
    rw [hv, hf]
    have heq : M.edgeCount = 4 := by omega
    rw [heq]
    norm_num

theorem adj_of_class : ∀ d : Fin 8, vertexClass d ≠ vertexClass (M.alpha d) := by
  intro d
  fin_cases d <;> decide

theorem tri_of_class : ∀ d : Fin 8, faceClass d ≠ faceClass 7 →
    (M.facePerm ^ 3) d = d ∧
      (vertexClass d ≠ vertexClass (M.facePerm d) ∧
        vertexClass (M.facePerm d) ≠ vertexClass ((M.facePerm ^ 2) d) ∧
        vertexClass d ≠ vertexClass ((M.facePerm ^ 2) d)) := by
  intro d
  fin_cases d <;> decide

theorem outer_degree : M.faceDegree (M.faceOf 7) = 2 := by
  have h := closedOrbitList.length_eq_orbitDegree M.facePerm (7 : Fin 8)
  have hl : closedOrbitList M.facePerm (7 : Fin 8) = [7, 5] := by decide
  rw [hl] at h
  exact h.symm

/-- **The pinched model.** -/
noncomputable def disc : TriangulatedDisc simplex [1, 2, 1] where
  map := M
  planar := planar
  outer := M.faceOf 7
  vtx v := vertexEquiv v
  adj d := (SimpleGraph.top_adj _ _).mpr (adj_of_class d)
  tri d hd := tri_of_class d fun h => hd (faceOf_eq h)
  base := 7
  base_outer := rfl
  boundary := by
    rw [outer_degree]
    decide

theorem disc_innerFaceCount : disc.innerFaceCount = 2 := by
  have hf : M.faceCount = 3 := (Nat.card_congr faceEquiv).trans (by simp)
  change M.faceCount - 1 = 2
  omega

/-- The premises of `MirrorFoldPinchedStatement` at the dart `u v`. -/
theorem hypotheses :
    disc.map.faceOf (0 : Fin 8) ≠ disc.outer ∧
      disc.map.faceOf (disc.map.alpha (0 : Fin 8)) ≠ disc.outer ∧
      disc.third (0 : Fin 8) = disc.third (disc.map.alpha (0 : Fin 8)) :=
  ⟨faceOf_ne (d := 0) (e := 7) (by decide), faceOf_ne (d := M.alpha 0) (e := 7) (by decide),
    vertexOf_eq (d := (M.facePerm ^ 2) 0) (e := (M.facePerm ^ 2) (M.alpha 0)) (by decide)⟩

end Pinched

namespace PinchedFold

/-- Dart `0 : v → w` and its reverse `1`. -/
def dartAlpha : Perm (Fin 2) where
  toFun := ![1, 0]
  invFun := ![1, 0]
  left_inv := by decide
  right_inv := by decide

def M : CombMap where
  Dart := Fin 2
  dartFintype := inferInstance
  alpha := dartAlpha
  sigma := dartAlpha * dartAlpha
  alpha_involutive := by intro d; fin_cases d <;> rfl
  alpha_fixedPointFree := by decide

instance : DecidableEq M.Dart := inferInstanceAs (DecidableEq (Fin 2))
instance (n : ℕ) : OfNat M.Dart n := inferInstanceAs (OfNat (Fin 2) n)

def faceClass : Fin 2 → Fin 1 := fun _ => 0
def faceRep : Fin 1 → Fin 2 := ![0]

noncomputable def faceEquiv : M.Face ≃ Fin 1 :=
  OrbitClassifier.orbitEquiv M.facePerm faceClass faceRep
    (by decide) (by decide) (by decide)

def vertexClass : Fin 2 → Fin 2 := ![0, 1]
def vertexRep : Fin 2 → Fin 2 := ![0, 1]

noncomputable def vertexEquiv : M.Vertex ≃ Fin 2 :=
  OrbitClassifier.orbitEquiv M.sigma vertexClass vertexRep
    (by decide) (by decide) (by decide)

theorem faceOf_eq {d e : Fin 2} (h : faceClass d = faceClass e) :
    M.faceOf d = M.faceOf e := by
  apply faceEquiv.injective
  exact h

theorem planar : M.IsPlanar := by
  constructor
  · have h01 : Relation.EqvGen M.Adjacent 0 1 := .rel _ _ (Or.inl rfl)
    have hstep : ∀ d : Fin 2, Relation.EqvGen M.Adjacent 0 d := by
      intro d
      fin_cases d
      · exact .refl _
      · exact h01
    intro d e
    exact .trans _ _ _ (.symm _ _ (hstep d)) (hstep e)
  · have hv : M.vertexCount = 2 := (Nat.card_congr vertexEquiv).trans (by simp)
    have hf : M.faceCount = 1 := (Nat.card_congr faceEquiv).trans (by simp)
    have hd : M.dartCount = 2 := by simp [CombMap.dartCount, M]
    have he := M.dartCount_eq_two_mul_edgeCount
    unfold CombMap.eulerCharacteristic
    rw [hv, hf]
    have heq : M.edgeCount = 1 := by omega
    rw [heq]
    norm_num

/-- The labels `v ↦ 1`, `w ↦ 2`. -/
def vertexLabel : Fin 2 → Fin 3 := ![1, 2]

/-- The label of the start of a dart. -/
def label (d : Fin 2) : Fin 3 := vertexLabel (vertexClass d)

theorem adj_of_class : ∀ d : Fin 2, label d ≠ label (M.alpha d) := by
  intro d
  fin_cases d <;> decide

theorem outer_degree : M.faceDegree (M.faceOf 0) = 2 := by
  have h := closedOrbitList.length_eq_orbitDegree M.facePerm (0 : Fin 2)
  have hl : closedOrbitList M.facePerm (0 : Fin 2) = [0, 1] := by decide
  rw [hl] at h
  exact h.symm

/-- **The pinched fold**: the edge `1 2`, with no triangle. -/
noncomputable def disc : TriangulatedDisc simplex [1, 2, 1] where
  map := M
  planar := planar
  outer := M.faceOf 0
  vtx v := vertexLabel (vertexEquiv v)
  adj d := (SimpleGraph.top_adj _ _).mpr (adj_of_class d)
  tri d hd := (hd (faceOf_eq (d := d) (e := 0) rfl)).elim
  base := 0
  base_outer := rfl
  boundary := by
    rw [outer_degree]
    decide

theorem disc_innerFaceCount : disc.innerFaceCount = 0 := by
  have hf : M.faceCount = 1 := (Nat.card_congr faceEquiv).trans (by simp)
  change M.faceCount - 1 = 0
  omega

end PinchedFold

/-- **The distinct case of HC6 is not vacuous.**  In the 2-simplex, `Distinct.disc` meets every
premise of `MirrorFoldDistinctStatement` at the dart `u v`, and `DistinctFold.disc` has the
same boundary and two fewer triangles. -/
theorem mirrorFoldDistinct_nonvacuous :
    ∃ (γ : List (Fin 3)) (D : TriangulatedDisc simplex γ) (d : D.map.Dart),
      (D.map.faceOf d ≠ D.outer ∧ D.map.faceOf (D.map.alpha d) ≠ D.outer ∧
        D.vtx (D.third d) = D.vtx (D.third (D.map.alpha d)) ∧
        D.third d ≠ D.third (D.map.alpha d)) ∧
      ∃ D' : TriangulatedDisc simplex γ, D'.innerFaceCount + 2 ≤ D.innerFaceCount := by
  refine ⟨_, Distinct.disc, (0 : Fin 10), Distinct.hypotheses, DistinctFold.disc, ?_⟩
  have h := Distinct.disc_innerFaceCount
  have h' := DistinctFold.disc_innerFaceCount
  omega

/-- **The pinched case of HC6 is not vacuous.**  In the 2-simplex, `Pinched.disc` meets every
premise of `MirrorFoldPinchedStatement` at the dart `u v`, and `PinchedFold.disc` has the same
boundary and two fewer triangles. -/
theorem mirrorFoldPinched_nonvacuous :
    ∃ (γ : List (Fin 3)) (D : TriangulatedDisc simplex γ) (d : D.map.Dart),
      (D.map.faceOf d ≠ D.outer ∧ D.map.faceOf (D.map.alpha d) ≠ D.outer ∧
        D.third d = D.third (D.map.alpha d)) ∧
      ∃ D' : TriangulatedDisc simplex γ, D'.innerFaceCount + 2 ≤ D.innerFaceCount := by
  refine ⟨_, Pinched.disc, (0 : Fin 8), Pinched.hypotheses, PinchedFold.disc, ?_⟩
  have h := Pinched.disc_innerFaceCount
  have h' := PinchedFold.disc_innerFaceCount
  omega

end MirrorFoldModel
end Systolic
end GroupApproximation

#audit_closed_axioms GroupApproximation.Systolic.MirrorFoldModel.mirrorFoldDistinct_nonvacuous
#audit_closed_axioms GroupApproximation.Systolic.MirrorFoldModel.mirrorFoldPinched_nonvacuous
