import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.NoWalkAbsorbLemmas
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-35: audit of the whole-pocket residual

## LOUD: the LEFT disjunct of `NoWalkAbsorbStatement` is false on nondegenerate contacts

`noWalkAbsorb_left_mem`: take an outer walk `ow` of the whole pocket `P = sideFaces K.walk`, and a
contact dart `d ∈ a.cellArcList i` with `faceOf d ∉ P`.  Then `α d` is a dart of `K.walk`
(the contact of `a` starts `K.firstArc`), so `faceOf (α d) ∈ P`, and `d ∈ ow` by `mem_iff`.
Its across face `faceOf (α d)` is in `a.1` (`faceOf_alpha_mem_of_mem_cellArcList`).  So the dart
clause of LEFT forces `d ∈ G₁ ∨ d ∈ G₂`.  `noWalkAbsorb_left_false` is the resulting
contradiction when `d` lies on neither.

In the intended application, `S.nondegenerate` makes `a.cellArcList i` nonempty.  Its darts are
cell darts of `Π_i` that come before `G₁` in `K.firstArc` (so off `G₁` when that arc has no
repeated dart), and off the cell `Π_j ≠ Π_i`.  In a disc pocket the face of `Π_i` is outside
`sideFaces K.walk`.  So LEFT fails there, and `NoWalkAbsorbStatement` reduces to its right
disjunct, the target conclusion.

## Rejected strengthening: closed arcs

The closure hypothesis of `noWalkAbsorb_step_of_closed` (every `g ∈ G₁ ∩ ow` with
`facePerm g ∈ G₁` has `facePerm g ∈ ow`) cannot be asked of the face set in general.  In M9 with a
hole (an `a`-lobe attached along `E` in the middle of `G₁`), the face set has to exclude the
lobe.  The walk leaves `G₁` at the first dart of `E` while `facePerm` stays on `G₁`, off the walk.
A residual that demands closure is therefore FALSE there.

## The local step clause is a face-successor step

`noWalk_stepClause_iff`: at a position whose next walk dart lies on the same face (for example two
darts of `G₁`), the step clause `walkKeep (facePerm ow[p]) ∨ PinchFreeAt ow[p]` holds exactly
when `facePerm ow[p] = ow[p+1]`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded SimpleClosedWalkSides

namespace FourPieceWitness

section Audit

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **An outer contact dart of `a` lies on the walk, with an `a.1` face across.**  So the dart
clause of LEFT puts it on `G₁` or on `G₂`. -/
theorem noWalkAbsorb_left_mem {a : RegionCandidate D eps X} (hai : a.JoinsCells i j)
    (K : CellPocketWalk D eps X i j) {l post : List X.toCombMap.Dart}
    (hG : K.firstArc.darts = a.cellArcList i ++ l ++ post) {ow : List X.toCombMap.Dart}
    (E : EnclosedFaceSetSucc X (sideFaces X.toCombMap K.walk) ow)
    {l₁ l₂ : List X.toCombMap.Dart} {fb : Finset X.toCombMap.Face}
    (hdarts : ∀ d ∈ ow, d ∈ l₁ ∨ d ∈ l₂ ∨
      (X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ a.1 ∧
        X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ fb))
    {d : X.toCombMap.Dart} (hd : d ∈ a.cellArcList i)
    (hface : X.toCombMap.faceOf d ∉ sideFaces X.toCombMap K.walk) :
    d ∈ l₁ ∨ d ∈ l₂ := by
  have hG' : K.firstArc.darts = [] ++ a.cellArcList i ++ (l ++ post) := by
    rw [hG]
    simp only [List.nil_append, List.append_assoc]
  have hinv : X.toCombMap.alpha d ∈ invDarts X (a.cellArcList i) := by
    rw [Embedded.mem_invDarts_iff, X.toCombMap.alpha_involutive d]
    exact hd
  have hx : X.toCombMap.alpha d ∈ K.walk := noWalkAbsorb_mem_walk_of_first K hG' hinv
  have hacross : X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ sideFaces X.toCombMap K.walk :=
    (mem_sideFaces_iff X.toCombMap K.walk (X.toCombMap.alpha d)).mpr
      ⟨X.toCombMap.alpha d, hx, Relation.EqvGen.refl _⟩
  have hmem : d ∈ ow := (E.mem_iff d).mpr ⟨hface, Or.inl hacross⟩
  have ha : X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ a.1 :=
    RegionCandidate.faceOf_alpha_mem_of_mem_cellArcList hai hd
  rcases hdarts d hmem with h | h | ⟨hna, -⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd ha hna

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.noWalkAbsorb_left_mem

/-- **LEFT fails at an outer contact dart of `a` off both gaps.** -/
theorem noWalkAbsorb_left_false {a : RegionCandidate D eps X} (hai : a.JoinsCells i j)
    (K : CellPocketWalk D eps X i j) {l post : List X.toCombMap.Dart}
    (hG : K.firstArc.darts = a.cellArcList i ++ l ++ post) {ow : List X.toCombMap.Dart}
    (E : EnclosedFaceSetSucc X (sideFaces X.toCombMap K.walk) ow)
    {l₁ l₂ : List X.toCombMap.Dart} {fb : Finset X.toCombMap.Face}
    (hdarts : ∀ d ∈ ow, d ∈ l₁ ∨ d ∈ l₂ ∨
      (X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ a.1 ∧
        X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ fb))
    {d : X.toCombMap.Dart} (hd : d ∈ a.cellArcList i)
    (hface : X.toCombMap.faceOf d ∉ sideFaces X.toCombMap K.walk)
    (hn₁ : d ∉ l₁) (hn₂ : d ∉ l₂) : False :=
  (noWalkAbsorb_left_mem hai K hG E hdarts hd hface).elim hn₁ hn₂

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.noWalkAbsorb_left_false

end Audit

section Step

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {X : DiscDiagram.{u, w, v} W} {F : Finset X.toCombMap.Face} {ow : List X.toCombMap.Dart}

/-- **A step clause on one face is a face-successor step.** -/
theorem noWalk_stepClause_iff (E : EnclosedFaceSetSucc X F ow) (p : ℕ) (hp : p < ow.length)
    (hface : X.toCombMap.faceOf
        (ow[(p + 1) % ow.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le p) hp))) =
      X.toCombMap.faceOf ow[p]) :
    (walkKeep X.toCombMap ow (X.toCombMap.facePerm ow[p]) ∨
        PocketRun.PinchFreeAt X.toCombMap ow[p]) ↔
      X.toCombMap.facePerm ow[p] =
        ow[(p + 1) % ow.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le p) hp)) := by
  constructor
  · rintro (hk | hpf)
    · exact PocketRun.succ_eq_facePerm_of_keep E p hp hk
    · exact PocketRun.succ_eq_facePerm_of_pinchFree E p hp hpf hface
  · intro h
    refine Or.inl (Or.inl ?_)
    rw [h]
    exact List.getElem_mem _

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.noWalk_stepClause_iff

end Step

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
