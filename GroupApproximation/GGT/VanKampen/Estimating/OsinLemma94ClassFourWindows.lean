import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CaseOneWalkHolds
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonClasses
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4 on class words: the face walk around two class runs

Osin (math/0411039v3, §9), proof of Lemma 9.4, Cases 1 and 2, on class words.  A class of
`OsinLemma94ClassPolygons` is a run of consecutive sides of its polygon, joined across gaps.  The gaps lie
off the face walk, so the darts of a class that the face walk passes are its side darts, read in order:
the side run `sideRun`.  Read from `classBase`, the side runs of the classes are the sides of the polygon
(`flatMap_sideRun`), and that reading is a rotation of the face walk (`exists_rotate_eq_classWalk`) of
value one (`classWalk_value`).

* `flatMap_rotate_eq_rotate`: rotating the index list rotates the concatenation by the length of the
  blocks moved.
* `OsinLemma94ClassPolygons.sideRun`, `classWalk`, `flatMap_sideRun`, `exists_rotate_eq_classWalk`,
  `classWalk_value`.
* `OsinLemma94ClassPolygons.class_four_windows`: two windows of the side runs of two different classes, in
  either cyclic order, on some rotation of the face walk `X ++ T ++ Y ++ P`, where `X` and `Y` join the
  prefixes of `classWalk` at the window ends.  This is the class-level `CaseOneWalk.polygon_four_windows`,
  shared by the class-level Case 2 and the class-level same-cell kill.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 9.4 inside the proof of Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open CaseOneWalk

/-- **Rotating the blocks rotates the concatenation**, by the length of the blocks moved to the end. -/
theorem flatMap_rotate_eq_rotate {α β : Type*} (l : List α) (f : α → List β) (m : ℕ) :
    (l.rotate m).flatMap f =
      (l.flatMap f).rotate (((l.take (m % l.length)).flatMap f).length) := by
  have e : l.flatMap f =
      (l.take (m % l.length)).flatMap f ++ (l.drop (m % l.length)).flatMap f := by
    rw [← List.flatMap_append, List.take_append_drop]
  have hk : ((l.take (m % l.length)).flatMap f).length ≤
      ((l.take (m % l.length)).flatMap f ++ (l.drop (m % l.length)).flatMap f).length := by
    rw [List.length_append]
    omega
  rw [List.rotate_eq_drop_append_take_mod, List.flatMap_append, e,
    List.rotate_eq_drop_append_take hk, List.drop_left' rfl, List.take_left' rfl]

namespace OsinLemma94ClassPolygons

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

/-- **The side run of class `i`**: the darts of its sides, in order, without the gaps. -/
def sideRun (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (i : ℕ) :
    List S.diagram.toCombMap.Dart :=
  (Q.classSides k i).flatMap (P.sideDarts k)

/-- **The sides of polygon `k` read from `classBase k`.** -/
def classWalk (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) :
    List S.diagram.toCombMap.Dart :=
  ((List.range (P.sideCount k)).rotate (Q.classBase k)).flatMap (P.sideDarts k)

/-- The side runs of the classes, read in order, are the sides read from `classBase k`. -/
theorem flatMap_sideRun (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) :
    (List.range (Q.classCount k)).flatMap (fun i => Q.sideRun k i) = Q.classWalk k := by
  show (List.range (Q.classCount k)).flatMap (fun i => (Q.classSides k i).flatMap (P.sideDarts k)) =
    ((List.range (P.sideCount k)).rotate (Q.classBase k)).flatMap (P.sideDarts k)
  rw [← Q.sides_eq k, List.flatMap_assoc]

/-- The sides read from `classBase k` are a rotation of the face walk. -/
theorem exists_rotate_eq_classWalk (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) :
    ∃ r, (S.diagram.faceBoundary (P.face k)).darts.rotate r = Q.classWalk k := by
  refine ⟨P.base k + ((((List.range (P.sideCount k)).take
    (Q.classBase k % (List.range (P.sideCount k)).length)).flatMap (P.sideDarts k)).length), ?_⟩
  rw [← List.rotate_rotate, P.walk k]
  show _ = ((List.range (P.sideCount k)).rotate (Q.classBase k)).flatMap (P.sideDarts k)
  rw [flatMap_rotate_eq_rotate]

/-- The sides read from `classBase k` have value one. -/
theorem classWalk_value (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) :
    RelLetter.listVal (dartWord S.diagram (Q.classWalk k)) = 1 := by
  show RelLetter.listVal (dartWord S.diagram
    (((List.range (P.sideCount k)).rotate (Q.classBase k)).flatMap (P.sideDarts k))) = 1
  rw [dartWord_flatMap_eq]
  exact listVal_flatMap_rotate _ (P.word k) _ (P.closed k)

/-- **The face walk around two class runs.**  For different classes `i` and `i'`, windows `[pa, pa']` of
the side run of `i` and `[pb', pb]` of the side run of `i'` sit on some rotation of the face walk as
`X ++ T ++ Y ++ P`, with `X` and `Y` joining the prefixes of `classWalk` at the window ends. -/
theorem class_four_windows (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) {i i' : ℕ}
    (hi : i < Q.classCount k) (hi' : i' < Q.classCount k) (hne : i ≠ i')
    {pa pa' pb' pb : ℕ} (haa : pa ≤ pa') (ha' : pa' ≤ (Q.sideRun k i).length)
    (hbb : pb' ≤ pb) (hb : pb ≤ (Q.sideRun k i').length) :
    ∃ (X Y : List S.diagram.toCombMap.Dart) (r : ℕ),
      (S.diagram.faceBoundary (P.face k)).darts.rotate r =
          X ++ ((Q.sideRun k i').drop pb').take (pb - pb') ++ Y ++
            ((Q.sideRun k i).drop pa).take (pa' - pa) ∧
        RelLetter.listVal (dartWord S.diagram ((Q.classWalk k).take
            (((List.range i).flatMap (fun x => Q.sideRun k x)).length + pa'))) *
            RelLetter.listVal (dartWord S.diagram X) =
          RelLetter.listVal (dartWord S.diagram ((Q.classWalk k).take
            (((List.range i').flatMap (fun x => Q.sideRun k x)).length + pb'))) ∧
        RelLetter.listVal (dartWord S.diagram ((Q.classWalk k).take
            (((List.range i').flatMap (fun x => Q.sideRun k x)).length + pb))) *
            RelLetter.listVal (dartWord S.diagram Y) =
          RelLetter.listVal (dartWord S.diagram ((Q.classWalk k).take
            (((List.range i).flatMap (fun x => Q.sideRun k x)).length + pa))) := by
  obtain ⟨r0, hr0⟩ := Q.exists_rotate_eq_classWalk k
  have hF := (Q.flatMap_sideRun k).symm
  have hls := rangeFlatMap_length_le (fun x => Q.sideRun k x) hi
  have hlt := rangeFlatMap_length_le (fun x => Q.sideRun k x) hi'
  have hlen : (Q.classWalk k).length =
      ((List.range (Q.classCount k)).flatMap (fun x => Q.sideRun k x)).length := by
    rw [hF]
  have horder :
      (((List.range i).flatMap (fun x => Q.sideRun k x)).length + pa' ≤
          ((List.range i').flatMap (fun x => Q.sideRun k x)).length + pb' ∧
        ((List.range i').flatMap (fun x => Q.sideRun k x)).length + pb ≤ (Q.classWalk k).length) ∨
      (((List.range i').flatMap (fun x => Q.sideRun k x)).length + pb ≤
          ((List.range i).flatMap (fun x => Q.sideRun k x)).length + pa ∧
        ((List.range i).flatMap (fun x => Q.sideRun k x)).length + pa' ≤ (Q.classWalk k).length) := by
    rw [hlen]
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := rangeFlatMap_length_le (fun x => Q.sideRun k x) h
      exact Or.inl ⟨by omega, by omega⟩
    · have := rangeFlatMap_length_le (fun x => Q.sideRun k x) h
      exact Or.inr ⟨by omega, by omega⟩
  obtain ⟨X, Y, r, hrot, hX, hY⟩ := walk_four_windows _ _ r0 hr0 (Q.classWalk_value k)
    (Nat.add_le_add_left haa _) (Nat.add_le_add_left hbb _) horder
  refine ⟨X, Y, r, ?_, hX, hY⟩
  have e1 : ((List.range i').flatMap (fun x => Q.sideRun k x)).length + pb -
      (((List.range i').flatMap (fun x => Q.sideRun k x)).length + pb') = pb - pb' := by omega
  have e2 : ((List.range i).flatMap (fun x => Q.sideRun k x)).length + pa' -
      (((List.range i).flatMap (fun x => Q.sideRun k x)).length + pa) = pa' - pa := by omega
  rw [hrot, e1, e2, hF, rangeFlatMap_drop_take (fun x => Q.sideRun k x) hi' (by omega),
    rangeFlatMap_drop_take (fun x => Q.sideRun k x) hi (by omega)]

end OsinLemma94ClassPolygons

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.flatMap_rotate_eq_rotate
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.exists_rotate_eq_classWalk
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.class_four_windows
