import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CuttingSidesCount
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonClasses
import GroupApproximation.GGT.VanKampen.FaceSetBoundaryRotation
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04, window shapes: successive sides are contiguous on the polygon face walk

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, on class words (step 2 of the argument recorded in
`Piece04.RotationTurns`): "Consecutive class sides `s`, `s+1` are consecutive on `∂Γ`
(`sides_eq`), so `φ (side_s.last) = side_(s+1).head`.  Sides are nonempty."

This module proves the polygon half of that sentence, read cyclically: the last dart of side `s`
and the first dart of side `(s + 1) % k_i` follow the face permutation `φ = facePerm`.

## Proof

Let `L` be the walk of `Γ = P.face k` rotated by `P.base k`; by `P.walk`,
`L = (range m).flatMap sideDarts` with `m = P.sideCount k`.

* `s + 1 < m`.  `(s + 1) % m = s + 1`, and side `s` followed by side `s + 1` is an infix of `L`.
  `L` follows `φ` (`OsinLemma94RealizedPolygons.walk_isChain`), so the junction of the two
  blocks does too.  This is `OsinLemma94RealizedPolygons.facePerm_getLast_eq_head`.
* `s + 1 = m` (this includes `m = 1`).  `(s + 1) % m = 0`.  Splitting the last block,
  `L = (range s).flatMap sideDarts ++ sideDarts s`, so `L.getLast? = (sideDarts s).getLast?`
  since sides are nonempty (`P.side_ne_nil`).  Splitting the first block
  (`List.range_succ_eq_map`), `L.head? = (sideDarts 0).head?`.  A rotation of a closed face
  walk closes (`Embedded.isChain_rotate_closing` on `faceBoundary.chain`/`closes`), so
  `φ L.getLast = L.head`.

The statement is TRUE as printed in the lane (`gl-p04-03`); no correction was needed.  It uses
none of the class data `Q`; the binder is kept so that the endpoint has the lane's text.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.SideSuccFace

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate

/-- A list whose last dart is related to its first dart relates any `getLast?` value to any
`head?` value. -/
theorem rel_of_getLast?_of_head? {α : Type*} {R : α → α → Prop} {L : List α} (hne : L ≠ [])
    (hclose : R (L.getLast hne) (L.head hne)) {d t : α}
    (hd : L.getLast? = some d) (ht : L.head? = some t) : R d t := by
  rw [List.getLast?_eq_some_getLast hne, Option.some_inj] at hd
  rw [List.head?_eq_some_head hne, Option.some_inj] at ht
  rw [← hd, ← ht]
  exact hclose

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.SideSuccFace.rel_of_getLast?_of_head?

/-- **Successive sides, read cyclically, over the polygons alone.**  The last dart of side `s`
and the first dart of side `(s + 1) % k_i` follow the face permutation. -/
theorem facePerm_last_core {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) {s : ℕ} (hs : s < P.sideCount k)
    {d t : S.diagram.toCombMap.Dart} (hd : (P.sideDarts k s).getLast? = some d)
    (ht : (P.sideDarts k ((s + 1) % P.sideCount k)).head? = some t) :
    S.diagram.toCombMap.facePerm d = t := by
  by_cases hlt : s + 1 < P.sideCount k
  · rw [Nat.mod_eq_of_lt hlt] at ht
    exact P.facePerm_getLast_eq_head hlt (Option.mem_def.mpr hd) (Option.mem_def.mpr ht)
  · have hm : P.sideCount k = s + 1 := by omega
    have hmod : (s + 1) % P.sideCount k = 0 := by
      rw [hm, Nat.mod_self]
    rw [hmod] at ht
    have hne : (S.diagram.faceBoundary (P.face k)).darts.rotate (P.base k) ≠ [] :=
      List.rotate_eq_nil_iff.not.mpr (S.diagram.faceBoundary (P.face k)).nonempty
    have hclose : S.diagram.toCombMap.facePerm
        (((S.diagram.faceBoundary (P.face k)).darts.rotate (P.base k)).getLast hne) =
          ((S.diagram.faceBoundary (P.face k)).darts.rotate (P.base k)).head hne :=
      Embedded.isChain_rotate_closing (R := fun d e => S.diagram.toCombMap.facePerm d = e)
        (S.diagram.faceBoundary (P.face k)).nonempty (S.diagram.faceBoundary (P.face k)).chain
        (S.diagram.faceBoundary (P.face k)).closes (P.base k) hne
    have hlast : ((S.diagram.faceBoundary (P.face k)).darts.rotate (P.base k)).getLast? =
        some d := by
      rw [P.walk k, hm, List.range_succ, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil,
        List.getLast?_append_of_ne_nil _ (P.side_ne_nil k s hs)]
      exact hd
    have hhead : ((S.diagram.faceBoundary (P.face k)).darts.rotate (P.base k)).head? =
        some t := by
      have h0 : 0 < P.sideCount k := by omega
      rw [P.walk k, hm, List.range_succ_eq_map, List.flatMap_cons,
        List.head?_append_of_ne_nil _ (P.side_ne_nil k 0 h0)]
      exact ht
    exact rel_of_getLast?_of_head? (R := fun d e => S.diagram.toCombMap.facePerm d = e)
      hne hclose hlast hhead

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.SideSuccFace.facePerm_last_core

/-- **Lane gl-p04-03 endpoint: successive sides are contiguous on the polygon face walk.**
For a polygon `k` with class data `Q`, the last dart `d` of side `s` and the first dart `t` of
side `(s + 1) % P.sideCount k` satisfy `φ d = t`. -/
theorem facePerm_last :
    ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
      {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
      {cuts : SectionCuts D lambda c Delta.boundaryWord}
      {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
      {P : OsinLemma94RealizedPolygons S} (_Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
      (s : ℕ), s < P.sideCount k → ∀ (d t : S.diagram.toCombMap.Dart),
        (P.sideDarts k s).getLast? = some d →
        (P.sideDarts k ((s + 1) % P.sideCount k)).head? = some t →
        S.diagram.toCombMap.facePerm d = t := by
  intro G _ Lambda W D lambda c eps Delta cuts S P _ k s hs d t hd ht
  exact facePerm_last_core P k hs hd ht

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.SideSuccFace.facePerm_last

/-- The lane `gl-p04-03` target as a named `Prop`, for dependent lanes that restate it. -/
def SideSuccFaceStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    {P : OsinLemma94RealizedPolygons S} (_Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    (s : ℕ), s < P.sideCount k → ∀ (d t : S.diagram.toCombMap.Dart),
      (P.sideDarts k s).getLast? = some d →
      (P.sideDarts k ((s + 1) % P.sideCount k)).head? = some t →
      S.diagram.toCombMap.facePerm d = t

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.SideSuccFace.SideSuccFaceStatement

/-- **The lane `gl-p04-03` Statement holds** (closed). -/
theorem sideSuccFace : SideSuccFaceStatement.{u, w, v} := by
  intro G _ Lambda W D lambda c eps Delta cuts S P Q k s hs d t hd ht
  exact facePerm_last Q k s hs d t hd ht

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.SideSuccFace.sideSuccFace

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.SideSuccFace
