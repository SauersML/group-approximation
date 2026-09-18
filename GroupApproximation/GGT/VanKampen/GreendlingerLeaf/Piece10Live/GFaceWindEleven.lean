import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindElevenEnd
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'`: inner lobes except for a non-adjacent inside chord

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-70.

## Route

`gfaceWindTen_Statement` asks, at a residual state, for an inner lobe `W'` of each non-clean
lobe `W` of `c`. Write `c = X₁ ++ X₂` with `X₂ ++ X₁ = W ++ T`, where `T` has the darts of the
rest (`gfaceWindEleven_rest`). A stretch `Q` of `T` is *inside* when each of its darts has its
face on the side of `W`. The following cases are proved here and each yields `W'`:
* some dart of `T` is inside (`gfaceWindEleven_inside`, from non-cleanness);
* an inside stretch repeats a vertex (`gfaceWindEleven_e1`);
* an inside stretch closes up (`gfaceWindEleven_e2`);
* an inside prefix of `T` with inner vertices off `W` ends on `W` (`gfaceWindEleven_adjStart`);
* an inside suffix of `T` with inner vertices off `W` starts on `W` (`gfaceWindEleven_adjEnd`).
`gfaceWindEleven_Statement` is `gfaceWindTen_Statement` with the negations of these cases as
extra hypotheses, and `gfaceWindEleven_ten` is the reduction.

## Strength (LOUD)

**As a proposition, `gfaceWindEleven_Statement` is WEAKER than `gfaceWindTen_Statement`**: it is
Ten with extra hypotheses (`gfaceWindEleven_of_ten`). With `gfaceWindEleven_ten`, the two are
**interderivable, hence EQUIVALENT as propositions**. What shrinks is the proof content: every
case above is discharged, so only this remains.

**Remaining gap.** Inside darts exist, and no inside stretch repeats a vertex or closes. Every
inside prefix or suffix that meets `W` does so at an inner vertex, so a maximal inside
stretch runs strictly inside `T` as a simple chord between two distinct vertices of `W`. Closing
this case needs a Jordan-type argument that uses `h1`/`h2`.

## Truth check

Scratchpad `gl-p10-70/elevencheck.py` extends `gl-p10-68/ten.py`. At every residual state, for
every non-clean lobe, it tests literally the five extra hypotheses and the conclusion. The runs
were 200 s each:

| run         | inst   | res    | nonclean |
| ----------- | ------ | ------ | -------- |
| rand seed 1 | 305949 | 557356 | 276648   |
| wit seed 2  | 252162 | 597650 | 290085   |
| rand seed 3 | 333115 | 512709 | 293099   |

That is 1667715 residual states and 859832 non-clean lobes. The results:
* `T1` holds on every non-clean lobe;
* `INFAIL` = 0 (non-clean implies an inside dart);
* `EASYFAIL` = 0 (the proved cases);
* `RESID` = 0: no tested lobe satisfies all extra hypotheses, so the residual is vacuous there.

The hand map is also 0/0/0.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10ExtremalWrap GFaceChoose
open scoped Classical

/-- **Inner lobes at a non-adjacent inside chord** (residual of `gfaceWindTen_Statement`): its
hypotheses, a rotation `W ++ T` of `c`, an inside dart of `T`, and the negations of the cases
`e1`, `e2`, `adjStart`, `adjEnd`. -/
def gfaceWindEleven_Statement : Prop :=
  ∀ (M : CombMap.{v}), M.IsPlanar → ∀ (C : List M.Dart) (F : Finset M.Face) (o : M.Face),
    C.Nodup → (∀ d, Surgery.MapCollapse.IsBoundaryDart M F d ↔ d ∈ C) →
    C.IsChain (fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) → gfaceWindSix_Bal M C →
    o ∉ F → ∀ (c : List M.Dart) (g : M.Face → ℤ),
      Relation.ReflTransGen (gfaceWind_Step M o) (C, gfaceWind_ind F) (c, g) →
      (∀ f, 0 ≤ g f) → ¬ (c.map M.vertexOf).Nodup →
      (¬ ∃ p A q : List M.Dart, c = p ++ A ++ q ∧ IsSimpleClosedWalk M A ∧
        o ∈ SimpleClosedWalkSides.sideFaces M A) →
      (¬ ∃ p A q : List M.Dart, c = p ++ A ++ q ∧ IsSimpleClosedWalk M (q ++ p) ∧
        o ∈ SimpleClosedWalkSides.sideFaces M (q ++ p)) →
      (¬ ∃ p A q : List M.Dart, c = p ++ A ++ q ∧ IsSimpleClosedWalk M A ∧
        IsSimpleClosedWalk M (q ++ p)) →
      ∀ W R : List M.Dart, gfaceWindEight_Lobe M c W R → ¬ gfaceWindEight_Clean M W R →
      ∀ X₁ X₂ T : List M.Dart, c = X₁ ++ X₂ → X₂ ++ X₁ = W ++ T → (∀ x, x ∈ R ↔ x ∈ T) →
      (∃ r ∈ T, M.faceOf r ∈ SimpleClosedWalkSides.sideFaces M W) →
      (∀ X Q Y : List M.Dart, T = X ++ Q ++ Y →
        (∀ x ∈ Q, M.faceOf x ∈ SimpleClosedWalkSides.sideFaces M W) →
        (Q.map M.vertexOf).Nodup) →
      (∀ (X Q Y : List M.Dart) (hQ : Q ≠ []), T = X ++ Q ++ Y →
        (∀ x ∈ Q, M.faceOf x ∈ SimpleClosedWalkSides.sideFaces M W) →
        M.vertexOf (M.alpha (Q.getLast hQ)) ≠ M.vertexOf (Q.head hQ)) →
      (∀ (Q Y : List M.Dart) (hQ : Q ≠ []), T = Q ++ Y →
        (∀ x ∈ Q, M.faceOf x ∈ SimpleClosedWalkSides.sideFaces M W) →
        (∀ x ∈ Q.tail, M.vertexOf x ∉ W.map M.vertexOf) →
        M.vertexOf (M.alpha (Q.getLast hQ)) ∉ W.map M.vertexOf) →
      (∀ (X Q : List M.Dart) (hQ : Q ≠ []), T = X ++ Q →
        (∀ x ∈ Q, M.faceOf x ∈ SimpleClosedWalkSides.sideFaces M W) →
        (∀ x ∈ Q.tail, M.vertexOf x ∉ W.map M.vertexOf) →
        M.vertexOf (Q.head hQ) ∉ W.map M.vertexOf) →
          ∃ W' R' : List M.Dart, gfaceWindEight_Lobe M c W' R' ∧
            (∀ x ∈ W', M.faceOf x ∈ SimpleClosedWalkSides.sideFaces M W) ∧
              ∃ x ∈ W', x ∉ W

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindEleven_Statement

/-- **The residual is weaker than `gfaceWindTen_Statement`** (it only adds hypotheses). -/
theorem gfaceWindEleven_of_ten (h : gfaceWindTen_Statement.{v}) :
    gfaceWindEleven_Statement.{v} :=
  fun M hM C F o hC hS hch hbal ho c g hr hpos hnd h1 h2 h3 W R hl hnc _ _ _ _ _ _ _ _ _ _ _ =>
    h M hM C F o hC hS hch hbal ho c g hr hpos hnd h1 h2 h3 W R hl hnc

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindEleven_of_ten

/-- **Reduction of `gfaceWindTen_Statement` to the non-adjacent inside chord.** -/
theorem gfaceWindEleven_ten (h : gfaceWindEleven_Statement.{v}) :
    gfaceWindTen_Statement.{v} := by
  intro M hM C F o hC hS hch hbal ho c g hr hpos hnd h1 h2 h3 W R hl hnc
  have hinv : gfaceWind_Inv M C o c g :=
    gfaceWindSix_inv_rt (s := (C, gfaceWind_ind F)) (t := (c, g)) hM hC hr
      (gfaceWind_inv_start hS hch ho)
  have hsub : ∀ x ∈ c, x ∈ C := by
    intro x hx
    have hx' : x ∈ C.filter (gfaceWind_mem c) := by
      rw [hinv.1]
      exact hx
    exact (List.mem_filter.mp hx').1
  have hal : ∀ x ∈ c, M.alpha x ∉ c := fun x hx hax =>
    ((hS x).mpr (hsub x hx)).2 ((hS _).mpr (hsub _ hax)).1
  have hbc : gfaceWindSix_Bal M c :=
    gfaceWindSix_bal_reach (s := (C, gfaceWind_ind F)) (t := (c, g)) hr hbal
  have hcnd : c.Nodup := by
    have h0 := List.Nodup.filter (gfaceWind_mem c) hC
    rw [hinv.1] at h0
    exact h0
  obtain ⟨X₁, X₂, T, hc, hZ, hRT⟩ := gfaceWindEleven_rest hl
  have hperm : c.Perm (W ++ T) := by
    rw [hc, ← hZ]
    exact List.perm_append_comm
  have hZnd : (W ++ T).Nodup := hperm.nodup_iff.mp hcnd
  have halZ : ∀ x ∈ W ++ T, M.alpha x ∉ W ++ T := fun x hx hax =>
    hal x (hperm.mem_iff.mpr hx) (hperm.mem_iff.mpr hax)
  have hdis : ∀ x ∈ T, x ∉ W := fun x hxT hxW =>
    (List.nodup_append.mp hZnd).2.2 x hxW x hxT rfl
  have hW : IsSimpleClosedWalk M W := gfaceWindTen_lobe_simple hl
  have hchZ : (W ++ T).IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e := by
    rw [← hZ]
    exact gfaceWindEleven_cycChain (by rw [← hc]; exact hinv.2.1) (by rw [← hc]; exact hbc)
  obtain ⟨Y₁, Y₂, hY, hY2⟩ := gfaceWindEleven_rotate hZ
  have hc' : c = Y₁ ++ Y₂ := hc.trans hY
  have hchZ' : (T ++ W).IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e := by
    rw [← hY2]
    exact gfaceWindEleven_cycChain (by rw [← hc']; exact hinv.2.1) (by rw [← hc']; exact hbc)
  have hlobe : ∀ P L S : List M.Dart, W ++ T = P ++ L ++ S → IsSimpleClosedWalk M L →
      ∃ R : List M.Dart, gfaceWindEight_Lobe M c L R := fun P L S hs hL =>
    gfaceWindEleven_segLobe hc (hZ.trans hs) hL
  have hlobe' : ∀ P L S : List M.Dart, T ++ W = P ++ L ++ S → IsSimpleClosedWalk M L →
      ∃ R : List M.Dart, gfaceWindEight_Lobe M c L R := fun P L S hs hL =>
    gfaceWindEleven_segLobe hc' (hY2.trans hs) hL
  have hWR : ∀ x ∈ W, M.alpha x ∉ R := fun x hx hax =>
    halZ x (List.mem_append_left T hx) (List.mem_append_right W ((hRT _).mp hax))
  have hin : ∃ r ∈ T, M.faceOf r ∈ SimpleClosedWalkSides.sideFaces M W := by
    obtain ⟨r, hrR, hrf⟩ := gfaceWindEleven_inside hM hW hWR hnc
    exact ⟨r, (hRT r).mp hrR, hrf⟩
  by_contra hgoal
  have hE1 : ∀ X Q Y : List M.Dart, T = X ++ Q ++ Y →
      (∀ x ∈ Q, M.faceOf x ∈ SimpleClosedWalkSides.sideFaces M W) →
      (Q.map M.vertexOf).Nodup := by
    intro X Q Y hT hQ
    by_contra hrep
    exact hgoal (gfaceWindEleven_e1 hchZ halZ hdis hlobe hT hQ hrep)
  have hE2 : ∀ (X Q Y : List M.Dart) (hQ : Q ≠ []), T = X ++ Q ++ Y →
      (∀ x ∈ Q, M.faceOf x ∈ SimpleClosedWalkSides.sideFaces M W) →
      M.vertexOf (M.alpha (Q.getLast hQ)) ≠ M.vertexOf (Q.head hQ) := by
    intro X Q Y hQ0 hT hQ hcl
    exact hgoal (gfaceWindEleven_e2 hchZ halZ hdis hlobe hT hQ0 hQ (hE1 X Q Y hT hQ) hcl)
  have hST : ∀ (Q Y : List M.Dart) (hQ : Q ≠ []), T = Q ++ Y →
      (∀ x ∈ Q, M.faceOf x ∈ SimpleClosedWalkSides.sideFaces M W) →
      (∀ x ∈ Q.tail, M.vertexOf x ∉ W.map M.vertexOf) →
      M.vertexOf (M.alpha (Q.getLast hQ)) ∉ W.map M.vertexOf := by
    intro Q Y hQ0 hT hQ hint hend
    have hT' : T = [] ++ Q ++ Y := by rw [hT, List.nil_append]
    exact hgoal (gfaceWindEleven_adjStart hW hchZ halZ hdis hlobe hT hQ0 hQ
      (hE1 [] Q Y hT' hQ) (hE2 [] Q Y hQ0 hT' hQ) hint hend)
  have hEN : ∀ (X Q : List M.Dart) (hQ : Q ≠ []), T = X ++ Q →
      (∀ x ∈ Q, M.faceOf x ∈ SimpleClosedWalkSides.sideFaces M W) →
      (∀ x ∈ Q.tail, M.vertexOf x ∉ W.map M.vertexOf) →
      M.vertexOf (Q.head hQ) ∉ W.map M.vertexOf := by
    intro X Q hQ0 hT hQ hint hst
    have hT' : T = X ++ Q ++ [] := by rw [hT, List.append_nil]
    exact hgoal (gfaceWindEleven_adjEnd hW hchZ' halZ hdis hlobe' hT hQ0 hQ
      (hE1 X Q [] hT' hQ) (hE2 X Q [] hQ0 hT' hQ) hint hst)
  exact hgoal (h M hM C F o hC hS hch hbal ho c g hr hpos hnd h1 h2 h3 W R hl hnc
    X₁ X₂ T hc hZ hRT hin hE1 hE2 hST hEN)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindEleven_ten

/-- **The positive step from the residual** (`gfaceWindTen_posStep`). -/
theorem gfaceWindEleven_posStep (h : gfaceWindEleven_Statement.{v}) :
    gfaceWindSix_PosStep.{v} :=
  gfaceWindTen_posStep (gfaceWindEleven_ten h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindEleven_posStep

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind
