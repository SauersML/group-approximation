import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketLakeAbsorption
import GroupApproximation.GGT.VanKampen.ClosedWalkLobeExcision
import GroupApproximation.Meta.AxiomGuard

/-!
# Separated lobes of a boundary cycle

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  This module holds the map-level part of the rose case of the
outer-pinch step (`P10ChordLift.RoseStepStatement`).

## The mathematics

Let `faces` be a finite set of faces of a combinatorial map `M` and `c` a list of darts whose
members are exactly the boundary darts of `faces` (a `BoundaryCycle`).  Write `R` for the
face-class relation `FaceClassStep M (walkKeep M c)`: move around a face, or cross an edge off
`c`.

1. *A face-class chain does not change membership in `faces`.*  An edge off `c` is not a boundary
   edge of `faces`, so both of its faces are in `faces` or both are out
   (`faceOf_mem_iff_of_walkEqvGen`, from `ExteriorComponent.faceOf_mem_iff_of_eqvGen`).
2. *The faces of a lobe.*  For a sublist `L` of `c`, `lobeFaces M c L` is the set of faces reached
   by `R` from a dart of `L`.  By (1) these faces lie in `faces` (`mem_faces_of_mem_lobeFaces`).
3. *The boundary of a lobe.*  Call `L` *closed* when every dart of `c` that is `R`-related to a
   dart of `L` lies in `L`.  Then the boundary darts of `lobeFaces M c L` are exactly the darts of
   `L` (`isBoundaryDart_lobeFaces_iff`).  A dart `e ∈ L` has its face in the lobe, and the face
   across `e` is outside `faces`, hence outside the lobe.  Conversely let `e` be a boundary dart of
   the lobe, reached from `d ∈ L`.  If `e ∈ c` then `e ∈ L` by closedness.  If `alpha e ∈ c` then
   the face of `e` is off `faces`, since `alpha e` is a boundary dart of `faces`; but by (1) it is
   in `faces`, a contradiction.  Otherwise `e` is off the walk, so `R` crosses to `alpha e`, and
   the face across `e` is in the lobe, a contradiction.  So a closed nonempty duplicate-free `L`
   is a `BoundaryCycle` of its lobe (`lobeBoundary`).
4. *Every face of `faces` is in some lobe*, when `M` is connected and `c ≠ []`
   (`exists_mem_eqvGen_of_faceOf_mem`).  Suppose the face of `x` is in `faces` and no dart of `c`
   is `R`-related to `x`.  Every `y` related to `x` is then off the walk: `y ∈ c` is excluded by
   assumption, and `alpha y ∈ c` would put the face of `y` off `faces`, against (1).  So the class
   of `x` is closed under `alpha`, and under `sigma = facePerm ∘ alpha`.  By connectedness it is
   everything, and contains the head of `c`: a contradiction.
5. *Splitting the cycle.*  If `c` is a permutation of `L ++ L'` with `L` closed, then `L'` is
   closed (`closed_right`), and every face of `faces` is in the lobe of `L` or of `L'`
   (`mem_lobeFaces_or`).  The repeated visits `length - #vertices` strictly drop from `c` to `L`
   when some dart of `L` and some dart of `L'` start at one vertex (`length_sub_card_lt`).
6. *Walk order.*  A closed dart walk `P ++ Q` whose two parts start at one vertex splits into the
   closed dart walks `P` and `Q` (`closedDartWalk_split`).

## The rose step from a separated lobe (module `P10Rose/Proof`)

Let `K` be a pocket face set in walk order with cycle `s_1 t_1 s_2 t_2`, and suppose a sub-walk
`B` of a side `s_i` is closed in the sense of (3) and starts at the vertex where it ends.  By (5)
the relator cell `kept` lies in the lobe of `B` or in the lobe of the rest `A ++ C` of the cycle.
In the first case `B` alone, with zero arcs, is a pocket face set; in the second the rest, with
`B` cut out of its side, is one.  Both are in walk order by (6), keep proper arcs, have sides no
longer than those of `K` (so their norms stay below `ε` by letter labels), and have strictly fewer
repeated visits by (5).

## The remaining gap for `P10ChordLift.RoseStepStatement`

The rose hypothesis `AllNonFirstTurnsCrossed K` does not produce a closed sub-walk of a side.
Take a vertex `v` visited three times by the cycle, with two lakes `H_1`, `H_2` (face sets
outside `K`) touching `∂K` only at `v`, and rotation around `v`
`ā[K] x[H_1] ȳ[K] y'[H_2] z̄[K] z[ext]`, the walk order being `P_ext P_{H_2} P_{H_1}`.  Every
non-first turn at `v` is crossed by another passage, yet no lobe of the cycle cut at `v` is closed
under `R`: each lobe shares the face class of a lake edge with another lobe.  The statement is not
refuted by this configuration (filling the lakes first changes `K`), but closing it needs one of:

* the lake absorption `PocketFaceSet.absorb` together with walk order for the absorbed cycle
  (not proved in `Estimating/OsinPocketLakeAbsorption`);
* cuts at vertices inside the arcs `t_1`, `t_2`, which leave the four-part shape;
* cuts across `t_2` wrapping the base position, which break `lo ≤ targetArc.start`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose

universe v

open Surgery.MapCollapse SimpleClosedWalkSides

/-- **The faces of a lobe**: the faces reached from a dart of `L` by moving around faces and
crossing edges off the walk `c`. -/
noncomputable def lobeFaces (M : CombMap.{v}) (c L : List M.Dart) : Finset M.Face := by
  classical
  exact Finset.univ.filter fun f => ∃ x, M.faceOf x = f ∧
    ∃ d ∈ L, Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) d x

theorem mem_lobeFaces_iff (M : CombMap.{v}) (c L : List M.Dart) (x : M.Dart) :
    M.faceOf x ∈ lobeFaces M c L ↔
      ∃ d ∈ L, Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) d x := by
  classical
  unfold lobeFaces
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨-, y, hy, d, hd, h⟩
    exact ⟨d, hd, .trans _ _ _ h
      (eqvGen_faceClass_of_sameCycle M _ ((M.faceOf_eq_iff y x).mp hy))⟩
  · rintro ⟨d, hd, h⟩
    exact ⟨Finset.mem_univ _, x, rfl, d, hd, h⟩

section Lobes

variable {M : CombMap.{v}}

/-- **A face-class chain of a boundary cycle keeps membership in the face set.** -/
theorem faceOf_mem_iff_of_walkEqvGen {faces : Finset M.Face} {c : List M.Dart}
    (hc : ∀ d, d ∈ c ↔ IsBoundaryDart M faces d) {x y : M.Dart}
    (h : Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) x y) :
    M.faceOf x ∈ faces ↔ M.faceOf y ∈ faces :=
  Surgery.MapCollapse.ExteriorComponent.faceOf_mem_iff_of_eqvGen
    (SimpleClosedWalkSides.faceClass_mono M (keep := walkKeep M c)
      (keep' := Surgery.MapCollapse.ExteriorComponent.BoundaryEdge M faces)
      (fun z hz hb => hz (Or.elim hb (fun hb => Or.inl ((hc z).mpr hb))
        (fun hb => Or.inr ((hc _).mpr hb)))) h)

/-- The faces of a lobe of a boundary cycle lie in the face set. -/
theorem mem_faces_of_mem_lobeFaces {faces : Finset M.Face} {c L : List M.Dart}
    (hc : ∀ d, d ∈ c ↔ IsBoundaryDart M faces d) (hL : ∀ d ∈ L, d ∈ c) {f : M.Face}
    (hf : f ∈ lobeFaces M c L) : f ∈ faces := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep f
  obtain ⟨d, hd, h⟩ := (mem_lobeFaces_iff M c L x).mp hf
  exact (faceOf_mem_iff_of_walkEqvGen hc h).mp ((hc d).mp (hL d hd)).1

/-- **The boundary of a closed lobe is the lobe.** -/
theorem isBoundaryDart_lobeFaces_iff {faces : Finset M.Face} {c L : List M.Dart}
    (hc : ∀ d, d ∈ c ↔ IsBoundaryDart M faces d) (hL : ∀ d ∈ L, d ∈ c)
    (hclosed : ∀ d ∈ L, ∀ e ∈ c,
      Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) d e → e ∈ L) (e : M.Dart) :
    IsBoundaryDart M (lobeFaces M c L) e ↔ e ∈ L := by
  constructor
  · rintro ⟨he, hae⟩
    obtain ⟨d, hd, h⟩ := (mem_lobeFaces_iff M c L e).mp he
    by_cases hk : walkKeep M c e
    · rcases hk with hk | hk
      · exact hclosed d hd e hk h
      · exfalso
        have hin : M.faceOf e ∈ faces :=
          (faceOf_mem_iff_of_walkEqvGen hc h).mp ((hc d).mp (hL d hd)).1
        exact ((hc _).mp hk).2 (by rw [M.alpha_involutive e]; exact hin)
    · exact absurd ((mem_lobeFaces_iff M c L (M.alpha e)).mpr
        ⟨d, hd, .trans _ _ _ h (.rel _ _ (Or.inr ⟨hk, rfl⟩))⟩) hae
  · intro he
    exact ⟨(mem_lobeFaces_iff M c L e).mpr ⟨e, he, .refl _⟩,
      fun hae => ((hc e).mp (hL e he)).2 (mem_faces_of_mem_lobeFaces hc hL hae)⟩

/-- **The boundary cycle of a closed lobe.** -/
noncomputable def lobeBoundary {faces : Finset M.Face} {c L : List M.Dart}
    (hc : ∀ d, d ∈ c ↔ IsBoundaryDart M faces d) (hL : ∀ d ∈ L, d ∈ c)
    (hclosed : ∀ d ∈ L, ∀ e ∈ c,
      Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) d e → e ∈ L)
    (hne : L ≠ []) (hnd : L.Nodup) : BoundaryCycle M (lobeFaces M c L) where
  cycle := L
  cycle_nonempty := hne
  cycle_nodup := hnd
  cycle_mem_iff := fun e => (isBoundaryDart_lobeFaces_iff hc hL hclosed e).symm

/-- **Every face of the face set is reached from the boundary cycle**, in a connected map. -/
theorem exists_mem_eqvGen_of_faceOf_mem (hM : M.IsConnected) {faces : Finset M.Face}
    {c : List M.Dart} (hc : ∀ d, d ∈ c ↔ IsBoundaryDart M faces d) (hne : c ≠ [])
    {x : M.Dart} (hx : M.faceOf x ∈ faces) :
    ∃ d ∈ c, Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) d x := by
  by_contra hno
  have hP : ∀ y, Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) x y →
      Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) x (M.alpha y) := by
    intro y hy
    have hyin : M.faceOf y ∈ faces := (faceOf_mem_iff_of_walkEqvGen hc hy).mp hx
    have hk : ¬ walkKeep M c y := by
      rintro (hk | hk)
      · exact hno ⟨y, hk, .symm _ _ hy⟩
      · exact ((hc _).mp hk).2 (by rw [M.alpha_involutive y]; exact hyin)
    exact .trans _ _ _ hy (.rel _ _ (Or.inr ⟨hk, rfl⟩))
  have hface : ∀ y, M.facePerm (M.alpha y) = M.sigma y := fun y => by
    show M.sigma (M.alpha (M.alpha y)) = M.sigma y
    rw [M.alpha_involutive y]
  have hA : ∀ a b, M.Adjacent a b →
      (Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) x a ↔
        Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) x b) := by
    intro a b hab
    have h2 : Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) (M.alpha a) (M.sigma a) := by
      rw [← hface a]
      exact .rel _ _ (Or.inl rfl)
    rcases hab with rfl | rfl
    · refine ⟨hP a, fun h => ?_⟩
      have h' := hP _ h
      rwa [M.alpha_involutive a] at h'
    · refine ⟨fun h => .trans _ _ _ (hP a h) h2, fun h => ?_⟩
      have h' := hP _ (.trans _ _ _ h (.symm _ _ h2))
      rwa [M.alpha_involutive a] at h'
  have hall : ∀ a b, Relation.EqvGen M.Adjacent a b →
      (Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) x a ↔
        Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) x b) := by
    intro a b h
    induction h with
    | rel a₁ a₂ hab => exact hA a₁ a₂ hab
    | refl _ => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have hd := (hall x (c.head hne) (hM x (c.head hne))).mp (.refl _)
  exact hno ⟨c.head hne, List.head_mem hne, .symm _ _ hd⟩

/-- **The complement of a closed lobe is closed.** -/
theorem closed_right {c L L' : List M.Dart} (hperm : List.Perm c (L ++ L')) (hnd : c.Nodup)
    (hL : ∀ d ∈ L, ∀ e ∈ c,
      Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) d e → e ∈ L) :
    ∀ d ∈ L', ∀ e ∈ c,
      Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) d e → e ∈ L' := by
  intro d hd e he h
  obtain ⟨-, -, hdisj⟩ := List.nodup_append.mp (hnd.perm hperm)
  rcases List.mem_append.mp (hperm.mem_iff.mp he) with heL | heL'
  · exact absurd (hL e heL d (hperm.mem_iff.mpr (List.mem_append_right L hd)) (.symm _ _ h))
      (fun hdL => hdisj d hdL d hd rfl)
  · exact heL'

/-- **Every face of the face set lies in one of two complementary lobes**, in a connected map. -/
theorem mem_lobeFaces_or (hM : M.IsConnected) {faces : Finset M.Face} {c L L' : List M.Dart}
    (hc : ∀ d, d ∈ c ↔ IsBoundaryDart M faces d) (hne : c ≠ []) (hperm : List.Perm c (L ++ L'))
    {f : M.Face} (hf : f ∈ faces) : f ∈ lobeFaces M c L ∨ f ∈ lobeFaces M c L' := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep f
  obtain ⟨d, hd, h⟩ := exists_mem_eqvGen_of_faceOf_mem hM hc hne (x := x) hf
  rcases List.mem_append.mp (hperm.mem_iff.mp hd) with hdL | hdL'
  · exact Or.inl ((mem_lobeFaces_iff M c L x).mpr ⟨d, hdL, h⟩)
  · exact Or.inr ((mem_lobeFaces_iff M c L' x).mpr ⟨d, hdL', h⟩)

/-- **A closed dart walk splits at a repeated vertex** into two closed dart walks. -/
theorem closedDartWalk_split {P Q : List M.Dart} (hw : IsClosedDartWalk M (P ++ Q))
    (hP : P ≠ []) (hQ : Q ≠ []) (hv : M.vertexOf (P.head hP) = M.vertexOf (Q.head hQ)) :
    IsClosedDartWalk M P ∧ IsClosedDartWalk M Q := by
  obtain ⟨d, X, rfl⟩ := List.exists_cons_of_ne_nil hP
  obtain ⟨e, Y, rfl⟩ := List.exists_cons_of_ne_nil hQ
  obtain ⟨-, hcc⟩ := isClosedDartWalk_iff_closedChain.mp hw
  have hv' : M.vertexOf d = M.vertexOf e := hv
  obtain ⟨h₁, h₂⟩ := ClosedWalkFaceColouring.closedChain_split
    (R := fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (fun x => by
      show M.vertexOf (M.alpha x) = M.vertexOf d ↔ M.vertexOf (M.alpha x) = M.vertexOf e
      rw [hv']) hcc
  exact ⟨isClosedDartWalk_iff_closedChain.mpr ⟨List.cons_ne_nil _ _, h₁⟩,
    isClosedDartWalk_iff_closedChain.mpr ⟨List.cons_ne_nil _ _, h₂⟩⟩

end Lobes

/-- **Cutting a list at a repeated value lowers its repeats.**  If `l` is a permutation of
`l₁ ++ l₂` and `f` takes one value on a member of `l₁` and a member of `l₂`, then `l₁` has
strictly fewer repeats of `f` than `l`. -/
theorem length_sub_card_lt {α β : Type*} {_ : DecidableEq β} (f : α → β) {l l₁ l₂ : List α}
    (hperm : List.Perm l (l₁ ++ l₂)) {x y : α} (hx : x ∈ l₁) (hy : y ∈ l₂) (hxy : f x = f y) :
    l₁.length - (l₁.map f).toFinset.card < l.length - (l.map f).toFinset.card := by
  have hlen : l.length = l₁.length + l₂.length := by
    rw [hperm.length_eq, List.length_append]
  have hfin : (l.map f).toFinset = (l₁.map f).toFinset ∪ (l₂.map f).toFinset := by
    rw [List.toFinset_eq_of_perm _ _ (hperm.map f), List.map_append, List.toFinset_append]
  have hI : 0 < ((l₁.map f).toFinset ∩ (l₂.map f).toFinset).card :=
    Finset.card_pos.mpr ⟨f x, Finset.mem_inter.mpr
      ⟨List.mem_toFinset.mpr (List.mem_map_of_mem hx),
        List.mem_toFinset.mpr (by rw [hxy]; exact List.mem_map_of_mem hy)⟩⟩
  have hU := Finset.card_union_add_card_inter (l₁.map f).toFinset (l₂.map f).toFinset
  have hA := List.toFinset_card_le (l₁.map f)
  have hB := List.toFinset_card_le (l₂.map f)
  rw [List.length_map] at hA hB
  rw [hlen, hfin]
  omega

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.lobeFaces
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.mem_lobeFaces_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.faceOf_mem_iff_of_walkEqvGen
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.mem_faces_of_mem_lobeFaces
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.isBoundaryDart_lobeFaces_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.lobeBoundary
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.exists_mem_eqvGen_of_faceOf_mem
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.closed_right
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.mem_lobeFaces_or
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.closedDartWalk_split
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.length_sub_card_lt
