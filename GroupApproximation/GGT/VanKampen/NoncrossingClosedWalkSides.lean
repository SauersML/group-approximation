import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# Both boundary cycles of a closed walk that touches itself without crossing

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(b):

> "Let us consider the subdiagram `Γ_1` of `Δ` such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2`, where
> `s_1, s_2` are side arcs of some of `Γ_{i,1}`'s and `t_1, t_2` are subpaths of `∂Π` and the
> section `q_1` of `∂Δ`, respectively; (ii) `Γ_1` contains all `Γ_{i,1}`'s."

The walk `s_1 t_1 s_2 t_2` can pass twice through a vertex, and then it is not a simple closed
walk in the sense of `SimpleClosedWalkSides.lean`.  This module keeps the separation argument of
that file and replaces vertex injectivity by a condition at each vertex: rotating from the
reversal of a walk dart, the first dart met on an edge of the walk is a walk dart, not a reversed
walk dart.  At a vertex the walk passes more than once, the retained darts then alternate between
reversed and forward walk darts, so the walk touches itself there but never crosses.

The map on the edges of the walk is connected, since consecutive walk darts meet at one vertex,
and its faces advance along walk darts.  The Jordan-type separation
`CombMap.IsRestriction.faceOf_eq_of_faceClass` then shows that advancing around ambient faces and
crossing edges off the walk never reaches a reversed walk dart from a walk dart.

* `IsNoncrossingClosedWalk`: the walk carrier.
* `IsSimpleClosedWalk.isNoncrossingClosedWalk`: a simple closed walk is noncrossing.
* `IsNoncrossingClosedWalk.innerCycle`, `IsNoncrossingClosedWalk.outerCycle`: the walk is a
  boundary cycle of the faces on its side, and the reversed walk one of the other faces.
* `NoncrossingClosedWalkSidesStatement`, `noncrossingClosedWalkSides`: both boundary cycles, in
  every planar map.

A boundary cycle that passes twice through a vertex need not follow the face-set boundary
(`OsinPocketPinchedTwoGonModel.not_followsBoundary`), so no `FollowsBoundary` claim is made.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv Surgery.MapCollapse SimpleClosedWalkSides

universe u

/-- **A noncrossing closed walk** in a combinatorial map.  The walk is a nonempty list of distinct
darts, each ending where the next starts and the last ending where the first starts, with no edge
used in both directions.  Rotating around a vertex from the reversal `alpha d` of a walk dart `d`,
the first dart met on an edge of the walk is a walk dart. -/
structure IsNoncrossingClosedWalk (M : CombMap.{u}) (w : List M.Dart) : Prop where
  ne_nil : w ≠ []
  nodup : w.Nodup
  chain : w.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e
  closes : M.vertexOf (M.alpha (w.getLast ne_nil)) = M.vertexOf (w.head ne_nil)
  alpha_not_mem : ∀ d ∈ w, M.alpha d ∉ w
  turn_mem : ∀ d ∈ w, ∀ m : ℕ, 0 < m → walkKeep M w ((M.sigma ^ m) (M.alpha d)) →
    (∀ k, 0 < k → k < m → ¬ walkKeep M w ((M.sigma ^ k) (M.alpha d))) →
    (M.sigma ^ m) (M.alpha d) ∈ w

namespace NoncrossingClosedWalkSides

/-- Darts in one rotation cycle are joined by rotation steps. -/
theorem eqvGen_adjacent_of_sameCycle (N : CombMap.{u}) {x y : N.Dart}
    (h : N.sigma.SameCycle x y) : Relation.EqvGen N.Adjacent x y := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have hpow : ∀ (m : ℕ) (z : N.Dart), Relation.EqvGen N.Adjacent z ((N.sigma ^ m) z) := by
    intro m
    induction m with
    | zero => intro z; exact Relation.EqvGen.refl _
    | succ m ih =>
        intro z
        rw [pow_succ, Perm.mul_apply]
        exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ (Or.inr rfl))
          (ih (N.sigma z))
  simpa only [hn] using hpow n x

end NoncrossingClosedWalkSides

open NoncrossingClosedWalkSides

namespace IsSimpleClosedWalk

variable {M : CombMap.{u}} {w : List M.Dart}

/-- **A simple closed walk is noncrossing**: at the vertex where a walk dart `d` ends, the only
retained darts are `alpha d` and the next walk dart. -/
theorem isNoncrossingClosedWalk (hw : IsSimpleClosedWalk M w) : IsNoncrossingClosedWalk M w where
  ne_nil := hw.ne_nil
  nodup := hw.nodup
  chain := hw.chain
  closes := hw.closes
  alpha_not_mem := hw.alpha_not_mem
  turn_mem := by
    intro d hd m hm hkeep havoid
    obtain ⟨b, hb, hdb⟩ := hw.exists_next hd
    obtain ⟨m', hm', hpm', havoid'⟩ :=
      (walkMap_isRestriction M w).sigma_firstReturn ⟨M.alpha d, hw.alpha_keep hd⟩
    have hpb : (M.sigma ^ m') (M.alpha d) = b :=
      hpm'.trans (congrArg Subtype.val (hw.walkMap_sigma_alpha hd hb hdb (hw.alpha_keep hd)))
    rcases lt_trichotomy m m' with hlt | rfl | hgt
    · exact (havoid' m hm hlt ⟨⟨_, hkeep⟩, rfl⟩).elim
    · rw [hpb]
      exact hb
    · exact (havoid m' hm' hgt (by rw [hpb]; exact Or.inl hb)).elim

end IsSimpleClosedWalk

namespace IsNoncrossingClosedWalk

variable {M : CombMap.{u}} {w : List M.Dart}

theorem alpha_keep (_hw : IsNoncrossingClosedWalk M w) {a : M.Dart} (ha : a ∈ w) :
    walkKeep M w (M.alpha a) :=
  Or.inr (by rw [M.alpha_involutive a]; exact ha)

/-- The restricted face permutation sends walk darts to walk darts. -/
theorem walkMap_facePerm_mem (hw : IsNoncrossingClosedWalk M w) (d : (walkMap M w).Dart)
    (hd : d.1 ∈ w) : ((walkMap M w).facePerm d).1 ∈ w := by
  obtain ⟨m, hm, hpm, havoid⟩ :=
    (walkMap_isRestriction M w).sigma_firstReturn ⟨M.alpha d.1, hw.alpha_keep hd⟩
  obtain ⟨z, hz, hzd⟩ : ∃ z : (walkMap M w).Dart,
      (M.sigma ^ m) (M.alpha d.1) = z.1 ∧ (walkMap M w).facePerm d = z :=
    ⟨(walkMap M w).sigma ⟨M.alpha d.1, hw.alpha_keep hd⟩, hpm, rfl⟩
  rw [hzd, ← hz]
  refine hw.turn_mem d.1 hd m hm ?_ fun k hk0 hkm hkeep => havoid k hk0 hkm ⟨⟨_, hkeep⟩, rfl⟩
  rw [hz]
  exact z.2

/-- The map on the edges of the walk is connected. -/
theorem walkMap_connected (hw : IsNoncrossingClosedWalk M w) : (walkMap M w).IsConnected := by
  have hmem : ∀ x ∈ w, ∃ hx : walkKeep M w x, Relation.EqvGen (walkMap M w).Adjacent
      ⟨w.head hw.ne_nil, Or.inl (List.head_mem hw.ne_nil)⟩ ⟨x, hx⟩ := by
    refine List.IsChain.induction (fun x => ∃ hx : walkKeep M w x,
      Relation.EqvGen (walkMap M w).Adjacent
        ⟨w.head hw.ne_nil, Or.inl (List.head_mem hw.ne_nil)⟩ ⟨x, hx⟩)
      w (List.IsChain.iff_mem.mp hw.chain) ?_ ?_
    · rintro x y ⟨hxw, hyw, hxy⟩ ⟨hx, h⟩
      refine ⟨Or.inl hyw, Relation.EqvGen.trans _ _ _ h
        (Relation.EqvGen.trans _ ⟨M.alpha x, hw.alpha_keep hxw⟩ _
          (Relation.EqvGen.rel _ _ (Or.inl rfl)) (eqvGen_adjacent_of_sameCycle _ ?_))⟩
      exact (PermFirstReturn.sameCycle_iff _ _ _ (walkMap_isRestriction M w).sigma_firstReturn
        _ _).mpr ((M.vertexOf_eq_iff _ _).mp hxy)
    · intro lne
      exact ⟨Or.inl (List.head_mem lne), Relation.EqvGen.refl _⟩
  have hall : ∀ x : (walkMap M w).Dart, Relation.EqvGen (walkMap M w).Adjacent
      ⟨w.head hw.ne_nil, Or.inl (List.head_mem hw.ne_nil)⟩ x := by
    rintro ⟨x, hx | hx⟩
    · obtain ⟨_, h⟩ := hmem x hx
      exact h
    · obtain ⟨_, h⟩ := hmem _ hx
      exact Relation.EqvGen.trans _ _ _ h
        (Relation.EqvGen.rel _ _ (Or.inl (Subtype.ext (M.alpha_involutive x))))
  intro d e
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hall d)) (hall e)

/-- **Separation.**  Advancing around ambient faces and crossing edges off the walk never
reaches a reversed walk dart from a walk dart. -/
theorem not_faceClass_alpha (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar) {a d : M.Dart}
    (hd : d ∈ w) (ha : a ∈ w) :
    ¬ Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w)) d (M.alpha a) := by
  intro h
  have h' : Relation.EqvGen
      (CombMap.FaceClassStep M (· ∈ Set.range (Function.Embedding.subtype (walkKeep M w))))
      d (M.alpha a) :=
    faceClass_mono M (fun x hx => by rintro ⟨z, rfl⟩; exact hx z.2) h
  have hface := (walkMap_isRestriction M w).faceOf_eq_of_faceClass hM hw.walkMap_connected
    (d := ⟨d, Or.inl hd⟩) (d' := ⟨M.alpha a, hw.alpha_keep ha⟩) h'
  obtain ⟨n, hn⟩ := (((walkMap M w).faceOf_eq_iff _ _).mp hface).exists_nat_pow_eq
  have hpow : ∀ m : ℕ, (((walkMap M w).facePerm ^ m) ⟨d, Or.inl hd⟩).1 ∈ w := by
    intro m
    induction m with
    | zero => exact hd
    | succ m ih =>
        rw [pow_succ', Perm.mul_apply]
        exact hw.walkMap_facePerm_mem _ ih
  have hmem := hpow n
  rw [hn] at hmem
  exact hw.alpha_not_mem a ha hmem

theorem isBoundaryDart_sideFaces_iff (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (x : M.Dart) : IsBoundaryDart M (sideFaces M w) x ↔ x ∈ w := by
  show M.faceOf x ∈ sideFaces M w ∧ M.faceOf (M.alpha x) ∉ sideFaces M w ↔ x ∈ w
  rw [mem_sideFaces_iff, mem_sideFaces_iff]
  constructor
  · rintro ⟨⟨d, hd, h⟩, hout⟩
    by_contra hx
    by_cases hk : walkKeep M w x
    · rcases hk with hx' | hx'
      · exact hx hx'
      · refine hw.not_faceClass_alpha hM hd hx' ?_
        rw [M.alpha_involutive x]
        exact h
    · exact hout ⟨d, hd, .trans _ _ _ h (.rel _ _ (Or.inr ⟨hk, rfl⟩))⟩
  · intro hx
    exact ⟨⟨x, hx, .refl _⟩, fun ⟨d, hd, h⟩ => hw.not_faceClass_alpha hM hd hx h⟩

theorem isBoundaryDart_sideOutside_iff (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (x : M.Dart) : IsBoundaryDart M (sideOutside M w) x ↔ M.alpha x ∈ w := by
  rw [← hw.isBoundaryDart_sideFaces_iff hM (M.alpha x)]
  show M.faceOf x ∈ sideOutside M w ∧ M.faceOf (M.alpha x) ∉ sideOutside M w ↔
    M.faceOf (M.alpha x) ∈ sideFaces M w ∧ M.faceOf (M.alpha (M.alpha x)) ∉ sideFaces M w
  rw [mem_sideOutside_iff, mem_sideOutside_iff, Classical.not_not, M.alpha_involutive x]
  exact And.comm

/-- The walk is a boundary cycle of the faces on its side. -/
def innerCycle (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar) :
    BoundaryCycle M (sideFaces M w) where
  cycle := w
  cycle_nonempty := hw.ne_nil
  cycle_nodup := hw.nodup
  cycle_mem_iff d := (hw.isBoundaryDart_sideFaces_iff hM d).symm

/-- The reversed walk is a boundary cycle of the faces on the other side. -/
def outerCycle (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar) :
    BoundaryCycle M (sideOutside M w) where
  cycle := w.reverse.map M.alpha
  cycle_nonempty := by simpa using hw.ne_nil
  cycle_nodup := (List.nodup_reverse.mpr hw.nodup).map M.alpha.injective
  cycle_mem_iff d := by
    rw [hw.isBoundaryDart_sideOutside_iff hM d, List.mem_map]
    constructor
    · rintro ⟨e, he, rfl⟩
      rw [M.alpha_involutive e]
      exact List.mem_reverse.mp he
    · intro hd
      exact ⟨M.alpha d, List.mem_reverse.mpr hd, M.alpha_involutive d⟩

end IsNoncrossingClosedWalk

/-- **Both boundary cycles of a noncrossing closed walk.**  For a planar map `M` and a
noncrossing closed walk `w` there are complementary face sets `faces` and `outside` whose boundary
cycles are `w` and the reversed walk `w.reverse.map M.alpha`. -/
def NoncrossingClosedWalkSidesStatement : Prop :=
  ∀ (M : CombMap.{u}) (w : List M.Dart), M.IsPlanar → IsNoncrossingClosedWalk M w →
    ∃ (faces outside : Finset M.Face) (inner : BoundaryCycle M faces)
      (outer : BoundaryCycle M outside),
      (∀ f, f ∈ outside ↔ f ∉ faces) ∧ inner.cycle = w ∧ outer.cycle = w.reverse.map M.alpha

theorem noncrossingClosedWalkSides : NoncrossingClosedWalkSidesStatement.{u} := by
  intro M w hM hw
  exact ⟨sideFaces M w, sideOutside M w, hw.innerCycle hM, hw.outerCycle hM,
    mem_sideOutside_iff M w, rfl, rfl⟩

end GroupApproximation.GGT.VanKampen

#audit_closed_axioms GroupApproximation.GGT.VanKampen.noncrossingClosedWalkSides
#audit_axioms GroupApproximation.GGT.VanKampen.IsSimpleClosedWalk.isNoncrossingClosedWalk
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.not_faceClass_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.isBoundaryDart_sideFaces_iff
