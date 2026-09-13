import GroupApproximation.GGT.VanKampen.CombMapRestrictionFaceClasses
import GroupApproximation.GGT.VanKampen.SurgeryReclosedPlanarity
import GroupApproximation.Meta.AxiomGuard

/-!
# Both sides of a simple closed walk in a planar map are disc regions

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(b):

> "Let us consider the subdiagram `Γ_1` of `Δ` such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2`, where
> `s_1, s_2` are side arcs of some of `Γ_{i,1}`'s and `t_1, t_2` are subpaths of `∂Π` and the
> section `q_1` of `∂Δ`, respectively; (ii) `Γ_1` contains all `Γ_{i,1}`'s."

The closed walk `s_1 t_1 s_2 t_2` cuts the diagram, and both the subdiagram and its complement
are then used as discs.  This module proves the Jordan-type fact behind that step for an actual
combinatorial map: a closed walk that starts no two of its darts at the same vertex and never
uses an edge in both directions bounds a disc region on each side.

The proof restricts the map to the edges of the walk (`CombMap.PredicateRestriction`).  At each
vertex of the walk exactly two retained darts remain, so the restricted vertex rotation swaps
them: the restriction is connected and its faces advance along the walk.  The Jordan-type
separation `CombMap.IsRestriction.faceOf_eq_of_faceClass` (face classes of a connected planar
restriction) shows that advancing around ambient faces and crossing edges off the walk never
reaches a reversed walk dart from a walk dart.  The faces reached from the walk this way form one
side, the remaining faces the other.  The boundary darts of the first side are the walk, those of
the second the reversed walk, and the first-return steps of the vertex rotation are boundary
walks, so `BoundaryCycle.toDiscRegion_of_followsBoundary` produces both disc regions with both
topology fields proved.

* `IsSimpleClosedWalk`: the walk carrier.
* `SimpleClosedWalkSidesStatement`, `simpleClosedWalkSides`: both sides are disc regions, with
  boundary cycles the walk and the reversed walk.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv Surgery.MapCollapse

universe u v

/-- **A simple closed walk** in a combinatorial map.  A dart `d` starts at `vertexOf d` and ends
at `vertexOf (alpha d)`.  The walk is a nonempty list of darts, each ending where the next starts
and the last ending where the first starts, with no two darts starting at the same vertex and no
edge used in both directions. -/
structure IsSimpleClosedWalk (M : CombMap.{u}) (w : List M.Dart) : Prop where
  ne_nil : w ≠ []
  chain : w.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e
  closes : M.vertexOf (M.alpha (w.getLast ne_nil)) = M.vertexOf (w.head ne_nil)
  vertex_nodup : (w.map M.vertexOf).Nodup
  alpha_not_mem : ∀ d ∈ w, M.alpha d ∉ w

namespace SimpleClosedWalkSides

/-- If `p` returns from `e b` only to `e b` and `e c` among the points of the image of `e`, and
`b ≠ c`, then the first return from `b` is `c`. -/
theorem firstReturn_eq_of_two {A : Type u} {B : Type v} [Finite A] (p : Perm A) (q : Perm B)
    (e : B ↪ A) (h : PermFirstReturn.IsFirstReturn p q e) {b c : B} (hbc : b ≠ c)
    (hsame : p.SameCycle (e b) (e c))
    (honly : ∀ d, p.SameCycle (e b) (e d) → d = b ∨ d = c) : q b = c := by
  obtain ⟨m, hm, hpm, havoid⟩ := h b
  rcases honly (q b) ⟨(m : ℤ), by rw [zpow_natCast]; exact hpm⟩ with hfix | hc
  · exfalso
    obtain ⟨j, hj⟩ := hsame.exists_nat_pow_eq
    have hpow : (p ^ m) (e b) = e b := by rw [hpm, hfix]
    have hmul : ∀ n : ℕ, (p ^ (m * n)) (e b) = e b := fun n => by
      rw [pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hpow n
    rw [← Nat.mod_add_div j m, pow_add, Perm.mul_apply, hmul] at hj
    by_cases hz : j % m = 0
    · rw [hz, pow_zero, Perm.one_apply] at hj
      exact hbc (e.injective hj)
    · exact havoid (j % m) (Nat.pos_of_ne_zero hz) (Nat.mod_lt j hm) ⟨c, hj.symm⟩
  · exact hc

/-- The darts of the edges of `w`. -/
def walkKeep (M : CombMap.{u}) (w : List M.Dart) (d : M.Dart) : Prop :=
  d ∈ w ∨ M.alpha d ∈ w

theorem walkKeep_alpha (M : CombMap.{u}) (w : List M.Dart) (d : M.Dart) :
    walkKeep M w (M.alpha d) ↔ walkKeep M w d := by
  unfold walkKeep
  rw [M.alpha_involutive d]
  exact Or.comm

/-- The map on the edges of `w`. -/
noncomputable abbrev walkMap (M : CombMap.{u}) (w : List M.Dart) : CombMap.{u} :=
  CombMap.PredicateRestriction.toCombMap M (walkKeep M w) (walkKeep_alpha M w)

theorem walkMap_isRestriction (M : CombMap.{u}) (w : List M.Dart) :
    M.IsRestriction (walkMap M w) (Function.Embedding.subtype (walkKeep M w)) :=
  CombMap.PredicateRestriction.isRestriction M (walkKeep M w) (walkKeep_alpha M w)

/-- Retaining fewer darts only enlarges face classes. -/
theorem faceClass_mono (M : CombMap.{u}) {keep keep' : M.Dart → Prop}
    (hkk : ∀ x, ¬ keep x → ¬ keep' x) {x y : M.Dart}
    (h : Relation.EqvGen (CombMap.FaceClassStep M keep) x y) :
    Relation.EqvGen (CombMap.FaceClassStep M keep') x y := by
  induction h with
  | rel x₁ x₂ hx =>
      rcases hx with hx | ⟨hk, hx⟩
      · exact .rel _ _ (Or.inl hx)
      · exact .rel _ _ (Or.inr ⟨hkk x₁ hk, hx⟩)
  | refl x₁ => exact .refl _
  | symm x₁ x₂ _ ih => exact .symm _ _ ih
  | trans x₁ x₂ x₃ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

/-- Darts on one ambient face lie in one face class. -/
theorem eqvGen_faceClass_of_sameCycle (M : CombMap.{u}) (keep : M.Dart → Prop) {x y : M.Dart}
    (h : M.facePerm.SameCycle x y) : Relation.EqvGen (CombMap.FaceClassStep M keep) x y := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have hpow : ∀ (m : ℕ) (z : M.Dart),
      Relation.EqvGen (CombMap.FaceClassStep M keep) z ((M.facePerm ^ m) z) := by
    intro m
    induction m with
    | zero => intro z; exact Relation.EqvGen.refl _
    | succ m ih =>
        intro z
        rw [pow_succ, Perm.mul_apply]
        exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ (Or.inl rfl))
          (ih (M.facePerm z))
  simpa only [hn] using hpow n x

/-- Rotating from `alpha y` through darts that are not retained stays in the face class of `y`,
together with the reversed darts crossed on the way. -/
theorem faceClass_run (M : CombMap.{u}) (keep : M.Dart → Prop) (y : M.Dart) (m : ℕ)
    (hnk : ∀ k, 0 < k → k < m → ¬ keep ((M.sigma ^ k) (M.alpha y))) :
    ∀ k, 0 < k → k ≤ m →
      Relation.EqvGen (CombMap.FaceClassStep M keep) y ((M.sigma ^ k) (M.alpha y)) := by
  intro k
  induction k with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | succ k ih =>
      intro _ hkm
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp only [zero_add, pow_one]
        exact Relation.EqvGen.rel _ _ (Or.inl rfl)
      · refine Relation.EqvGen.trans _ _ _ (ih hk (by omega)) ?_
        refine Relation.EqvGen.trans _ (M.alpha ((M.sigma ^ k) (M.alpha y))) _
          (Relation.EqvGen.rel _ _ (Or.inr ⟨hnk k hk (by omega), rfl⟩))
          (Relation.EqvGen.rel _ _ (Or.inl ?_))
        rw [pow_succ', Perm.mul_apply]
        show M.sigma ((M.sigma ^ k) (M.alpha y)) =
          M.sigma (M.alpha (M.alpha ((M.sigma ^ k) (M.alpha y))))
        rw [M.alpha_involutive ((M.sigma ^ k) (M.alpha y))]

/-- A first-return run whose whole face class lies in `faces` is a boundary walk of `faces`. -/
theorem boundaryWalk_of_run (M : CombMap.{u}) (keep : M.Dart → Prop) (faces : Finset M.Face)
    (y : M.Dart) {m : ℕ} (hm : 0 < m)
    (hnk : ∀ k, 0 < k → k < m → ¬ keep ((M.sigma ^ k) (M.alpha y)))
    (hint : ∀ x, Relation.EqvGen (CombMap.FaceClassStep M keep) y x → M.faceOf x ∈ faces) :
    BoundaryWalk M faces y ((M.sigma ^ m) (M.alpha y)) := by
  have hrun := faceClass_run M keep y m hnk
  have hsteps : ∀ k, 0 < k → k ≤ m →
      Relation.ReflTransGen (fun x z => InternalDart M faces x ∧ M.sigma x = z)
        (M.facePerm y) ((M.sigma ^ k) (M.alpha y)) := by
    intro k
    induction k with
    | zero => intro h; exact absurd h (lt_irrefl 0)
    | succ k ih =>
        intro _ hkm
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp only [zero_add, pow_one]
          exact Relation.ReflTransGen.refl
        · refine Relation.ReflTransGen.tail (ih hk (by omega))
            ⟨⟨hint _ (hrun k hk (by omega)), ?_⟩, ?_⟩
          · exact hint _ (Relation.EqvGen.trans _ _ _ (hrun k hk (by omega))
              (Relation.EqvGen.rel _ _ (Or.inr ⟨hnk k hk (by omega), rfl⟩)))
          · rw [pow_succ', Perm.mul_apply]
  exact hsteps m hm le_rfl

/-- The faces on one side of `w`: those reached from a dart of `w` by advancing around faces
and crossing edges that are not on `w`. -/
noncomputable def sideFaces (M : CombMap.{u}) (w : List M.Dart) : Finset M.Face := by
  classical
  exact Finset.univ.filter fun f => ∃ x, M.faceOf x = f ∧
    ∃ d ∈ w, Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w)) d x

theorem mem_sideFaces_iff (M : CombMap.{u}) (w : List M.Dart) (x : M.Dart) :
    M.faceOf x ∈ sideFaces M w ↔
      ∃ d ∈ w, Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w)) d x := by
  unfold sideFaces
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨-, y, hy, d, hd, h⟩
    exact ⟨d, hd, .trans _ _ _ h
      (eqvGen_faceClass_of_sameCycle M _ ((M.faceOf_eq_iff y x).mp hy))⟩
  · rintro ⟨d, hd, h⟩
    exact ⟨Finset.mem_univ _, x, rfl, d, hd, h⟩

/-- The faces on the other side of `w`. -/
noncomputable def sideOutside (M : CombMap.{u}) (w : List M.Dart) : Finset M.Face := by
  classical
  exact Finset.univ.filter fun f => f ∉ sideFaces M w

theorem mem_sideOutside_iff (M : CombMap.{u}) (w : List M.Dart) (f : M.Face) :
    f ∈ sideOutside M w ↔ f ∉ sideFaces M w := by
  unfold sideOutside
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ f, h⟩⟩

end SimpleClosedWalkSides

open SimpleClosedWalkSides

namespace IsSimpleClosedWalk

variable {M : CombMap.{u}} {w : List M.Dart}

theorem nodup (hw : IsSimpleClosedWalk M w) : w.Nodup :=
  List.Nodup.of_map M.vertexOf hw.vertex_nodup

theorem next (hw : IsSimpleClosedWalk M w) (i : Fin w.length) :
    M.vertexOf (M.alpha (w.get i)) = M.vertexOf (w.get (finRotate _ i)) :=
  FaceBoundary.cyclic_relation_get_rotate (fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    w hw.ne_nil hw.chain hw.closes i

theorem vertexOf_inj (hw : IsSimpleClosedWalk M w) {d e : M.Dart} (hd : d ∈ w) (he : e ∈ w)
    (h : M.vertexOf d = M.vertexOf e) : d = e :=
  List.inj_on_of_nodup_map hw.vertex_nodup hd he h

theorem alpha_vertexOf_inj (hw : IsSimpleClosedWalk M w) {d e : M.Dart} (hd : d ∈ w)
    (he : e ∈ w) (h : M.vertexOf (M.alpha d) = M.vertexOf (M.alpha e)) : d = e := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hd
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp he
  have hrot : w.get (finRotate _ i) = w.get (finRotate _ j) :=
    hw.vertexOf_inj (List.get_mem _ _) (List.get_mem _ _)
      (((hw.next i).symm.trans h).trans (hw.next j))
  exact congrArg w.get ((finRotate _).injective (hw.nodup.get_inj_iff.mp hrot))

theorem exists_next (hw : IsSimpleClosedWalk M w) {a : M.Dart} (ha : a ∈ w) :
    ∃ b ∈ w, M.vertexOf (M.alpha a) = M.vertexOf b := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
  exact ⟨_, List.get_mem _ _, hw.next i⟩

theorem alpha_keep (hw : IsSimpleClosedWalk M w) {a : M.Dart} (ha : a ∈ w) :
    walkKeep M w (M.alpha a) :=
  Or.inr (by rw [M.alpha_involutive a]; exact ha)

/-- The retained darts at the vertex where `a` ends and `b` starts are `b` and `alpha a`. -/
theorem keep_at_vertex (hw : IsSimpleClosedWalk M w) {a b x : M.Dart} (ha : a ∈ w)
    (hb : b ∈ w) (hab : M.vertexOf (M.alpha a) = M.vertexOf b) (hx : walkKeep M w x)
    (hvx : M.vertexOf x = M.vertexOf b) : x = b ∨ x = M.alpha a := by
  rcases hx with hx | hx
  · exact Or.inl (hw.vertexOf_inj hx hb hvx)
  · refine Or.inr ?_
    have hxa : M.alpha x = a :=
      hw.alpha_vertexOf_inj hx ha (by rw [M.alpha_involutive x, hvx, hab])
    rw [← hxa, M.alpha_involutive x]

/-- The restricted rotation sends the reversal of `a` to the next walk dart `b`. -/
theorem walkMap_sigma_alpha (hw : IsSimpleClosedWalk M w) {a b : M.Dart} (ha : a ∈ w)
    (hb : b ∈ w) (hab : M.vertexOf (M.alpha a) = M.vertexOf b)
    (hk : walkKeep M w (M.alpha a)) :
    (walkMap M w).sigma ⟨M.alpha a, hk⟩ = ⟨b, Or.inl hb⟩ := by
  refine firstReturn_eq_of_two M.sigma (walkMap M w).sigma
    (Function.Embedding.subtype (walkKeep M w)) (walkMap_isRestriction M w).sigma_firstReturn
    ?_ ((M.vertexOf_eq_iff _ _).mp hab) ?_
  · intro h
    have h' : M.alpha a = b := congrArg Subtype.val h
    exact hw.alpha_not_mem a ha (by rw [h']; exact hb)
  · intro d hd
    have hv : M.vertexOf d.1 = M.vertexOf b :=
      ((M.vertexOf_eq_iff (M.alpha a) d.1).mpr hd).symm.trans hab
    rcases hw.keep_at_vertex ha hb hab d.2 hv with h | h
    · exact Or.inr (Subtype.ext h)
    · exact Or.inl (Subtype.ext h)

/-- The restricted rotation sends the next walk dart `b` to the reversal of `a`. -/
theorem walkMap_sigma_self (hw : IsSimpleClosedWalk M w) {a b : M.Dart} (ha : a ∈ w)
    (hb : b ∈ w) (hab : M.vertexOf (M.alpha a) = M.vertexOf b)
    (hk : walkKeep M w (M.alpha a)) :
    (walkMap M w).sigma ⟨b, Or.inl hb⟩ = ⟨M.alpha a, hk⟩ := by
  refine firstReturn_eq_of_two M.sigma (walkMap M w).sigma
    (Function.Embedding.subtype (walkKeep M w)) (walkMap_isRestriction M w).sigma_firstReturn
    ?_ ((M.vertexOf_eq_iff _ _).mp hab).symm ?_
  · intro h
    have h' : b = M.alpha a := congrArg Subtype.val h
    exact hw.alpha_not_mem a ha (by rw [← h']; exact hb)
  · intro d hd
    have hv : M.vertexOf d.1 = M.vertexOf b := ((M.vertexOf_eq_iff b d.1).mpr hd).symm
    rcases hw.keep_at_vertex ha hb hab d.2 hv with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

theorem walkMap_facePerm_mem (hw : IsSimpleClosedWalk M w) (d : (walkMap M w).Dart)
    (hd : d.1 ∈ w) : ((walkMap M w).facePerm d).1 ∈ w := by
  obtain ⟨b, hb, hab⟩ := hw.exists_next hd
  have hs : (walkMap M w).facePerm d = ⟨b, Or.inl hb⟩ :=
    hw.walkMap_sigma_alpha hd hb hab (hw.alpha_keep hd)
  rw [hs]
  exact hb

/-- The map on the edges of the walk is connected. -/
theorem walkMap_connected (hw : IsSimpleClosedWalk M w) : (walkMap M w).IsConnected := by
  have hmem : ∀ x ∈ w, ∃ hx : walkKeep M w x, Relation.EqvGen (walkMap M w).Adjacent
      ⟨w.head hw.ne_nil, Or.inl (List.head_mem hw.ne_nil)⟩ ⟨x, hx⟩ := by
    refine List.IsChain.induction (fun x => ∃ hx : walkKeep M w x,
      Relation.EqvGen (walkMap M w).Adjacent
        ⟨w.head hw.ne_nil, Or.inl (List.head_mem hw.ne_nil)⟩ ⟨x, hx⟩)
      w (List.IsChain.iff_mem.mp hw.chain) ?_ ?_
    · rintro x y ⟨hxw, hyw, hxy⟩ ⟨hx, h⟩
      refine ⟨Or.inl hyw, Relation.EqvGen.trans _ _ _ h
        (Relation.EqvGen.trans _ ⟨M.alpha x, hw.alpha_keep hxw⟩ _
          (Relation.EqvGen.rel _ _ (Or.inl rfl)) (Relation.EqvGen.rel _ _ (Or.inr ?_)))⟩
      exact hw.walkMap_sigma_alpha hxw hyw hxy (hw.alpha_keep hxw)
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
theorem not_faceClass_alpha (hw : IsSimpleClosedWalk M w) (hM : M.IsPlanar) {a d : M.Dart}
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

theorem isBoundaryDart_sideFaces_iff (hw : IsSimpleClosedWalk M w) (hM : M.IsPlanar)
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

theorem isBoundaryDart_sideOutside_iff (hw : IsSimpleClosedWalk M w) (hM : M.IsPlanar)
    (x : M.Dart) : IsBoundaryDart M (sideOutside M w) x ↔ M.alpha x ∈ w := by
  rw [← hw.isBoundaryDart_sideFaces_iff hM (M.alpha x)]
  show M.faceOf x ∈ sideOutside M w ∧ M.faceOf (M.alpha x) ∉ sideOutside M w ↔
    M.faceOf (M.alpha x) ∈ sideFaces M w ∧ M.faceOf (M.alpha (M.alpha x)) ∉ sideFaces M w
  rw [mem_sideOutside_iff, mem_sideOutside_iff, Classical.not_not, M.alpha_involutive x]
  exact And.comm

/-- A walk step is a boundary walk step of the faces on the walk's side. -/
theorem innerStep (hw : IsSimpleClosedWalk M w) {a b : M.Dart} (ha : a ∈ w) (hb : b ∈ w)
    (hab : M.vertexOf (M.alpha a) = M.vertexOf b) : BoundaryWalk M (sideFaces M w) a b := by
  obtain ⟨m, hm, hpm, havoid⟩ :=
    (walkMap_isRestriction M w).sigma_firstReturn ⟨M.alpha a, hw.alpha_keep ha⟩
  have hpm' : (M.sigma ^ m) (M.alpha a) = b :=
    hpm.trans (congrArg Subtype.val (hw.walkMap_sigma_alpha ha hb hab (hw.alpha_keep ha)))
  rw [← hpm']
  refine boundaryWalk_of_run M (walkKeep M w) (sideFaces M w) a hm ?_ ?_
  · intro k hk0 hkm hkeep
    exact havoid k hk0 hkm ⟨⟨_, hkeep⟩, rfl⟩
  · intro x hx
    exact (mem_sideFaces_iff M w x).mpr ⟨a, ha, hx⟩

/-- A reversed walk step is a boundary walk step of the faces on the other side. -/
theorem outerStep (hw : IsSimpleClosedWalk M w) (hM : M.IsPlanar) {a b : M.Dart} (ha : a ∈ w)
    (hb : b ∈ w) (hab : M.vertexOf (M.alpha a) = M.vertexOf b) :
    BoundaryWalk M (sideOutside M w) (M.alpha b) (M.alpha a) := by
  obtain ⟨m, hm, hpm, havoid⟩ :=
    (walkMap_isRestriction M w).sigma_firstReturn ⟨b, Or.inl hb⟩
  have hpm' : (M.sigma ^ m) (M.alpha (M.alpha b)) = M.alpha a := by
    rw [M.alpha_involutive b]
    exact hpm.trans (congrArg Subtype.val (hw.walkMap_sigma_self ha hb hab (hw.alpha_keep ha)))
  rw [← hpm']
  refine boundaryWalk_of_run M (walkKeep M w) (sideOutside M w) (M.alpha b) hm ?_ ?_
  · intro k hk0 hkm hkeep
    rw [M.alpha_involutive b] at hkeep
    exact havoid k hk0 hkm ⟨⟨_, hkeep⟩, rfl⟩
  · intro x hx
    rw [mem_sideOutside_iff, mem_sideFaces_iff]
    rintro ⟨d, hd, h⟩
    exact hw.not_faceClass_alpha hM hd hb (.trans _ _ _ h (.symm _ _ hx))

/-- The walk is the boundary cycle of the faces on its side. -/
def innerCycle (hw : IsSimpleClosedWalk M w) (hM : M.IsPlanar) :
    BoundaryCycle M (sideFaces M w) where
  cycle := w
  cycle_nonempty := hw.ne_nil
  cycle_nodup := hw.nodup
  cycle_mem_iff d := (hw.isBoundaryDart_sideFaces_iff hM d).symm

/-- The reversed walk is the boundary cycle of the faces on the other side. -/
def outerCycle (hw : IsSimpleClosedWalk M w) (hM : M.IsPlanar) :
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

theorem innerCycle_follows (hw : IsSimpleClosedWalk M w) (hM : M.IsPlanar) :
    (hw.innerCycle hM).FollowsBoundary :=
  BoundaryCycle.followsBoundary_of_chain _
    (hw.chain.imp_of_mem_imp fun _ _ ha hb h => hw.innerStep ha hb h)
    (hw.innerStep (List.getLast_mem _) (List.head_mem _) hw.closes)

theorem outerCycle_follows (hw : IsSimpleClosedWalk M w) (hM : M.IsPlanar) :
    (hw.outerCycle hM).FollowsBoundary := by
  refine BoundaryCycle.followsBoundary_of_chain _ ?_ ?_
  · show (w.reverse.map M.alpha).IsChain (BoundaryWalk M (sideOutside M w))
    rw [List.isChain_map, List.isChain_reverse]
    exact hw.chain.imp_of_mem_imp fun _ _ ha hb h => hw.outerStep hM ha hb h
  · show BoundaryWalk M (sideOutside M w) ((w.reverse.map M.alpha).getLast _)
      ((w.reverse.map M.alpha).head _)
    simp only [List.getLast_map, List.getLast_reverse, List.head_map, List.head_reverse]
    exact hw.outerStep hM (List.getLast_mem _) (List.head_mem _) hw.closes

end IsSimpleClosedWalk

/-- **Both sides of a simple closed walk in a planar map are disc regions.**  For a planar map
`M` and a simple closed walk `w` there are complementary face sets `faces` and `outside`, each a
disc region, whose boundary cycles are `w` and the reversed walk `w.reverse.map M.alpha`, and
both cycles follow their boundary walks. -/
def SimpleClosedWalkSidesStatement : Prop :=
  ∀ (M : CombMap.{u}) (w : List M.Dart), M.IsPlanar → IsSimpleClosedWalk M w →
    ∃ (faces outside : Finset M.Face) (inner : IsDiscRegion M faces)
      (outer : IsDiscRegion M outside),
      (∀ f, f ∈ outside ↔ f ∉ faces) ∧ inner.cycle = w ∧ outer.cycle = w.reverse.map M.alpha ∧
        inner.FollowsBoundary ∧ outer.FollowsBoundary

theorem simpleClosedWalkSides : SimpleClosedWalkSidesStatement.{u} := by
  intro M w hM hw
  exact ⟨sideFaces M w, sideOutside M w,
    (hw.innerCycle hM).toDiscRegion_of_followsBoundary M _ (hw.innerCycle_follows hM) hM,
    (hw.outerCycle hM).toDiscRegion_of_followsBoundary M _ (hw.outerCycle_follows hM) hM,
    mem_sideOutside_iff M w, rfl, rfl, hw.innerCycle_follows hM, hw.outerCycle_follows hM⟩

end GroupApproximation.GGT.VanKampen

#audit_closed_axioms GroupApproximation.GGT.VanKampen.simpleClosedWalkSides
#audit_axioms GroupApproximation.GGT.VanKampen.IsSimpleClosedWalk.not_faceClass_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.IsSimpleClosedWalk.innerCycle_follows
#audit_axioms GroupApproximation.GGT.VanKampen.IsSimpleClosedWalk.outerCycle_follows
