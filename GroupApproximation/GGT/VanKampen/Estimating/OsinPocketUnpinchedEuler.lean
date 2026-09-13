import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionUnpinched
import GroupApproximation.GGT.VanKampen.CombMapRestrictionPlanarity
import GroupApproximation.Meta.AxiomGuard

/-!
# Two boundary circuits give an unpinched face set

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  In a planar map, suppose the boundary cycle of a face set and the
boundary cycle of its complement both follow the boundary.  Then the face set is unpinched.

Keep only the boundary edges.  The kept map has two faces, one on each side, and one edge for each
boundary dart of the face set.  It is connected, so it is planar, so it has as many vertices as
edges.  Every vertex of the kept map carries a boundary dart of the face set, so no vertex carries
two.  The count needs planarity: on a torus both circuits can pass twice through one vertex.

* `Surgery.MapCollapse.boundaryEdgeMap`: the map on the boundary edges of a face set.
* `Surgery.MapCollapse.restriction_facePerm_eq_boundaryPerm`: in a restriction that keeps the
  boundary darts and no internal dart, face rotation at a boundary dart is the first return along
  the boundary walk.
* `BoundaryEdgeMap.isPlanar`, `BoundaryEdgeMap.faceCount_eq_two`, `BoundaryEdgeMap.edgeCount_eq`
  and `BoundaryEdgeMap.vertexOf_bijective`: the count.
* `Surgery.MapCollapse.unpinched_of_followsBoundary_complement` and the endpoint
  `BothFollowUnpinchedStatement` / `bothFollowUnpinched`.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u v

/-- Iterates of semiconjugate permutations. -/
private theorem pow_apply_of_semiconj {A : Type u} {B : Type v} (p : Equiv.Perm A)
    (q : Equiv.Perm B) (f : A → B) (h : ∀ a, q (f a) = f (p a)) (a : A) (n : ℕ) :
    (q ^ n) (f a) = f ((p ^ n) a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih, h]

/-- A semiconjugacy carries cycles into cycles. -/
private theorem sameCycle_of_semiconj {A : Type u} {B : Type v} [Finite A] (p : Equiv.Perm A)
    (q : Equiv.Perm B) (f : A → B) (h : ∀ a, q (f a) = f (p a)) {a b : A}
    (hab : p.SameCycle a b) : q.SameCycle (f a) (f b) := by
  obtain ⟨n, rfl⟩ := hab.exists_nat_pow_eq
  exact ⟨n, by rw [zpow_natCast, pow_apply_of_semiconj p q f h a n]⟩

/-- Face rotation is two elementary steps. -/
private theorem eqvGen_facePerm_pow (N : CombMap.{v}) (d : N.Dart) (n : ℕ) :
    Relation.EqvGen N.Adjacent d ((N.facePerm ^ n) d) := by
  induction n with
  | zero => exact Relation.EqvGen.refl _
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact Relation.EqvGen.trans _ _ _ ih
        (Relation.EqvGen.trans _ (N.alpha ((N.facePerm ^ n) d)) _
          (Relation.EqvGen.rel _ _ (Or.inl rfl)) (Relation.EqvGen.rel _ _ (Or.inr rfl)))

namespace Surgery.MapCollapse

section Restriction

variable {M : CombMap.{v}} (faces : Finset M.Face)

/-- **Face rotation on a boundary edge.**  In a restriction that keeps the boundary darts of a
face set and no internal dart, face rotation at a boundary dart is the first return along the
boundary walk. -/
theorem restriction_facePerm_eq_boundaryPerm (keep : M.Dart → Prop)
    (hkeep : ∀ d, keep (M.alpha d) ↔ keep d) (hint : ∀ z, InternalDart M faces z → ¬keep z)
    (x : BoundaryDart M faces) (hx : keep x.1)
    (hy : keep (FaceSetCircuits.boundaryPerm M faces x).1) :
    (CombMap.PredicateRestriction.toCombMap M keep hkeep).facePerm ⟨x.1, hx⟩ =
      ⟨(FaceSetCircuits.boundaryPerm M faces x).1, hy⟩ := by
  have hwalk : Relation.ReflTransGen (fun a b => InternalDart M faces a ∧ M.sigma a = b)
      (M.facePerm x.1) (FaceSetCircuits.boundaryPerm M faces x).1 :=
    FaceSetCircuits.boundaryPerm_walk M faces x
  obtain ⟨n, hn, hskip⟩ :=
    PermFirstReturn.exists_pow_of_skip_walk M.sigma (InternalDart M faces) hwalk
  have hax : keep (M.alpha x.1) := (hkeep x.1).mpr hx
  obtain ⟨m, hm, hmeq, hmskip⟩ :=
    CombMap.PredicateRestriction.sigma_firstReturn M keep ⟨M.alpha x.1, hax⟩
  have hpow : ∀ k : ℕ, (M.sigma ^ (k + 1)) (M.alpha x.1) = (M.sigma ^ k) (M.facePerm x.1) := by
    intro k
    rw [pow_succ, Equiv.Perm.mul_apply]
    rfl
  have hlt : ¬m < n + 1 := by
    intro h
    apply hint _ (hskip (m - 1) (by omega))
    have hval : (M.sigma ^ (m - 1)) (M.facePerm x.1) =
        (CombMap.PredicateRestriction.sigma M keep ⟨M.alpha x.1, hax⟩).1 := by
      rw [← hpow (m - 1), Nat.sub_add_cancel hm]
      exact hmeq
    rw [hval]
    exact (CombMap.PredicateRestriction.sigma M keep ⟨M.alpha x.1, hax⟩).2
  have hgt : ¬n + 1 < m := fun h =>
    hmskip (n + 1) (by omega) h
      ⟨⟨(FaceSetCircuits.boundaryPerm M faces x).1, hy⟩, ((hpow n).trans hn).symm⟩
  obtain rfl : m = n + 1 := by omega
  apply Subtype.ext
  change (CombMap.PredicateRestriction.sigma M keep ⟨M.alpha x.1, hax⟩).1 =
    (FaceSetCircuits.boundaryPerm M faces x).1
  exact hmeq.symm.trans ((hpow n).trans hn)

end Restriction

/-- The darts on the boundary edges of a face set. -/
def boundaryEdgeKeep (M : CombMap.{v}) (faces : Finset M.Face) (x : M.Dart) : Prop :=
  IsBoundaryDart M faces x ∨ IsBoundaryDart M faces (M.alpha x)

theorem boundaryEdgeKeep_alpha (M : CombMap.{v}) (faces : Finset M.Face) (x : M.Dart) :
    boundaryEdgeKeep M faces (M.alpha x) ↔ boundaryEdgeKeep M faces x := by
  unfold boundaryEdgeKeep
  rw [M.alpha_involutive x]
  exact Or.comm

/-- **The boundary edge map**: the map on the boundary edges of a face set, with the actual
cyclic order at each vertex. -/
noncomputable abbrev boundaryEdgeMap (M : CombMap.{v}) (faces : Finset M.Face) : CombMap.{v} :=
  CombMap.PredicateRestriction.toCombMap M (boundaryEdgeKeep M faces)
    (boundaryEdgeKeep_alpha M faces)

theorem boundaryEdgeMap_isRestriction (M : CombMap.{v}) (faces : Finset M.Face) :
    M.IsRestriction (boundaryEdgeMap M faces)
      (Function.Embedding.subtype (boundaryEdgeKeep M faces)) :=
  CombMap.PredicateRestriction.isRestriction M (boundaryEdgeKeep M faces)
    (boundaryEdgeKeep_alpha M faces)

namespace BoundaryEdgeMap

variable {M : CombMap.{v}} (faces : Finset M.Face) {outside : Finset M.Face}

/-- A boundary dart of the face set, as a dart of the boundary edge map. -/
def innerDart (a : BoundaryDart M faces) : (boundaryEdgeMap M faces).Dart :=
  ⟨a.1, Or.inl a.2⟩

theorem not_keep_of_internal {z : M.Dart} (hz : InternalDart M faces z) :
    ¬boundaryEdgeKeep M faces z := by
  rintro (h | h)
  · exact h.2 hz.2
  · apply h.2
    rw [M.alpha_involutive]
    exact hz.1

/-- **Face rotation at a boundary dart** is the first return along the boundary walk. -/
theorem facePerm_innerDart (a : BoundaryDart M faces) :
    (boundaryEdgeMap M faces).facePerm (innerDart faces a) =
      innerDart faces (FaceSetCircuits.boundaryPerm M faces a) :=
  restriction_facePerm_eq_boundaryPerm faces (boundaryEdgeKeep M faces)
    (boundaryEdgeKeep_alpha M faces) (fun _ => not_keep_of_internal faces) a (Or.inl a.2)
    (Or.inl (FaceSetCircuits.boundaryPerm M faces a).2)

/-- The boundary darts of the face set lie in one face of the boundary edge map. -/
theorem sameCycle_innerDart {inner : BoundaryCycle M faces} (hin : inner.FollowsBoundary)
    (a b : BoundaryDart M faces) :
    (boundaryEdgeMap M faces).facePerm.SameCycle (innerDart faces a) (innerDart faces b) := by
  obtain ⟨c, hc⟩ := inner.exists_component_of_followsBoundary hin
  exact sameCycle_of_semiconj _ _ (innerDart faces) (facePerm_innerDart faces)
    (Quotient.eq''.mp ((hc a).trans (hc b).symm))

/-- The face of a boundary dart of the face set holds only boundary darts of the face set. -/
theorem isBoundaryDart_of_sameCycle (a : BoundaryDart M faces)
    {d : (boundaryEdgeMap M faces).Dart}
    (h : (boundaryEdgeMap M faces).facePerm.SameCycle (innerDart faces a) d) :
    IsBoundaryDart M faces d.1 := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  rw [pow_apply_of_semiconj _ _ (innerDart faces) (facePerm_innerDart faces) a n]
  exact ((FaceSetCircuits.boundaryPerm M faces ^ n) a).2

theorem isBoundaryDart_outside_iff (hmem : ∀ f, f ∈ outside ↔ f ∉ faces) (x : M.Dart) :
    IsBoundaryDart M outside x ↔ IsBoundaryDart M faces (M.alpha x) := by
  change (M.faceOf x ∈ outside ∧ M.faceOf (M.alpha x) ∉ outside) ↔
    (M.faceOf (M.alpha x) ∈ faces ∧ M.faceOf (M.alpha (M.alpha x)) ∉ faces)
  rw [hmem, hmem, not_not, M.alpha_involutive x]
  exact and_comm

/-- A boundary dart of the complement, as a dart of the boundary edge map. -/
def outerDart (hmem : ∀ f, f ∈ outside ↔ f ∉ faces) (a : BoundaryDart M outside) :
    (boundaryEdgeMap M faces).Dart :=
  ⟨a.1, Or.inr ((isBoundaryDart_outside_iff faces hmem a.1).mp a.2)⟩

theorem not_keep_of_internal_outside (hmem : ∀ f, f ∈ outside ↔ f ∉ faces) {z : M.Dart}
    (hz : InternalDart M outside z) : ¬boundaryEdgeKeep M faces z := by
  rintro (h | h)
  · exact (hmem _).mp hz.1 h.1
  · exact (hmem _).mp hz.2 h.1

/-- **Face rotation at a boundary dart of the complement** is the first return along the boundary
walk of the complement. -/
theorem facePerm_outerDart (hmem : ∀ f, f ∈ outside ↔ f ∉ faces) (a : BoundaryDart M outside) :
    (boundaryEdgeMap M faces).facePerm (outerDart faces hmem a) =
      outerDart faces hmem (FaceSetCircuits.boundaryPerm M outside a) :=
  restriction_facePerm_eq_boundaryPerm outside (boundaryEdgeKeep M faces)
    (boundaryEdgeKeep_alpha M faces) (fun _ => not_keep_of_internal_outside faces hmem) a
    (Or.inr ((isBoundaryDart_outside_iff faces hmem a.1).mp a.2))
    (Or.inr ((isBoundaryDart_outside_iff faces hmem _).mp
      (FaceSetCircuits.boundaryPerm M outside a).2))

/-- The boundary darts of the complement lie in one face of the boundary edge map. -/
theorem sameCycle_outerDart (hmem : ∀ f, f ∈ outside ↔ f ∉ faces)
    {outer : BoundaryCycle M outside} (hout : outer.FollowsBoundary)
    (a b : BoundaryDart M outside) :
    (boundaryEdgeMap M faces).facePerm.SameCycle (outerDart faces hmem a)
      (outerDart faces hmem b) := by
  obtain ⟨c, hc⟩ := outer.exists_component_of_followsBoundary hout
  exact sameCycle_of_semiconj _ _ (outerDart faces hmem) (facePerm_outerDart faces hmem)
    (Quotient.eq''.mp ((hc a).trans (hc b).symm))

/-- The boundary edge map is connected. -/
theorem isConnected {inner : BoundaryCycle M faces} (hin : inner.FollowsBoundary) :
    (boundaryEdgeMap M faces).IsConnected := by
  have hall : ∀ d : (boundaryEdgeMap M faces).Dart, ∃ a : BoundaryDart M faces,
      Relation.EqvGen (boundaryEdgeMap M faces).Adjacent (innerDart faces a) d := by
    rintro ⟨d, h | h⟩
    · exact ⟨⟨d, h⟩, Relation.EqvGen.refl _⟩
    · exact ⟨⟨M.alpha d, h⟩,
        Relation.EqvGen.rel _ _ (Or.inl (Subtype.ext (M.alpha_involutive d)))⟩
  intro d e
  obtain ⟨a, ha⟩ := hall d
  obtain ⟨b, hb⟩ := hall e
  obtain ⟨n, hn⟩ := (sameCycle_innerDart faces hin a b).exists_nat_pow_eq
  have hab := eqvGen_facePerm_pow (boundaryEdgeMap M faces) (innerDart faces a) n
  rw [hn] at hab
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ ha)
    (Relation.EqvGen.trans _ _ _ hab hb)

/-- The boundary edge map of a face set in a planar map is planar. -/
theorem isPlanar (hM : M.IsPlanar) {inner : BoundaryCycle M faces} (hin : inner.FollowsBoundary)
    (a : BoundaryDart M faces) : (boundaryEdgeMap M faces).IsPlanar :=
  (boundaryEdgeMap_isRestriction M faces).planar hM (isConnected faces hin) (innerDart faces a)

/-- **Two faces.**  The boundary edge map has one face on each side. -/
theorem faceCount_eq_two (hmem : ∀ f, f ∈ outside ↔ f ∉ faces) {inner : BoundaryCycle M faces}
    {outer : BoundaryCycle M outside} (hin : inner.FollowsBoundary)
    (hout : outer.FollowsBoundary) (a : BoundaryDart M faces) :
    (boundaryEdgeMap M faces).faceCount = 2 := by
  have ha : IsBoundaryDart M outside (M.alpha a.1) := by
    rw [isBoundaryDart_outside_iff faces hmem, M.alpha_involutive]
    exact a.2
  show Nat.card (boundaryEdgeMap M faces).Face = 2
  rw [Nat.card_eq_two_iff]
  refine ⟨(boundaryEdgeMap M faces).faceOf (innerDart faces a),
    (boundaryEdgeMap M faces).faceOf (outerDart faces hmem ⟨M.alpha a.1, ha⟩), fun h => ?_, ?_⟩
  · have hb := isBoundaryDart_of_sameCycle faces a
      (((boundaryEdgeMap M faces).faceOf_eq_iff _ _).mp h)
    exact a.2.2 hb.1
  · refine Set.eq_univ_of_forall fun f => ?_
    refine Quotient.inductionOn' f fun d => ?_
    rcases d with ⟨d, h | h⟩
    · refine Set.mem_insert_iff.mpr (Or.inl ?_)
      exact ((boundaryEdgeMap M faces).faceOf_eq_iff ⟨d, Or.inl h⟩ (innerDart faces a)).mpr
        (sameCycle_innerDart faces hin ⟨d, h⟩ a)
    · refine Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr ?_))
      have hd : IsBoundaryDart M outside d := (isBoundaryDart_outside_iff faces hmem d).mpr h
      exact ((boundaryEdgeMap M faces).faceOf_eq_iff ⟨d, Or.inr h⟩
        (outerDart faces hmem ⟨M.alpha a.1, ha⟩)).mpr
        (sameCycle_outerDart faces hmem hout ⟨d, hd⟩ ⟨M.alpha a.1, ha⟩)

/-- **One edge for each boundary dart.** -/
theorem edgeCount_eq :
    (boundaryEdgeMap M faces).edgeCount = Nat.card (BoundaryDart M faces) := by
  refine (Nat.card_eq_of_bijective
    (fun a => (boundaryEdgeMap M faces).edgeOf (innerDart faces a))
    ⟨fun a b hab => ?_, fun f => ?_⟩).symm
  · rcases ((boundaryEdgeMap M faces).edgeOf_eq_iff _ _).mp hab with hab | hab
    · have hv : (innerDart faces a).1 = (innerDart faces b).1 := congrArg Subtype.val hab
      exact Subtype.ext hv
    · have hv : M.alpha a.1 = b.1 := congrArg Subtype.val hab
      have hb := b.2.1
      rw [← hv] at hb
      exact absurd hb a.2.2
  · refine Quotient.inductionOn' f fun d => ?_
    rcases d with ⟨d, h | h⟩
    · exact ⟨⟨d, h⟩, rfl⟩
    · exact ⟨⟨M.alpha d, h⟩, ((boundaryEdgeMap M faces).edgeOf_eq_iff
        (innerDart faces ⟨M.alpha d, h⟩) ⟨d, Or.inr h⟩).mpr
        (Or.inr (Subtype.ext (M.alpha_involutive d)))⟩

/-- Every vertex of the boundary edge map carries a boundary dart of the face set. -/
theorem vertexOf_surjective :
    Function.Surjective fun a : BoundaryDart M faces =>
      (boundaryEdgeMap M faces).vertexOf (innerDart faces a) := by
  intro v
  refine Quotient.inductionOn' v fun d => ?_
  rcases d with ⟨d, h | h⟩
  · exact ⟨⟨d, h⟩, rfl⟩
  · refine ⟨FaceSetCircuits.boundaryPerm M faces ⟨M.alpha d, h⟩, ?_⟩
    show (boundaryEdgeMap M faces).vertexOf
        (innerDart faces (FaceSetCircuits.boundaryPerm M faces ⟨M.alpha d, h⟩)) =
      (boundaryEdgeMap M faces).vertexOf ⟨d, Or.inr h⟩
    rw [← facePerm_innerDart faces]
    have hd : (boundaryEdgeMap M faces).alpha (innerDart faces ⟨M.alpha d, h⟩) =
        ⟨d, Or.inr h⟩ :=
      Subtype.ext (M.alpha_involutive d)
    change (boundaryEdgeMap M faces).vertexOf
      ((boundaryEdgeMap M faces).sigma ((boundaryEdgeMap M faces).alpha
        (innerDart faces ⟨M.alpha d, h⟩))) = _
    rw [hd, CombMap.vertexOf_sigma]

/-- **No vertex carries two boundary darts.**  The Euler formula of the boundary edge map gives as
many vertices as edges, so the surjection from boundary darts to vertices is a bijection. -/
theorem vertexOf_bijective (hM : M.IsPlanar) (hmem : ∀ f, f ∈ outside ↔ f ∉ faces)
    {inner : BoundaryCycle M faces} {outer : BoundaryCycle M outside}
    (hin : inner.FollowsBoundary) (hout : outer.FollowsBoundary) (x0 : BoundaryDart M faces) :
    Function.Bijective fun a : BoundaryDart M faces =>
      (boundaryEdgeMap M faces).vertexOf (innerDart faces a) := by
  refine (vertexOf_surjective faces).bijective_of_nat_card_le ?_
  have heuler := (isPlanar faces hM hin x0).2
  have hface := faceCount_eq_two faces hmem hin hout x0
  have hedge := edgeCount_eq faces
  unfold CombMap.eulerCharacteristic at heuler
  rw [hface, hedge] at heuler
  change Nat.card (BoundaryDart M faces) ≤ (boundaryEdgeMap M faces).vertexCount
  omega

end BoundaryEdgeMap

variable {M : CombMap.{v}} {faces outside : Finset M.Face}

/-- **Two boundary circuits give an unpinched face set.**  In a planar map, if the boundary cycle
of a face set and the boundary cycle of its complement both follow the boundary, then no vertex
carries two boundary darts of the face set. -/
theorem unpinched_of_followsBoundary_complement (hM : M.IsPlanar)
    (hmem : ∀ f, f ∈ outside ↔ f ∉ faces) (inner : BoundaryCycle M faces)
    (outer : BoundaryCycle M outside) (hin : inner.FollowsBoundary)
    (hout : outer.FollowsBoundary) : Unpinched M faces := by
  intro x y hx hy hv
  have hbij := BoundaryEdgeMap.vertexOf_bijective faces hM hmem hin hout ⟨x, hx⟩
  have hN : (boundaryEdgeMap M faces).vertexOf (BoundaryEdgeMap.innerDart faces ⟨x, hx⟩) =
      (boundaryEdgeMap M faces).vertexOf (BoundaryEdgeMap.innerDart faces ⟨y, hy⟩) :=
    ((boundaryEdgeMap_isRestriction M faces).vertexOf_eq_iff _ _).mpr hv
  exact congrArg Subtype.val (hbij.1 hN)

/-- **Two boundary circuits give an unpinched face set** (Osin 9.7(b) infrastructure): in a planar
map, if the boundary cycle of a face set and that of its complement both follow the boundary, the
face set is unpinched. -/
def BothFollowUnpinchedStatement : Prop :=
  ∀ (M : CombMap.{v}) (faces outside : Finset M.Face) (inner : BoundaryCycle M faces)
    (outer : BoundaryCycle M outside), M.IsPlanar → (∀ f, f ∈ outside ↔ f ∉ faces) →
      inner.FollowsBoundary → outer.FollowsBoundary → Unpinched M faces

theorem bothFollowUnpinched : BothFollowUnpinchedStatement.{v} :=
  fun _ _ _ inner outer hM hmem hin hout =>
    unpinched_of_followsBoundary_complement hM hmem inner outer hin hout

end Surgery.MapCollapse

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.restriction_facePerm_eq_boundaryPerm
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.BoundaryEdgeMap.faceCount_eq_two
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.BoundaryEdgeMap.edgeCount_eq
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.BoundaryEdgeMap.vertexOf_bijective
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.unpinched_of_followsBoundary_complement
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.bothFollowUnpinched
