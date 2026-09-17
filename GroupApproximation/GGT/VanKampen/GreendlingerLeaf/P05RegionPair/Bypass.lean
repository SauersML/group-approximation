import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.TwoGon
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerPhiMapTransportDual
import GroupApproximation.Meta.AxiomGuard

/-!
# `Φ'_M` carried through a detour past one dart

Osin, arXiv:math/0411039v3, Appendix, the assumption before Lemma 9.3: "inside every 2-gon of
`Φ′_M`, there is a vertex of `Φ_M`".

Let `T` carry the regions of `S` to those of `S'`, and let `ιc` embed the collapsed map of `S`
into that of `S'` along the dart embedding of `T`.  Suppose the face rotations agree along `ιc`
except at one dart `w` that is not a crossing: where the old rotation turned to `w`, the new one
turns to a new dart `s` outside the range of `ιc`, and from `s` it continues where the old one
continued from `w`.

Mathematical proof.

(A) Iterates.  For `y ≠ w`, by induction on `k`,
  `p'^k (ι y) = if p^k y = w then s else ι (p^k y)`.  The inductive step splits on whether
  `p^k y = w`: if so, the new iterate is `p' s`, which is `ι (p w)` when `p w ≠ w`, and `s` when
  `p w = w` (then `p^(k+1) y = w` again).  Otherwise it is `h1` or `h2`.  Unlike
  `PhiMapTransport.pow_apply_bypass`, the fixed case `p w = w` is allowed.

(B) First returns.  A first return of `p` to a retained set avoiding `w` is, along `ι`, a first
  return of `p'`: by (A) the new iterates are the old ones mapped by `ι`, or `s`, which is not
  retained since it is outside the range of `ι`.

(C) Rotation of the Phi maps.  The kept darts of the carried component are exactly the images of
  the kept darts (`phiKeepO_map_iff`, `phiKeepO_range`), so `retainedEquiv` identifies the dart
  types; it commutes with `alpha` along `ιc`, and with the rotation by (B) and
  `apply_equiv_of_isFirstReturn`.

(D) A crossing lies in the collapsed map, and a crossing dart on the cell side `false` lies on the
  reversed source arc or on the target boundary darts.

* `pow_apply_bypass'`, `isFirstReturn_bypass'`, `retainedEquiv_sigma_bypass'`.
* `not_regionInternal_of_crossO`, `phiKeepO_map_iff`, `phiKeepO_range`,
  `mem_arcs_of_crossO_false`.
* `phiTransportAt_of_bypass'`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair

open Equiv Embedded Embedded.RegionCandidate PhiMapTransport

universe u w v

section Perm

open scoped Classical in
/-- **Iterates through a detour past one point**, allowing the detoured point to be fixed. -/
theorem pow_apply_bypass' {A : Type u} {B : Type v} {p : Perm A} {p' : Perm B} {ι : A ↪ B}
    {w : A} {s : B}
    (h1 : ∀ x, x ≠ w → p x ≠ w → p' (ι x) = ι (p x))
    (h2 : ∀ x, x ≠ w → p x = w → p' (ι x) = s)
    (h3 : p w ≠ w → p' s = ι (p w)) (h3f : p w = w → p' s = s) (k : ℕ) (y : A) (hy : y ≠ w) :
    (p' ^ k) (ι y) = if (p ^ k) y = w then s else ι ((p ^ k) y) := by
  induction k with
  | zero => simp only [pow_zero, Perm.one_apply, if_neg hy]
  | succ k ih =>
    have hp' : (p' ^ (k + 1)) (ι y) = p' ((p' ^ k) (ι y)) := by rw [pow_succ', Perm.mul_apply]
    have hp : (p ^ (k + 1)) y = p ((p ^ k) y) := by rw [pow_succ', Perm.mul_apply]
    rw [hp', ih, hp]
    by_cases hz : (p ^ k) y = w
    · rw [if_pos hz, hz]
      by_cases h0 : p w = w
      · rw [if_pos h0]
        exact h3f h0
      · rw [if_neg h0]
        exact h3 h0
    · rw [if_neg hz]
      by_cases hpz : p ((p ^ k) y) = w
      · rw [if_pos hpz]
        exact h2 _ hz hpz
      · rw [if_neg hpz]
        exact h1 _ hz hpz

/-- **A first return through a detour past one point**, allowing the detoured point to be fixed. -/
theorem isFirstReturn_bypass' {A : Type u} {B : Type v} {C : Type w} {p : Perm A}
    {p' : Perm B} {ι : A ↪ B} {w : A} {s : B} (hs : s ∉ Set.range ι)
    (h1 : ∀ x, x ≠ w → p x ≠ w → p' (ι x) = ι (p x))
    (h2 : ∀ x, x ≠ w → p x = w → p' (ι x) = s)
    (h3 : p w ≠ w → p' s = ι (p w)) (h3f : p w = w → p' s = s) {q : Perm C} {e : C ↪ A}
    (hw : w ∉ Set.range e) (hq : PermFirstReturn.IsFirstReturn p q e) :
    PermFirstReturn.IsFirstReturn p' q (e.trans ι) := by
  classical
  intro c
  have hc : e c ≠ w := fun h => hw ⟨c, h⟩
  obtain ⟨m, hm, hpm, hskip⟩ := hq c
  refine ⟨m, hm, ?_, fun k hk hkm hmem => ?_⟩
  · simp only [Function.Embedding.trans_apply]
    rw [pow_apply_bypass' h1 h2 h3 h3f m (e c) hc, hpm, if_neg (fun h => hw ⟨q c, h⟩)]
  · obtain ⟨c', hc'⟩ := hmem
    simp only [Function.Embedding.trans_apply] at hc'
    rw [pow_apply_bypass' h1 h2 h3 h3f k (e c) hc] at hc'
    by_cases hz : (p ^ k) (e c) = w
    · rw [if_pos hz] at hc'
      exact hs ⟨e c', hc'⟩
    · rw [if_neg hz] at hc'
      exact hskip k hk hkm ⟨c', ι.injective hc'⟩

end Perm

section Dual

variable {R : CombMap.{u}} {R' : CombMap.{v}} (ιc : R.Dart ↪ R'.Dart)
  {kp : R.Dart → Prop} (hkp : ∀ x, kp (R.dual.alpha x) ↔ kp x)
  {kp' : R'.Dart → Prop} (hkp' : ∀ x, kp' (R'.dual.alpha x) ↔ kp' x)
  (hcorr : ∀ x, kp' (ιc x) ↔ kp x) (hrange : ∀ x', kp' x' → x' ∈ Set.range ιc)

/-- **The correspondence of retained darts commutes with rotation** through a detour past one
non-retained dart, allowing that dart to be fixed by the face rotation. -/
theorem retainedEquiv_sigma_bypass' {w : R.Dart} {s : R'.Dart} (hs : s ∉ Set.range ιc)
    (hw : ¬ kp w)
    (h1 : ∀ x, x ≠ w → R.facePerm x ≠ w → R'.facePerm (ιc x) = ιc (R.facePerm x))
    (h2 : ∀ x, x ≠ w → R.facePerm x = w → R'.facePerm (ιc x) = s)
    (h3 : R.facePerm w ≠ w → R'.facePerm s = ιc (R.facePerm w))
    (h3f : R.facePerm w = w → R'.facePerm s = s)
    (y : (CombMap.PredicateRestriction.toCombMap R.dual kp hkp).Dart) :
    (CombMap.PredicateRestriction.toCombMap R'.dual kp' hkp').sigma
        (retainedEquiv ιc hkp hkp' hcorr hrange y) =
      retainedEquiv ιc hkp hkp' hcorr hrange
        ((CombMap.PredicateRestriction.toCombMap R.dual kp hkp).sigma y) := by
  have hq : PermFirstReturn.IsFirstReturn R.facePerm
      (CombMap.PredicateRestriction.sigma R.dual kp) (Function.Embedding.subtype kp) :=
    CombMap.PredicateRestriction.sigma_firstReturn R.dual kp
  have hq2 := isFirstReturn_bypass' hs h1 h2 h3 h3f (e := Function.Embedding.subtype kp)
    (fun hmem => by
      obtain ⟨c, hc⟩ := hmem
      apply hw
      rw [← hc]
      exact c.2) hq
  exact apply_equiv_of_isFirstReturn (retainedEquiv ιc hkp hkp' hcorr hrange) (fun _ => rfl) hq2
    (CombMap.PredicateRestriction.sigma_firstReturn R'.dual kp') y

end Dual

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- **A crossing dart is in the collapsed map.** -/
theorem not_regionInternal_of_crossO (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {a : RegionCandidate D eps S.diagram} (ha : a ∈ S.family) {s o : Bool}
    {d : S.diagram.toCombMap.Dart} (hd : crossO a s o = some d) : ¬ RegionInternal S.family d := by
  cases o with
  | false => exact not_regionInternal_of_mem_cycle S.pairwise ha (mem_cycle_crossO_false a hd)
  | true =>
    have h' : crossO a s false = some (S.diagram.toCombMap.alpha d) :=
      (crossO_alpha a s true d).mpr hd
    rw [← regionInternal_alpha S.family d]
    exact not_regionInternal_of_mem_cycle S.pairwise ha (mem_cycle_crossO_false a h')

/-- **The crossings of the carried component are the carried crossings.** -/
theorem phiKeepO_map_iff (T : RegionTransport S S') (a₀ : S.family)
    (ιc : (collapsedMap S.family).Dart ↪ (collapsedMap S'.family).Dart)
    (hιc : ∀ x, (ιc x).1 = T.darts x.1) (x : (collapsedMap S.family).Dart) :
    PhiKeepO S'.family (linkedComponentO S'.family (T.map a₀)) (ιc x) ↔
      PhiKeepO S.family (linkedComponentO S.family a₀.1) x := by
  constructor
  · rintro ⟨b', hb', s, o, h⟩
    obtain ⟨b, rfl, hb⟩ := (T.mem_linkedComponentO_map a₀).mp hb'
    refine ⟨b.1, hb, s, o, ?_⟩
    rw [T.cross, hιc] at h
    obtain ⟨d, hd, hdx⟩ := Option.map_eq_some_iff.mp h
    rw [hd, T.darts.injective hdx]
  · rintro ⟨b, hb, s, o, h⟩
    refine ⟨T.map ⟨b, linkedComponentO_subset _ _ hb⟩,
      (T.mem_linkedComponentO_map a₀).mpr ⟨_, rfl, hb⟩, s, o, ?_⟩
    rw [T.cross, hιc]
    exact congrArg (Option.map T.darts) h

/-- **Every crossing of the carried component is carried.** -/
theorem phiKeepO_range (T : RegionTransport S S') (a₀ : S.family)
    (ιc : (collapsedMap S.family).Dart ↪ (collapsedMap S'.family).Dart)
    (hιc : ∀ x, (ιc x).1 = T.darts x.1) (x' : (collapsedMap S'.family).Dart)
    (h : PhiKeepO S'.family (linkedComponentO S'.family (T.map a₀)) x') : x' ∈ Set.range ιc := by
  obtain ⟨b', hb', s, o, hx⟩ := h
  obtain ⟨b, rfl, hb⟩ := (T.mem_linkedComponentO_map a₀).mp hb'
  rw [T.cross] at hx
  obtain ⟨d, hd, hdx⟩ := Option.map_eq_some_iff.mp hx
  exact ⟨⟨d, not_regionInternal_of_crossO S b.2 hd⟩, Subtype.ext ((hιc _).trans hdx)⟩

/-- **A crossing inside a region lies on the reversed source arc or the target boundary.** -/
theorem mem_arcs_of_crossO_false (a : RegionCandidate D eps Delta) {side : Bool}
    {d : Delta.toCombMap.Dart} (hd : crossO a side false = some d) :
    d ∈ a.2.sourceArc.reverseDarts ∨ d ∈ targetBoundaryDarts Delta a.2.target a.2.targetArc := by
  cases side with
  | true =>
    rw [crossO_true, cross_false, Option.map_eq_some_iff] at hd
    obtain ⟨p, hp, rfl⟩ := hd
    simp only [cross, if_true] at hp
    left
    simp only [CyclicArc.reverseDarts, List.mem_map, List.mem_reverse]
    exact ⟨p, List.mem_of_mem_head? hp, rfl⟩
  | false =>
    rcases Option.eq_none_or_eq_some a.2.target with ht | ⟨i, ht⟩
    · rw [crossO_false_of_eq_none a ht, Bool.not_false] at hd
      simp only [cross, if_true] at hd
      exact Or.inr (mem_targetBoundaryDarts_of_eq_none Delta a.2.target a.2.targetArc ht
        (List.mem_of_mem_head? hd))
    · rw [crossO_false_of_eq_some a ht, cross_false, Option.map_eq_some_iff] at hd
      obtain ⟨p, hp, rfl⟩ := hd
      simp only [cross, if_true] at hp
      refine Or.inr (mem_targetBoundaryDarts_of_ne_none Delta a.2.target a.2.targetArc
        (by rw [ht]; exact Option.some_ne_none i) _ ?_)
      simp only [CyclicArc.reverseDarts, List.mem_map, List.mem_reverse]
      exact ⟨p, List.mem_of_mem_head? hp, rfl⟩

/-- **`Φ'_M` is carried when the face rotations agree up to a detour past a non-crossing dart**,
allowing that dart to be fixed. -/
theorem phiTransportAt_of_bypass' (T : RegionTransport S S') (a₀ : S.family)
    (ιc : (collapsedMap S.family).Dart ↪ (collapsedMap S'.family).Dart)
    (hιc : ∀ x, (ιc x).1 = T.darts x.1)
    (hαc : ∀ x, ιc ((collapsedMap S.family).alpha x) = (collapsedMap S'.family).alpha (ιc x))
    {w : (collapsedMap S.family).Dart} {s : (collapsedMap S'.family).Dart}
    (hs : s ∉ Set.range ιc) (hw : ¬ PhiKeepO S.family (linkedComponentO S.family a₀.1) w)
    (h1 : ∀ x, x ≠ w → (collapsedMap S.family).facePerm x ≠ w →
      (collapsedMap S'.family).facePerm (ιc x) = ιc ((collapsedMap S.family).facePerm x))
    (h2 : ∀ x, x ≠ w → (collapsedMap S.family).facePerm x = w →
      (collapsedMap S'.family).facePerm (ιc x) = s)
    (h3 : (collapsedMap S.family).facePerm w ≠ w →
      (collapsedMap S'.family).facePerm s = ιc ((collapsedMap S.family).facePerm w))
    (h3f : (collapsedMap S.family).facePerm w = w → (collapsedMap S'.family).facePerm s = s)
    (back : (collapsedMap S'.family).Dart → (collapsedMap S.family).Dart)
    (hback : ∀ x, back (ιc x) = x)
    (hsim : ∀ x' y', Relation.EqvGen (CombMap.FaceClassStep (collapsedMap S'.family).dual
        (PhiKeepO S'.family (linkedComponentO S'.family (T.map a₀)))) x' y' →
      Relation.EqvGen (CombMap.FaceClassStep (collapsedMap S.family).dual
        (PhiKeepO S.family (linkedComponentO S.family a₀.1))) (back x') (back y'))
    (hcell : ∀ (x' : (collapsedMap S'.family).Dart) (i' : Fin S'.diagram.rCellCount),
      S'.diagram.toCombMap.faceOf x'.1 = (cell S'.diagram i').face →
        S.diagram.toCombMap.faceOf (back x').1 = (cell S.diagram (T.cellIndex.symm i')).face) :
    PhiTransportAt T a₀ := by
  refine ⟨retainedEquiv ιc phiKeepO_alpha phiKeepO_alpha (phiKeepO_map_iff T a₀ ιc hιc)
      (phiKeepO_range T a₀ ιc hιc), fun y => hιc y.1,
    retainedEquiv_alpha ιc phiKeepO_alpha phiKeepO_alpha (phiKeepO_map_iff T a₀ ιc hιc)
      (phiKeepO_range T a₀ ιc hιc) hαc,
    fun y => (retainedEquiv_sigma_bypass' ιc phiKeepO_alpha phiKeepO_alpha
      (phiKeepO_map_iff T a₀ ιc hιc) (phiKeepO_range T a₀ ιc hιc) hs hw h1 h2 h3 h3f y).symm, ?_⟩
  intro y x' i' hpath hface
  have h1' : Relation.EqvGen (CombMap.FaceClassStep (collapsedMap S.family).dual
      (PhiKeepO S.family (linkedComponentO S.family a₀.1))) (back (ιc y.1)) (back x') :=
    hsim _ _ hpath
  rw [hback] at h1'
  exact ⟨back x', h1', hcell x' i' hface⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.pow_apply_bypass'
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.isFirstReturn_bypass'
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.retainedEquiv_sigma_bypass'
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.not_regionInternal_of_crossO
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.phiKeepO_map_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.phiKeepO_range
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.mem_arcs_of_crossO_false
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.phiTransportAt_of_bypass'
