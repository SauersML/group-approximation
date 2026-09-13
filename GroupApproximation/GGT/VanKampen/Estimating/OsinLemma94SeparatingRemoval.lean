import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ChainRespell
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94DartMinimal
import GroupApproximation.GGT.VanKampen.SurgeryGFaceMergeDarts
import GroupApproximation.Meta.AxiomGuard

/-!
# Removing a path between two G-faces

Osin (math/0411039v3, §9), Lemma 9.4, Case 2: "This contradicts our assumption that `∑ l(t_i)` is
minimal."  The respelling of a cutting path (`OsinLemma94ChainRespell`) ends by removing a path
whose two sides are two different unselected `G`-faces.  A `G`-face merge across the first edge
(`Surgery.GFaceMerge`) removes that edge and merges the two faces.  The rest of the path then
hangs from a vertex of valence one inside the merged face, and `PendantPathRemovalInput` removes
it.

* `Surgery.GFaceMerge.facePerm_keep_of_ne`: a dart off the deleted edge whose successor is off
  the edge keeps its successor.
* `Surgery.GFaceMerge.sigma_keep_eq_self`: the second dart of a path through a vertex of valence
  two leaves a vertex of valence one once the first edge is deleted.
* `GloballyDistinguishedSectionFamily.separatingPathRemovalInput_of_pendant`.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded

namespace Surgery.GFaceMerge

open scoped Classical

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}
  (R : GFaceMerge Delta)

/-- A dart off the deleted edge whose successor is off the edge keeps its successor. -/
theorem facePerm_keep_of_ne {d : Delta.toCombMap.Dart}
    (hd : d ≠ R.dart ∧ d ≠ Delta.toCombMap.alpha R.dart)
    (hnext : Delta.toCombMap.facePerm d ≠ R.dart ∧
      Delta.toCombMap.facePerm d ≠ Delta.toCombMap.alpha R.dart) :
    R.diagram.toCombMap.facePerm (R.keep d) = R.keep (Delta.toCombMap.facePerm d) := by
  apply R.val_injective
  have h : R.val (R.diagram.toCombMap.facePerm (R.keep d)) =
      EdgeDeletion.next Delta.toCombMap R.dart (R.val (R.keep d)) :=
    EdgeDeletion.value_facePerm_eq_next Delta.toCombMap R.dart (R.keep d)
  rw [R.val_keep hd, EdgeDeletion.next_of_ne_of_ne Delta.toCombMap R.dart hnext.1 hnext.2] at h
  rw [h, R.val_keep hnext]

/-- **The second dart of a path leaves a vertex of valence one.**  Let `d` follow `dart` on its
face, and let the walk across `d` run back to `alpha dart`.  Once the edge of `dart` is deleted,
the vertex rotation fixes `d`. -/
theorem sigma_keep_eq_self {d : Delta.toCombMap.Dart}
    (hd : d ≠ R.dart ∧ d ≠ Delta.toCombMap.alpha R.dart)
    (hnext : Delta.toCombMap.facePerm R.dart = d)
    (hback : Delta.toCombMap.facePerm (Delta.toCombMap.alpha d) =
      Delta.toCombMap.alpha R.dart) :
    R.diagram.toCombMap.sigma (R.keep d) = R.keep d := by
  apply R.val_injective
  rw [CombMap.sigma_eq_facePerm_alpha, R.alpha_keep hd]
  have h : R.val (R.diagram.toCombMap.facePerm (R.keep (Delta.toCombMap.alpha d))) =
      EdgeDeletion.next Delta.toCombMap R.dart (R.val (R.keep (Delta.toCombMap.alpha d))) :=
    EdgeDeletion.value_facePerm_eq_next Delta.toCombMap R.dart _
  have h1 : Delta.toCombMap.facePerm (Delta.toCombMap.alpha d) ≠ R.dart := by
    rw [hback]
    exact Delta.toCombMap.alpha_fixedPointFree R.dart
  have hfa : Delta.toCombMap.facePerm R.dart ≠ R.dart := by
    rw [hnext]
    exact hd.1
  rw [R.val_keep (R.offEdge_alpha hd), EdgeDeletion.next, if_neg h1, if_pos hback, if_neg hfa,
    hnext] at h
  rw [h, R.val_keep hd]

end Surgery.GFaceMerge

namespace GloballyDistinguishedSectionFamily

/-- **Removing a path between two `G`-faces, from the removal of a pendant path.**  Merge the two
faces across the first edge.  The rest of the path hangs from a vertex of valence one in the
merged face, and its removal takes away the other darts. -/
theorem separatingPathRemovalInput_of_pendant (hpendant : PendantPathRemovalInput.{u, w, v}) :
    SeparatingPathRemovalInput.{u, w, v} := by
  intro G _ Lambda W D lambda c eps Delta cuts S path first second hne hnodup hfs hfirst hsecond
    hjoints hsides
  obtain ⟨d0, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨h1, h2⟩ := hsides d0 (List.mem_cons.mpr (Or.inl rfl))
  subst h1
  subst h2
  obtain ⟨R, rfl⟩ : ∃ R : Surgery.GFaceMerge S.diagram, R.dart = d0 :=
    ⟨⟨d0, hfs, hfirst.1, hsecond.1, fun C hC => ⟨hfirst.2.1 C hC, hsecond.2.1 C hC⟩⟩, rfl⟩
  have havoid : ∀ b ∈ S.family, R.first ∉ b.1 ∧ R.second ∉ b.1 := fun b hb =>
    ⟨hfirst.2.2 b hb, hsecond.2.2 b hb⟩
  have hsum : (Surgery.GFaceMerge.transportDistinguished S R havoid).unboundSum = S.unboundSum :=
    Surgery.GFaceMerge.transportDistinguished_sum_unboundDarts_card S R havoid
  have hdarts := Surgery.GFaceMerge.transportDistinguished_dartCount_add_two S R havoid
  rcases rest with _ | ⟨d1, rest⟩
  · refine ⟨Surgery.GFaceMerge.transportDistinguished S R havoid, hsum, ?_⟩
    simp only [List.length_cons, List.length_nil]
    omega
  obtain ⟨hd0rest, hnodup'⟩ := List.nodup_cons.mp hnodup
  have hmem : ∀ d ∈ d1 :: rest, d ∈ R.dart :: d1 :: rest := fun d hd =>
    List.mem_cons.mpr (Or.inr hd)
  have hoff : ∀ d ∈ d1 :: rest, d ≠ R.dart ∧ d ≠ S.diagram.toCombMap.alpha R.dart := fun d hd =>
    ⟨fun h => hd0rest (h ▸ hd),
      fun h => hfs ((hsides d (hmem d hd)).1.symm.trans (congrArg S.diagram.toCombMap.faceOf h))⟩
  have hoffα : ∀ d ∈ d1 :: rest, S.diagram.toCombMap.alpha d ≠ R.dart ∧
      S.diagram.toCombMap.alpha d ≠ S.diagram.toCombMap.alpha R.dart := fun d hd =>
    R.offEdge_alpha (hoff d hd)
  have hface : ∀ x ∈ (d1 :: rest).map R.keep, R.diagram.toCombMap.faceOf x = R.merged ∧
      R.diagram.toCombMap.faceOf (R.diagram.toCombMap.alpha x) = R.merged := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    refine ⟨R.faceOf_keep_merged (hoff d hd) (Or.inl (hsides d (hmem d hd)).1), ?_⟩
    rw [R.alpha_keep (hoff d hd)]
    exact R.faceOf_keep_merged (hoffα d hd) (Or.inr (hsides d (hmem d hd)).2)
  have halpha : ∀ x ∈ (d1 :: rest).map R.keep,
      R.diagram.toCombMap.alpha x ∉ (d1 :: rest).map R.keep := by
    intro x hx hxα
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    obtain ⟨d', hd', hdd'⟩ := List.mem_map.mp hxα
    rw [R.alpha_keep (hoff d hd)] at hdd'
    have h := congrArg R.val hdd'
    rw [R.val_keep (hoff d' hd'), R.val_keep (hoffα d hd)] at h
    have h' := (hsides d' (hmem d' hd')).1
    rw [h] at h'
    exact hfs (h'.symm.trans (hsides d (hmem d hd)).2)
  have hj0 := hjoints 0 R.dart d1 (by simp) (by simp)
  have hleaf : ∀ x ∈ ((d1 :: rest).map R.keep).head?, R.diagram.toCombMap.sigma x = x := by
    intro x hx
    simp only [List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at hx
    subst hx
    exact R.sigma_keep_eq_self (hoff d1 (List.mem_cons.mpr (Or.inl rfl))) hj0.1 hj0.2
  have hjoints' : ∀ (j : ℕ) (e e' : R.diagram.toCombMap.Dart),
      ((d1 :: rest).map R.keep)[j]? = some e → ((d1 :: rest).map R.keep)[j + 1]? = some e' →
        R.diagram.toCombMap.facePerm e = e' ∧
          R.diagram.toCombMap.facePerm (R.diagram.toCombMap.alpha e') =
            R.diagram.toCombMap.alpha e := by
    intro j e e' he he'
    rw [List.getElem?_map, Option.map_eq_some_iff] at he he'
    obtain ⟨x, hx, rfl⟩ := he
    obtain ⟨y, hy, rfl⟩ := he'
    have hxy := hjoints (j + 1) x y (by simpa using hx) (by simpa using hy)
    have hxm : x ∈ d1 :: rest := List.mem_of_getElem? hx
    have hym : y ∈ d1 :: rest := List.mem_of_getElem? hy
    refine ⟨?_, ?_⟩
    · rw [R.facePerm_keep_of_ne (hoff x hxm) (by rw [hxy.1]; exact hoff y hym), hxy.1]
    · rw [R.alpha_keep (hoff y hym), R.alpha_keep (hoff x hxm),
        R.facePerm_keep_of_ne (hoffα y hym) (by rw [hxy.2]; exact hoffα x hxm), hxy.2]
  obtain ⟨U, hUsum, hUdarts⟩ := hpendant (Surgery.GFaceMerge.transportDistinguished S R havoid)
    R.merged ((d1 :: rest).map R.keep)
    ⟨R.merged_ne_outer, R.merged_not_relatorFace,
      Surgery.GFaceMerge.transportDistinguished_avoid_merged S R havoid⟩
    (by simp) (R.nodup_map_keep hoff hnodup') halpha hface hleaf hjoints'
  refine ⟨U, hUsum.trans hsum, ?_⟩
  rw [List.length_map] at hUdarts
  simp only [List.length_cons] at hUdarts ⊢
  omega

end GloballyDistinguishedSectionFamily

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.facePerm_keep_of_ne
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.sigma_keep_eq_self
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.separatingPathRemovalInput_of_pendant

end GroupApproximation.GGT.VanKampen
