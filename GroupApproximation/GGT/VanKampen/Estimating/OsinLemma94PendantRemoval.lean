import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SpikeTransport
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ChainRespell
import GroupApproximation.Meta.AxiomGuard

/-!
# Removing a pendant path from an unselected G-face

Osin (math/0411039v3, §9), Lemma 9.4, Case 2: "This contradicts our assumption that `∑ l(t_i)` is
minimal."  The respelling of a cutting path (`OsinLemma94ChainRespell`) ends with a path that
hangs inside one unselected `G`-face: every dart of the path has that face on both sides, the
path starts at a vertex of valence one and runs through vertices of valence two.  Deleting its
first edge is a spike deletion (`Surgery.SpikeDeletion`).  The rest of the path then hangs from a
vertex of valence one inside the shrunk face, which is again unselected, so the path goes edge by
edge.  Each deletion carries the distinguished family along with the same unbound sum
(`Surgery.SpikeDeletion.transportDistinguished`) and removes two darts.

* `Surgery.SpikeDeletion.facePerm_keep_of_ne`: a dart off the deleted edge whose successor is off
  the edge keeps its successor.
* `Surgery.SpikeDeletion.sigma_keep_eq_self`: the second dart of the path leaves a vertex of
  valence one once the first edge is deleted.
* `GloballyDistinguishedSectionFamily.pendantPathRemovalInput`: the whole path goes, with the same
  unbound sum and `2 * path.length` fewer darts.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded

namespace Surgery.SpikeDeletion

open scoped Classical

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W} (R : SpikeDeletion Delta)

/-- **A dart keeps its successor.**  A dart off the deleted edge whose successor is off the edge
has the same successor after the deletion. -/
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

end Surgery.SpikeDeletion

namespace GloballyDistinguishedSectionFamily

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- `pendantPathRemovalInput`, by induction on the length of the path. -/
theorem pendantPathRemoval_of_length (n : ℕ) :
    ∀ (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (f : S.diagram.toCombMap.Face) (path : List S.diagram.toCombMap.Dart),
      path.length = n → S.UnselectedGFace f → path.Nodup →
      (∀ d ∈ path, S.diagram.toCombMap.alpha d ∉ path) →
      (∀ d ∈ path, S.diagram.toCombMap.faceOf d = f ∧
        S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) = f) →
      (∀ d ∈ path.head?, S.diagram.toCombMap.sigma d = d) →
      S.DegreeTwoJoints path →
        ∃ T : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
          T.unboundSum = S.unboundSum ∧
          T.diagram.toCombMap.dartCount + 2 * path.length = S.diagram.toCombMap.dartCount := by
  induction n with
  | zero =>
    intro S _ path hlen _ _ _ _ _ _
    exact ⟨S, rfl, by rw [hlen, Nat.mul_zero, Nat.add_zero]⟩
  | succ n ih =>
    intro S f path hlen hf hnodup halpha hface htip hjoint
    cases path with
    | nil =>
      rw [List.length_nil] at hlen
      omega
    | cons d tail =>
      have htl : tail.length = n := by
        rw [List.length_cons] at hlen
        omega
      have hfd : S.diagram.toCombMap.faceOf d = f := (hface d List.mem_cons_self).1
      subst hfd
      obtain ⟨R, rfl⟩ : ∃ R : Surgery.SpikeDeletion S.diagram, R.dart = d :=
        ⟨⟨d, htip d (by simp), hf.1, hf.2.1⟩, rfl⟩
      have havoid : ∀ b ∈ S.family, R.face ∉ b.1 := hf.2.2
      have hnd := List.nodup_cons.mp hnodup
      have hoff : ∀ x ∈ tail, x ≠ R.dart ∧ x ≠ S.diagram.toCombMap.alpha R.dart := by
        intro x hx
        refine ⟨fun h => hnd.1 ?_, fun h => halpha R.dart List.mem_cons_self ?_⟩
        · rw [← h]
          exact hx
        · rw [← h]
          exact List.mem_cons_of_mem _ hx
      have hoffα : ∀ x ∈ tail, S.diagram.toCombMap.alpha x ≠ R.dart ∧
          S.diagram.toCombMap.alpha x ≠ S.diagram.toCombMap.alpha R.dart :=
        fun x hx => R.offEdge_alpha (hoff x hx)
      have halpha' :
          ∀ e ∈ tail.map R.keep, R.diagram.toCombMap.alpha e ∉ tail.map R.keep := by
        intro e he hmem
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
        rw [R.alpha_keep (hoff x hx)] at hmem
        obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hmem
        have hyx : y = S.diagram.toCombMap.alpha x :=
          (R.val_keep (hoff y hy)).symm.trans
            ((congrArg R.val hxy).trans (R.val_keep (hoffα x hx)))
        refine halpha x (List.mem_cons_of_mem _ hx) ?_
        rw [← hyx]
        exact List.mem_cons_of_mem _ hy
      have hface' : ∀ e ∈ tail.map R.keep, R.diagram.toCombMap.faceOf e = R.shrunk ∧
          R.diagram.toCombMap.faceOf (R.diagram.toCombMap.alpha e) = R.shrunk := by
        intro e he
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
        have hx' := hface x (List.mem_cons_of_mem _ hx)
        refine ⟨R.faceOf_keep_shrunk (hoff x hx) hx'.1, ?_⟩
        rw [R.alpha_keep (hoff x hx)]
        exact R.faceOf_keep_shrunk (hoffα x hx) hx'.2
      have htip' : ∀ e ∈ (tail.map R.keep).head?, R.diagram.toCombMap.sigma e = e := by
        intro e he
        cases tail with
        | nil => simp at he
        | cons d1 rest =>
          simp only [List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at he
          subst he
          have hj := hjoint 0 R.dart d1 (by simp) (by simp)
          exact R.sigma_keep_eq_self (hoff d1 List.mem_cons_self) hj.1 hj.2
      have hjoint' : ∀ (j : ℕ) (e e' : R.diagram.toCombMap.Dart),
          (tail.map R.keep)[j]? = some e → (tail.map R.keep)[j + 1]? = some e' →
            R.diagram.toCombMap.facePerm e = e' ∧
              R.diagram.toCombMap.facePerm (R.diagram.toCombMap.alpha e') =
                R.diagram.toCombMap.alpha e := by
        intro j e e' he he'
        rw [List.getElem?_map, Option.map_eq_some_iff] at he he'
        obtain ⟨x, hx, rfl⟩ := he
        obtain ⟨y, hy, rfl⟩ := he'
        have hxy := hjoint (j + 1) x y (by simpa using hx) (by simpa using hy)
        have hxm : x ∈ tail := List.mem_of_getElem? hx
        have hym : y ∈ tail := List.mem_of_getElem? hy
        refine ⟨?_, ?_⟩
        · rw [R.facePerm_keep_of_ne (hoff x hxm) (by rw [hxy.1]; exact hoff y hym), hxy.1]
        · rw [R.alpha_keep (hoff y hym), R.alpha_keep (hoff x hxm),
            R.facePerm_keep_of_ne (hoffα y hym) (by rw [hxy.2]; exact hoffα x hxm), hxy.2]
      obtain ⟨T, hTsum, hTdarts⟩ :=
        ih (Surgery.SpikeDeletion.transportDistinguished S R havoid) R.shrunk (tail.map R.keep)
          (by rw [List.length_map, htl])
          ⟨R.shrunk_ne_outer, R.shrunk_not_relatorFace,
            Surgery.SpikeDeletion.transportDistinguished_avoid_shrunk S R havoid⟩
          (R.nodup_map_keep hoff hnd.2) halpha' hface' htip' hjoint'
      refine ⟨T,
        hTsum.trans (Surgery.SpikeDeletion.transportDistinguished_unboundSum S R havoid), ?_⟩
      have hdarts := Surgery.SpikeDeletion.transportDistinguished_dartCount_add_two S R havoid
      rw [List.length_map] at hTdarts
      rw [List.length_cons]
      omega

/-- **Removing a pendant path from an unselected G-face.**  A path that hangs inside an
unselected `G`-face, from a vertex of valence one through vertices of valence two, is deleted
edge by edge.  The distinguished family follows with the same unbound sum, and every edge removes
two darts. -/
theorem pendantPathRemovalInput : PendantPathRemovalInput.{u, w, v} := by
  intro _ _ _ _ _ _ _ _ _ _ S f path hf _ hnodup halpha hface htip hjoint
  exact pendantPathRemoval_of_length _ S f path rfl hf hnodup halpha hface htip hjoint

end GloballyDistinguishedSectionFamily

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.SpikeDeletion.facePerm_keep_of_ne
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.SpikeDeletion.sigma_keep_eq_self
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.pendantPathRemoval_of_length
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.pendantPathRemovalInput
