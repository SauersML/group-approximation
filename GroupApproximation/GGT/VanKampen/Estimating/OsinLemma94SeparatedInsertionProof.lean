import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CornerInsertion
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SeparatedInsertion
import GroupApproximation.Meta.AxiomGuard

/-!
# Proof of the separated corner insertion

Osin (math/0411039v3, §9), Lemma 9.4, Case 2: "This contradicts our assumption that `∑ l(t_i)`
is minimal."  `GloballyDistinguishedSectionFamily.SeparatedCornerInsertionInput`
(`OsinLemma94SeparatedInsertion`) is the insertion step of Case 2.  An unselected `G`-face `f`
reads `front ++ back` from some base, `path` is a segment of `back` whose reverse darts lie in
`front`, and `word` has the value of `front`.  The split insertion of `word` from the corner before
`front` to the corner after it (`GFaceWordInsertion.exists_split_corner_output`) carries the
optimal family along (`GloballyDistinguishedSectionFamily.insertionTransport`,
`OsinLemma94InsertionTransport`).

* The suffix side reads the new path and then `back`, so the transported `path` runs along it.
  The prefix side reads the reversed new path and then `front`, so the walk across `path` runs
  along it.  The two sides are different faces, and neither is a retained old face.
* The walk across `path` stays inside `front`.  A dart across `path` is followed on the old walk
  by the dart across the previous dart of `path`.  That dart lies in `front`, so it is not the
  first dart of `back`, since the walk has no dart twice.  So the inner vertices of the
  transported `path` keep valence two.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded

namespace GloballyDistinguishedSectionFamily

/-- **Inserting a word that separates a path from its reverse.**  Osin (math/0411039v3, §9),
Lemma 9.4, Case 2: "This contradicts our assumption that `∑ l(t_i)` is minimal."  The word goes
in between the corners before and after `front`, and the optimal family follows.  The
transported `path` has the suffix side on its left and the prefix side on its right. -/
theorem separatedCornerInsertionInput : SeparatedCornerInsertionInput.{u, w, v} := by
  intro _ _ _ _ D _ _ _ _ _ S f r front back path word hunsel hsplit hback hinfix hacross hruns
    hne hword hval
  have hlen : (S.diagram.faceBoundary f).darts.length = front.length + back.length := by
    rw [← List.length_rotate (S.diagram.faceBoundary f).darts r, hsplit, List.length_append]
  have hbpos : 0 < back.length := List.length_pos_iff.mpr hback
  obtain ⟨start, hstart⟩ : ∃ start : Fin (S.diagram.faceBoundary f).darts.length,
      start.val = r % (S.diagram.faceBoundary f).darts.length :=
    ⟨⟨r % (S.diagram.faceBoundary f).darts.length, Nat.mod_lt r (by omega)⟩, rfl⟩
  have hrot : (S.diagram.faceBoundary f).darts.rotate start.val = front ++ back := by
    rw [hstart, List.rotate_mod, hsplit]
  obtain ⟨finish, hoff⟩ :=
    CornerInsertion.exists_forwardOffset_eq (S.diagram.faceBoundary f) start (k := front.length)
      (by omega)
  have htake : ((S.diagram.faceBoundary f).darts.rotate start.val).take
      ((S.diagram.faceBoundary f).forwardOffset start finish) = front := by
    rw [hrot, hoff]
    exact List.take_left' rfl
  have hdrop : ((S.diagram.faceBoundary f).darts.rotate start.val).drop
      ((S.diagram.faceBoundary f).forwardOffset start finish) = back := by
    rw [hrot, hoff]
    exact List.drop_left' rfl
  have hinv : ∀ l ∈ word, (symmetricLabelAlphabet D).IsLetter (HullSC.RelWord.inv l) := by
    intro l hl
    have hletter := hword l hl
    cases l with
    | base x => exact symmetricLabelAlphabet.symmetric D x hletter
    | comp i x => exact ((symmetricLabelAlphabet D).fam i).inv_mem hletter
  have hvalue : RelLetter.listVal word = RelLetter.listVal
      ((((S.diagram.faceBoundary f).darts.rotate start.val).take
        ((S.diagram.faceBoundary f).forwardOffset start finish)).map S.diagram.label) := by
    rw [htake]
    exact hval
  obtain ⟨R⟩ := GFaceWordInsertion.exists_split_corner_output (symmetricLabelAlphabet D)
    S.diagram S.label_admissible f hunsel.1 hunsel.2.1 start finish word hne hword hinv hvalue
  have hsuffix : ∀ x ∈ back,
      R.diagram.toCombMap.faceOf (R.embedding.darts x) = R.suffixSide := by
    intro x hx
    refine ((R.diagram.faceBoundary R.suffixSide).mem_iff _).mp ?_
    rw [GFaceWordInsertion.SplitCornerOutput.suffixSide_darts_original R, hdrop]
    exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨x, hx, rfl⟩))
  have hprefix : ∀ x ∈ front,
      R.diagram.toCombMap.faceOf (R.embedding.darts x) = R.prefixSide := by
    intro x hx
    refine ((R.diagram.faceBoundary R.prefixSide).mem_iff _).mp ?_
    rw [GFaceWordInsertion.SplitCornerOutput.prefixSide_darts_original R, htake]
    exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨x, hx, rfl⟩))
  have hacrossR : ∀ x ∈ path,
      R.diagram.toCombMap.faceOf (R.diagram.toCombMap.alpha (R.embedding.darts x)) =
        R.prefixSide := by
    intro x hx
    rw [R.embedding.alpha x]
    exact hprefix _ (hacross x hx)
  have hwalk : (front ++ back).Nodup := by
    rw [← hsplit]
    exact List.nodup_rotate.mpr (S.diagram.faceBoundary f).nodup
  have hnodup : (path.map R.embedding.darts).Nodup :=
    List.Nodup.map R.embedding.darts.injective
      (List.Nodup.sublist hinfix.sublist (List.nodup_append.mp hwalk).2.1)
  have hpathlen : (path.map R.embedding.darts).length = path.length :=
    List.length_map _
  have hwalkchain :
      List.IsChain (fun d e => S.diagram.toCombMap.facePerm d = e) (front ++ back) := by
    have h := ((S.diagram.faceBoundary f).rotate r).chain
    change List.IsChain _ ((S.diagram.faceBoundary f).darts.rotate r) at h
    rw [hsplit] at h
    exact h
  have hjoint : ∀ (j : ℕ) (e e' : R.diagram.toCombMap.Dart),
      (path.map R.embedding.darts)[j]? = some e →
        (path.map R.embedding.darts)[j + 1]? = some e' →
          R.diagram.toCombMap.facePerm e = e' ∧
            R.diagram.toCombMap.facePerm (R.diagram.toCombMap.alpha e') =
              R.diagram.toCombMap.alpha e := by
    intro j e e' he he'
    rw [List.getElem?_map, Option.map_eq_some_iff] at he he'
    obtain ⟨x, hx, rfl⟩ := he
    obtain ⟨x', hx', rfl⟩ := he'
    constructor
    · obtain ⟨s, t, hst⟩ := hinfix
      have hoffset : ∀ {i : ℕ} {y : S.diagram.toCombMap.Dart}, path[i]? = some y →
          back[s.length + i]? = some y := by
        intro i y hy
        have hi : i < path.length := (List.getElem?_eq_some_iff.mp hy).1
        rw [← hst, List.append_assoc, List.getElem?_append_right (Nat.le_add_right s.length i),
          Nat.add_sub_cancel_left, List.getElem?_append_left hi]
        exact hy
      have hnext : back[s.length + j + 1]? = some x' := by
        rw [Nat.add_assoc]
        exact hoffset hx'
      have hQ := (R.diagram.faceBoundary R.suffixSide).chain
      rw [GFaceWordInsertion.SplitCornerOutput.suffixSide_darts_original R, hdrop] at hQ
      exact CornerInsertion.rel_of_getElem? (List.isChain_append.mp hQ).2.1
        (CornerInsertion.getElem?_map_of_getElem? R.embedding.darts (hoffset hx))
        (CornerInsertion.getElem?_map_of_getElem? R.embedding.darts hnext)
    · have hruns' : S.diagram.toCombMap.facePerm (S.diagram.toCombMap.alpha x') =
          S.diagram.toCombMap.alpha x :=
        hruns j x x' hx hx'
      have hfrontx : S.diagram.toCombMap.alpha x ∈ front :=
        hacross x (List.mem_of_getElem? hx)
      obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp (hacross x' (List.mem_of_getElem? hx'))
      have hp_lt : p < front.length := (List.getElem?_eq_some_iff.mp hp).1
      obtain ⟨y, hy⟩ : ∃ y, (front ++ back)[p + 1]? = some y :=
        ⟨_, List.getElem?_eq_getElem (by rw [List.length_append]; omega)⟩
      have hnext : front[p + 1]? = some (S.diagram.toCombMap.alpha x) := by
        have hfy : S.diagram.toCombMap.facePerm (S.diagram.toCombMap.alpha x') = y :=
          CornerInsertion.rel_of_getElem? hwalkchain
            ((List.getElem?_append_left hp_lt).trans hp) hy
        rw [hruns'] at hfy
        subst hfy
        by_cases hlt : p + 1 < front.length
        · rwa [List.getElem?_append_left hlt] at hy
        · rw [List.getElem?_append_right (by omega : front.length ≤ p + 1)] at hy
          exact ((List.nodup_append.mp hwalk).2.2 _ hfrontx _ (List.mem_of_getElem? hy) rfl).elim
      have hP := (R.diagram.faceBoundary R.prefixSide).chain
      rw [GFaceWordInsertion.SplitCornerOutput.prefixSide_darts_original R, htake] at hP
      rw [R.embedding.alpha x', R.embedding.alpha x]
      exact CornerInsertion.rel_of_getElem? (List.isChain_append.mp hP).2.1
        (CornerInsertion.getElem?_map_of_getElem? R.embedding.darts hp)
        (CornerInsertion.getElem?_map_of_getElem? R.embedding.darts hnext)
  have hfirst : (insertionTransport S R hunsel.2.2).UnselectedGFace R.suffixSide :=
    ⟨GFaceWordInsertion.SplitOutput.side_ne_outerFace R hunsel.1 R.suffixSide_not_kept,
      GFaceWordInsertion.SplitOutput.side_ne_cellFace R hunsel.2.1 R.suffixSide_not_kept,
      fun a ha => (insertionTransport_avoid S R hunsel.2.2 a ha).2⟩
  have hsecond : (insertionTransport S R hunsel.2.2).UnselectedGFace R.prefixSide :=
    ⟨GFaceWordInsertion.SplitOutput.side_ne_outerFace R hunsel.1 R.prefixSide_not_kept,
      GFaceWordInsertion.SplitOutput.side_ne_cellFace R hunsel.2.1 R.prefixSide_not_kept,
      fun a ha => (insertionTransport_avoid S R hunsel.2.2 a ha).1⟩
  exact ⟨insertionTransport S R hunsel.2.2, insertionTransport_unboundSum S R hunsel.2.2,
    (GFaceWordInsertion.SplitOutput.dartCount_eq R).le, path.map R.embedding.darts, hpathlen,
    hnodup, hjoint, R.suffixSide, R.prefixSide, R.prefixSide_ne_suffixSide.symm, hfirst, hsecond,
    fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact ⟨hsuffix y (hinfix.subset hy), hacrossR y hy⟩⟩

end GloballyDistinguishedSectionFamily

end GroupApproximation.GGT.VanKampen

#audit_closed_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.separatedCornerInsertionInput
