import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94InsertionTransport
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ChainRespell
import GroupApproximation.GGT.VanKampen.FaceSetBoundaryWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Inserting a word across a G-face, from corner to corner

`GloballyDistinguishedSectionFamily.CornerInsertionInput` (`OsinLemma94ChainRespell`) is the first
move of the respelling of a cutting path.  An unselected `G`-face `f` reads `chain ++ rest` from
some base, every dart of `chain` has `f` on both sides, and `word` is a legal word with the value
of `chain`.  The split insertion of `word` from the corner before `chain` to the corner after it
(`GFaceWordInsertion.exists_split_corner_output`) carries the optimal family along
(`GloballyDistinguishedSectionFamily.insertionTransport`, `OsinLemma94InsertionTransport`).

* `GFaceWordInsertion.SplitOutput.dartCount_eq`: a split insertion adds exactly `2 * word.length`
  darts, since the old darts, the path and the reversed path are pairwise disjoint.
* `GFaceWordInsertion.SplitOutput.side_ne_outerFace`, `side_ne_cellFace`: a face that is no
  retained old face is neither the outer face nor a relator cell.
* `GloballyDistinguishedSectionFamily.cornerInsertionInput`: the transported `chain` runs along
  the prefix side, and the walk across it runs along the suffix side.  Its inner vertices keep
  valence two, because the walk across `chain` never reaches the last dart of `rest`: that dart
  is followed by the first dart of `chain`, and no dart of `chain` is across `chain`.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded

namespace CornerInsertion

/-- Consecutive entries of a chain are related. -/
theorem rel_of_getElem? {α : Type*} {r : α → α → Prop} :
    ∀ {l : List α}, l.IsChain r → ∀ {i : ℕ} {a b : α}, l[i]? = some a → l[i + 1]? = some b →
      r a b
  | [], _, _, _, _, ha, _ => by simp at ha
  | [_], _, _, _, _, _, hb => by simp at hb
  | _ :: _ :: _, h, 0, _, _, ha, hb => by
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at ha hb
      subst ha hb
      exact (List.isChain_cons_cons.mp h).1
  | _ :: _ :: _, h, i + 1, _, _, ha, hb => by
      rw [List.getElem?_cons_succ] at ha hb
      exact rel_of_getElem? (List.isChain_cons_cons.mp h).2 ha hb

theorem getElem?_map_of_getElem? {α β : Type*} (g : α → β) {l : List α} {i : ℕ} {a : α}
    (h : l[i]? = some a) : (l.map g)[i]? = some (g a) := by
  simp [h]

/-- Every length below the degree is the forward offset from `start` to some corner. -/
theorem exists_forwardOffset_eq {M : CombMap} {g : M.Face} (B : FaceBoundary M g)
    (start : Fin B.darts.length) {k : ℕ} (hk : k < B.darts.length) :
    ∃ finish : Fin B.darts.length, B.forwardOffset start finish = k := by
  have hs := start.isLt
  by_cases hsk : start.val + k < B.darts.length
  · refine ⟨⟨start.val + k, hsk⟩, ?_⟩
    change (if start.val ≤ start.val + k then start.val + k - start.val
      else B.darts.length + (start.val + k) - start.val) = k
    rw [if_pos (Nat.le_add_right _ _)]
    omega
  · refine ⟨⟨start.val + k - B.darts.length, by omega⟩, ?_⟩
    change (if start.val ≤ start.val + k - B.darts.length
      then start.val + k - B.darts.length - start.val
      else B.darts.length + (start.val + k - B.darts.length) - start.val) = k
    have hlt : ¬start.val ≤ start.val + k - B.darts.length := by omega
    rw [if_neg hlt]
    omega

end CornerInsertion

namespace GFaceWordInsertion.SplitOutput

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {Delta : DiscDiagram.{u, w, v} W} {f : Delta.toCombMap.Face}
  {k : Fin (Delta.faceBoundary f).darts.length} {word : List (RelLetter G Lambda)}
  (R : SplitOutput D Delta f k word)

theorem faceOf_of_mem_darts {x : R.diagram.toCombMap.Dart} (hx : x ∈ R.darts) :
    R.diagram.toCombMap.faceOf x = R.suffixSide :=
  ((R.diagram.faceBoundary R.suffixSide).mem_iff x).mp
    (by rw [R.suffixSide_darts]; exact List.mem_append.mpr (Or.inl hx))

theorem faceOf_of_mem_invDarts {x : R.diagram.toCombMap.Dart}
    (hx : x ∈ Embedded.invDarts R.diagram R.darts) :
    R.diagram.toCombMap.faceOf x = R.prefixSide :=
  ((R.diagram.faceBoundary R.prefixSide).mem_iff x).mp
    (by rw [R.prefixSide_darts]; exact List.mem_append.mpr (Or.inl hx))

/-- **A split insertion of `word` adds exactly `2 * word.length` darts.** -/
theorem dartCount_eq :
    R.diagram.toCombMap.dartCount = Delta.toCombMap.dartCount + 2 * word.length := by
  classical
  have hAB : Disjoint (Finset.univ.map R.embedding.darts) R.darts.toFinset := by
    rw [Finset.disjoint_left]
    intro x hx hxB
    obtain ⟨d, -, rfl⟩ := Finset.mem_map.mp hx
    exact R.path_disjoint _ (List.mem_toFinset.mp hxB) ⟨d, rfl⟩
  have hABC : Disjoint (Finset.univ.map R.embedding.darts ∪ R.darts.toFinset)
      (Embedded.invDarts R.diagram R.darts).toFinset := by
    rw [Finset.disjoint_left]
    intro x hx hxC
    have hC := List.mem_toFinset.mp hxC
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨d, -, rfl⟩ := Finset.mem_map.mp hx
      have halpha := (Embedded.mem_invDarts_iff R.darts _).mp hC
      rw [R.embedding.alpha d] at halpha
      exact R.path_disjoint _ halpha ⟨_, rfl⟩
    · exact R.prefixSide_ne_suffixSide
        ((R.faceOf_of_mem_invDarts hC).symm.trans
          (R.faceOf_of_mem_darts (List.mem_toFinset.mp hx)))
  have hle := Finset.card_le_univ
    ((Finset.univ.map R.embedding.darts ∪ R.darts.toFinset) ∪
      (Embedded.invDarts R.diagram R.darts).toFinset)
  rw [Finset.card_union_of_disjoint hABC, Finset.card_union_of_disjoint hAB, Finset.card_map,
    Finset.card_univ, List.toFinset_card_of_nodup R.nodup,
    List.toFinset_card_of_nodup (Embedded.invDarts_nodup R.nodup), Embedded.invDarts_length,
    R.length_eq] at hle
  have hge : Nat.card R.diagram.toCombMap.Dart ≤
      Nat.card Delta.toCombMap.Dart + 2 * word.length :=
    R.dartCount_le_add_two_mul
  change Nat.card R.diagram.toCombMap.Dart = Nat.card Delta.toCombMap.Dart + 2 * word.length
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hge ⊢
  omega

/-- A face that is no retained old face is not the outer face. -/
theorem side_ne_outerFace (hf : f ≠ Delta.outerFace) {side : R.diagram.toCombMap.Face}
    (hside : ∀ g, g ≠ f → R.embedding.faces g ≠ side) : side ≠ R.diagram.outerFace := by
  rw [R.embedding.outer]
  exact fun h => hside Delta.outerFace (Ne.symm hf) h.symm

/-- A face that is no retained old face is no relator cell. -/
theorem side_ne_cellFace (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f)
    {side : R.diagram.toCombMap.Face} (hside : ∀ g, g ≠ f → R.embedding.faces g ≠ side) :
    ∀ C ∈ R.diagram.relatorCells, C.face ≠ side := by
  intro C hC
  rw [R.cellMap.list_eq] at hC
  obtain ⟨C0, hC0, rfl⟩ := List.mem_map.mp hC
  rw [R.cellMap.face_eq]
  exact hside _ (hcells C0 hC0)

end GFaceWordInsertion.SplitOutput

namespace GloballyDistinguishedSectionFamily

/-- **Inserting a word across a `G`-face, from corner to corner.**  The word goes in between the
corners before and after `chain` and the optimal family follows.  The transported `chain` has
the prefix side on its left and the suffix side on its right. -/
theorem cornerInsertionInput : CornerInsertionInput.{u, w, v} := by
  intro _ _ _ _ D _ _ _ _ _ S f r chain rest word hunsel hsplit hchain hface hfree hruns hne hword
    hval
  have hrest : ∀ x ∈ chain, S.diagram.toCombMap.alpha x ∈ rest := by
    intro x hx
    have h : S.diagram.toCombMap.alpha x ∈ chain ++ rest := by
      rw [← hsplit, List.mem_rotate]
      exact ((S.diagram.faceBoundary f).mem_iff _).mpr (hface x hx)
    rcases List.mem_append.mp h with h | h
    · exact absurd h (hfree x hx)
    · exact h
  have hx0 := List.head_mem hchain
  have hcpos : 0 < chain.length := List.length_pos_of_mem hx0
  have hrpos : 0 < rest.length := List.length_pos_of_mem (hrest _ hx0)
  have hlen : (S.diagram.faceBoundary f).darts.length = chain.length + rest.length := by
    rw [← List.length_rotate (S.diagram.faceBoundary f).darts r, hsplit, List.length_append]
  obtain ⟨start, hstart⟩ : ∃ start : Fin (S.diagram.faceBoundary f).darts.length,
      start.val = r % (S.diagram.faceBoundary f).darts.length :=
    ⟨⟨r % (S.diagram.faceBoundary f).darts.length, Nat.mod_lt r (by omega)⟩, rfl⟩
  have hrot : (S.diagram.faceBoundary f).darts.rotate start.val = chain ++ rest := by
    rw [hstart, List.rotate_mod, hsplit]
  obtain ⟨finish, hoff⟩ :=
    CornerInsertion.exists_forwardOffset_eq (S.diagram.faceBoundary f) start (k := chain.length)
      (by omega)
  have htake : ((S.diagram.faceBoundary f).darts.rotate start.val).take
      ((S.diagram.faceBoundary f).forwardOffset start finish) = chain := by
    rw [hrot, hoff]
    exact List.take_left' rfl
  have hdrop : ((S.diagram.faceBoundary f).darts.rotate start.val).drop
      ((S.diagram.faceBoundary f).forwardOffset start finish) = rest := by
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
  have hprefix : ∀ x ∈ chain,
      R.diagram.toCombMap.faceOf (R.embedding.darts x) = R.prefixSide := by
    intro x hx
    refine ((R.diagram.faceBoundary R.prefixSide).mem_iff _).mp ?_
    rw [GFaceWordInsertion.SplitCornerOutput.prefixSide_darts_original R, htake]
    exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨x, hx, rfl⟩))
  have hacross : ∀ x ∈ chain,
      R.diagram.toCombMap.faceOf (R.diagram.toCombMap.alpha (R.embedding.darts x)) =
        R.suffixSide := by
    intro x hx
    rw [R.embedding.alpha x]
    refine ((R.diagram.faceBoundary R.suffixSide).mem_iff _).mp ?_
    rw [GFaceWordInsertion.SplitCornerOutput.suffixSide_darts_original R, hdrop]
    exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_, hrest x hx, rfl⟩))
  have hnodup : (chain.map R.embedding.darts).Nodup := by
    have h : (chain ++ rest).Nodup := by
      rw [← hsplit]
      exact List.nodup_rotate.mpr (S.diagram.faceBoundary f).nodup
    exact List.Nodup.map R.embedding.darts.injective (List.nodup_append.mp h).1
  have hpathlen : (chain.map R.embedding.darts).length = chain.length :=
    List.length_map _
  have hback : List.IsChain (fun d e => S.diagram.toCombMap.facePerm d = e) (rest ++ chain) := by
    have h := ((S.diagram.faceBoundary f).rotate (r + chain.length)).chain
    change List.IsChain _ ((S.diagram.faceBoundary f).darts.rotate (r + chain.length)) at h
    rw [← List.rotate_rotate, hsplit, List.rotate_append_length_eq] at h
    exact h
  have hjoint : ∀ (j : ℕ) (e e' : R.diagram.toCombMap.Dart),
      (chain.map R.embedding.darts)[j]? = some e →
        (chain.map R.embedding.darts)[j + 1]? = some e' →
          R.diagram.toCombMap.facePerm e = e' ∧
            R.diagram.toCombMap.facePerm (R.diagram.toCombMap.alpha e') =
              R.diagram.toCombMap.alpha e := by
    intro j e e' he he'
    rw [List.getElem?_map, Option.map_eq_some_iff] at he he'
    obtain ⟨x, hx, rfl⟩ := he
    obtain ⟨x', hx', rfl⟩ := he'
    constructor
    · have hP := (R.diagram.faceBoundary R.prefixSide).chain
      rw [GFaceWordInsertion.SplitCornerOutput.prefixSide_darts_original R, htake] at hP
      exact CornerInsertion.rel_of_getElem? (List.isChain_append.mp hP).2.1
        (CornerInsertion.getElem?_map_of_getElem? R.embedding.darts hx)
        (CornerInsertion.getElem?_map_of_getElem? R.embedding.darts hx')
    · have hruns' : S.diagram.toCombMap.facePerm (S.diagram.toCombMap.alpha x') =
          S.diagram.toCombMap.alpha x :=
        hruns j x x' hx hx'
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (hrest x' (List.mem_of_getElem? hx'))
      have hi_lt : i < rest.length := (List.getElem?_eq_some_iff.mp hi).1
      obtain ⟨y, hy⟩ : ∃ y, (rest ++ chain)[i + 1]? = some y :=
        ⟨_, List.getElem?_eq_getElem (by rw [List.length_append]; omega)⟩
      have hnext : rest[i + 1]? = some (S.diagram.toCombMap.alpha x) := by
        have hfy : S.diagram.toCombMap.facePerm (S.diagram.toCombMap.alpha x') = y :=
          CornerInsertion.rel_of_getElem? hback ((List.getElem?_append_left hi_lt).trans hi) hy
        rw [hruns'] at hfy
        subst hfy
        by_cases hlt : i + 1 < rest.length
        · rwa [List.getElem?_append_left hlt] at hy
        · have hge : rest.length ≤ i + 1 := by omega
          rw [List.getElem?_append_right hge] at hy
          exact absurd (List.mem_of_getElem? hy) (hfree x (List.mem_of_getElem? hx))
      have hQ := (R.diagram.faceBoundary R.suffixSide).chain
      rw [GFaceWordInsertion.SplitCornerOutput.suffixSide_darts_original R, hdrop] at hQ
      have hwalk : R.diagram.toCombMap.facePerm (R.embedding.darts (S.diagram.toCombMap.alpha x')) =
          R.embedding.darts (S.diagram.toCombMap.alpha x) :=
        CornerInsertion.rel_of_getElem? (List.isChain_append.mp hQ).2.1
          (CornerInsertion.getElem?_map_of_getElem? R.embedding.darts hi)
          (CornerInsertion.getElem?_map_of_getElem? R.embedding.darts hnext)
      rw [R.embedding.alpha x', R.embedding.alpha x]
      exact hwalk
  have hfirst : (insertionTransport S R hunsel.2.2).UnselectedGFace R.prefixSide :=
    ⟨GFaceWordInsertion.SplitOutput.side_ne_outerFace R hunsel.1 R.prefixSide_not_kept,
      GFaceWordInsertion.SplitOutput.side_ne_cellFace R hunsel.2.1 R.prefixSide_not_kept,
      fun a ha => (insertionTransport_avoid S R hunsel.2.2 a ha).1⟩
  have hsecond : (insertionTransport S R hunsel.2.2).UnselectedGFace R.suffixSide :=
    ⟨GFaceWordInsertion.SplitOutput.side_ne_outerFace R hunsel.1 R.suffixSide_not_kept,
      GFaceWordInsertion.SplitOutput.side_ne_cellFace R hunsel.2.1 R.suffixSide_not_kept,
      fun a ha => (insertionTransport_avoid S R hunsel.2.2 a ha).2⟩
  exact ⟨insertionTransport S R hunsel.2.2, insertionTransport_unboundSum S R hunsel.2.2,
    GFaceWordInsertion.SplitOutput.dartCount_eq R, chain.map R.embedding.darts, hpathlen, hnodup,
    hjoint, R.prefixSide, R.suffixSide, R.prefixSide_ne_suffixSide, hfirst, hsecond,
    fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact ⟨hprefix y hy, hacross y hy⟩⟩

end GloballyDistinguishedSectionFamily

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.SplitOutput.dartCount_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.cornerInsertionInput
