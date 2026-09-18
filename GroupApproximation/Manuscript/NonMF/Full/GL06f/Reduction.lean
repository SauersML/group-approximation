import GroupApproximation.Manuscript.NonMF.Full.GL06f.Statement
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketLakeAbsorption
import GroupApproximation.Meta.AxiomGuard

/-!
# The rose step from the sub-arc region move

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), rose configuration.  A sub-arc region
move (`RoseRegionMoveSubArcStatement`) gives a colouring `z` of darts and a rearrangement
`s_1 t_1 s_2 t_2` of the kept boundary darts.  In the same diagram, the moved face set
`flipFaces K.faces z` with the boundary cycle `s_1 t_1 s_2 t_2` is a pocket.

* Its boundary darts are exactly the kept darts of the old cycle (`isBoundaryDart_flipFaces_iff`).
* It has strictly fewer repeated visits (`rose_of_regionMoveSubArc`).  Walking round the old closed
  walk from a kept dart to a dropped one passes a kept dart `e` followed by a dropped dart `f`.  In
  the new closed walk `e` has a successor `x` starting at the vertex where `f` starts, so the
  vertices of the kept darts and of the dropped darts overlap.  Every dropped dart takes away one
  from the length, while together they take away strictly fewer vertices.

The proofs here are independent: foreign modules were read only for the statement shapes.

## Manuscript status

Infrastructure for `thm:hull` (`non_mf_groups_exist.tex`; Hull's small cancellation theorem,
through Osin's Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.GL06f

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.Surgery.MapCollapse
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

/-! ## Face sets after a move -/

/-- A function constant along a relation is constant along its equivalence closure. -/
theorem eq_of_eqvGen_of_step {α : Type*} {β : Type*} {r : α → α → Prop} {z : α → β}
    (hz : ∀ x y, r x y → z x = z y) {x y : α} (h : Relation.EqvGen r x y) : z x = z y := by
  induction h with
  | rel x₁ x₂ hx => exact hz x₁ x₂ hx
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Membership in the moved face set** (for `thm:hull`): with `z` constant on face classes, a
face is in `flipFaces faces z` exactly when its membership in `faces` agrees with `z = false`. -/
theorem mem_flipFaces_iff {M : CombMap.{v}} {faces : Finset M.Face} {keep : M.Dart → Prop}
    {z : M.Dart → Bool} (hz : ∀ x y, CombMap.FaceClassStep M keep x y → z x = z y)
    (d : M.Dart) :
    M.faceOf d ∈ flipFaces M faces z ↔ (M.faceOf d ∈ faces ↔ z d = false) := by
  unfold flipFaces
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨_, x, hx, hiff⟩
    have hzx : z x = z d :=
      eq_of_eqvGen_of_step hz
        (eqvGen_faceClass_of_sameCycle M keep ((M.faceOf_eq_iff x d).mp hx))
    rwa [hx, hzx] at hiff
  · intro h
    exact ⟨Finset.mem_univ _, d, rfl, h⟩

/-- **The boundary of the moved face set** (for `thm:hull`).  Let `c` enumerate the boundary darts
of `faces`, `z` be constant on the face classes of the walk `c`, and never flip both sides of a
dart of `c`.  The boundary darts of `flipFaces faces z` are the darts of `c` with neither side
flipped. -/
theorem isBoundaryDart_flipFaces_iff {M : CombMap.{v}} {faces : Finset M.Face} {c : List M.Dart}
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M faces d) {z : M.Dart → Bool}
    (hz : ∀ x y, CombMap.FaceClassStep M (walkKeep M c) x y → z x = z y)
    (hind : ∀ d ∈ c, z d = false ∨ z (M.alpha d) = false) (d : M.Dart) :
    Surgery.MapCollapse.IsBoundaryDart M (flipFaces M faces z) d ↔
      d ∈ c ∧ GL05b.movePred M z d = true := by
  rw [GL05b.movePred_eq_true_iff]
  change (M.faceOf d ∈ flipFaces M faces z ∧ M.faceOf (M.alpha d) ∉ flipFaces M faces z) ↔ _
  rw [mem_flipFaces_iff hz d, mem_flipFaces_iff hz (M.alpha d)]
  by_cases hd : d ∈ c
  · obtain ⟨h1, h2⟩ := (hc d).mp hd
    constructor
    · rintro ⟨hl, hr⟩
      refine ⟨hd, hl.mp h1, ?_⟩
      by_contra hne
      exact hr ⟨fun h => absurd h h2, fun h => absurd h hne⟩
    · rintro ⟨_, hzd, hza⟩
      exact ⟨⟨fun _ => hzd, fun _ => h1⟩, fun h => h2 (h.mpr hza)⟩
  · constructor
    · rintro ⟨hl, hr⟩
      by_cases ha : M.alpha d ∈ c
      · obtain ⟨h1, h2⟩ := (hc (M.alpha d)).mp ha
        rw [M.alpha_involutive d] at h2
        have hza : z (M.alpha d) ≠ false := fun h => hr ⟨fun _ => h, fun _ => h1⟩
        have hzd : z d = false := by
          rcases hind (M.alpha d) ha with h | h
          · exact absurd h hza
          · rwa [M.alpha_involutive d] at h
        exact absurd (hl.mpr hzd) h2
      · have hoff : ¬walkKeep M c d := fun h => Or.elim h hd ha
        have hstep : CombMap.FaceClassStep M (walkKeep M c) d (M.alpha d) := Or.inr ⟨hoff, rfl⟩
        have hzeq : z d = z (M.alpha d) := hz d (M.alpha d) hstep
        have hFeq : M.faceOf d ∈ faces ↔ M.faceOf (M.alpha d) ∈ faces :=
          GL05b.faceOf_mem_iff_of_walkEqvGen hc (Relation.EqvGen.rel _ _ hstep)
        exact hr (hFeq.symm.trans (hl.trans (iff_of_eq (congrArg (fun b => b = false) hzeq))))
    · rintro ⟨h, _⟩
      exact absurd h hd

/-! ## Transitions along a closed walk -/

/-- In a chain, every entry has a successor, except possibly the last entry. -/
theorem exists_succ_or_eq_getLast {α : Type*} {R : α → α → Prop} :
    ∀ {L : List α}, L.IsChain R → ∀ (hne : L ≠ []) {e : α}, e ∈ L →
      (∃ x ∈ L, R e x) ∨ e = L.getLast hne
  | [], _, hne, _, _ => (hne rfl).elim
  | [_], _, _, _, he => Or.inr (by rw [List.getLast_singleton]; exact List.mem_singleton.mp he)
  | a :: b :: l, hL, _, _, he => by
      rw [List.isChain_cons_cons] at hL
      rcases List.mem_cons.mp he with h | he'
      · rw [h]
        exact Or.inl ⟨b, List.mem_cons_of_mem a List.mem_cons_self, hL.1⟩
      · rcases exists_succ_or_eq_getLast hL.2 (List.cons_ne_nil b l) he' with ⟨x, hx, hr⟩ | h
        · exact Or.inl ⟨x, List.mem_cons_of_mem a hx, hr⟩
        · exact Or.inr (by rw [List.getLast_cons_cons]; exact h)

/-- A chain containing a `p`-true entry and ending at a `p`-false entry has a step from a `p`-true
entry to a `p`-false entry. -/
theorem exists_transition_of_getLast {α : Type*} {R : α → α → Prop} {p : α → Bool} :
    ∀ {L : List α} (hne : L ≠ []), L.IsChain R → ∀ {a : α}, a ∈ L → p a = true →
      p (L.getLast hne) = false → ∃ e ∈ L, ∃ f ∈ L, p e = true ∧ p f = false ∧ R e f
  | [], hne, _, _, _, _, _ => (hne rfl).elim
  | [_], _, _, _, ha, hpa, hlast => by
      rw [List.getLast_singleton] at hlast
      rw [List.mem_singleton.mp ha, hlast] at hpa
      exact Bool.noConfusion hpa
  | b :: c :: l, _, hL, a, ha, hpa, hlast => by
      rw [List.isChain_cons_cons] at hL
      rw [List.getLast_cons_cons] at hlast
      cases hpb : p b with
      | true =>
          cases hpc : p c with
          | false =>
              exact ⟨b, List.mem_cons_self, c, List.mem_cons_of_mem b List.mem_cons_self, hpb,
                hpc, hL.1⟩
          | true =>
              obtain ⟨e, he, f, hf, h⟩ := exists_transition_of_getLast (List.cons_ne_nil c l)
                hL.2 List.mem_cons_self hpc hlast
              exact ⟨e, List.mem_cons_of_mem b he, f, List.mem_cons_of_mem b hf, h⟩
      | false =>
          have ha' : a ∈ c :: l := by
            rcases List.mem_cons.mp ha with h | h
            · rw [h, hpb] at hpa
              exact Bool.noConfusion hpa
            · exact h
          obtain ⟨e, he, f, hf, h⟩ :=
            exists_transition_of_getLast (List.cons_ne_nil c l) hL.2 ha' hpa hlast
          exact ⟨e, List.mem_cons_of_mem b he, f, List.mem_cons_of_mem b hf, h⟩

/-- A chain starting at a `p`-true entry and containing a `p`-false entry has a step from a
`p`-true entry to a `p`-false entry. -/
theorem exists_transition_of_head {α : Type*} {R : α → α → Prop} {p : α → Bool} :
    ∀ {L : List α} (hne : L ≠ []), L.IsChain R → p (L.head hne) = true → ∀ {b : α}, b ∈ L →
      p b = false → ∃ e ∈ L, ∃ f ∈ L, p e = true ∧ p f = false ∧ R e f
  | [], hne, _, _, _, _, _ => (hne rfl).elim
  | [_], _, _, hhead, _, hb, hpb => by
      rw [List.head_cons] at hhead
      rw [List.mem_singleton.mp hb, hhead] at hpb
      exact Bool.noConfusion hpb
  | a :: c :: l, _, hL, hhead, b, hb, hpb => by
      rw [List.isChain_cons_cons] at hL
      rw [List.head_cons] at hhead
      cases hpc : p c with
      | false =>
          exact ⟨a, List.mem_cons_self, c, List.mem_cons_of_mem a List.mem_cons_self, hhead, hpc,
            hL.1⟩
      | true =>
          have hb' : b ∈ c :: l := by
            rcases List.mem_cons.mp hb with h | h
            · rw [h, hhead] at hpb
              exact Bool.noConfusion hpb
            · exact h
          obtain ⟨e, he, f, hf, h⟩ := exists_transition_of_head (List.cons_ne_nil c l) hL.2
            (by rw [List.head_cons]; exact hpc) hb' hpb
          exact ⟨e, List.mem_cons_of_mem a he, f, List.mem_cons_of_mem a hf, h⟩

/-- **A transition on a closed walk.**  A cyclic chain with a `p`-true entry and a `p`-false entry
has a step from a `p`-true entry to a `p`-false entry. -/
theorem exists_transition {α : Type*} {R : α → α → Prop} {p : α → Bool} {c : List α}
    (hne : c ≠ []) (hchain : c.IsChain R) (hclose : R (c.getLast hne) (c.head hne))
    {a b : α} (ha : a ∈ c) (hpa : p a = true) (hb : b ∈ c) (hpb : p b = false) :
    ∃ e ∈ c, ∃ f ∈ c, p e = true ∧ p f = false ∧ R e f := by
  cases hh : p (c.head hne) with
  | true => exact exists_transition_of_head hne hchain hh hb hpb
  | false =>
      cases hl : p (c.getLast hne) with
      | false => exact exists_transition_of_getLast hne hchain ha hpa hl
      | true =>
          exact ⟨c.getLast hne, List.getLast_mem hne, c.head hne, List.head_mem hne, hl, hh,
            hclose⟩

/-! ## Counting repeated visits -/

/-- **Dropping entries with a shared value lowers the repeats.**  Let `c` be split, up to
permutation, into `A` and `B`, with some `x ∈ A` and `y ∈ B` of equal value.  A permutation `L`
of `A` has fewer entries less values than `c`. -/
theorem length_sub_card_lt {α : Type*} {β : Type*} {_ : DecidableEq β} (f : α → β)
    {c A B L : List α} (hc : (A ++ B).Perm c) (hL : L.Perm A) {x y : α} (hx : x ∈ A)
    (hy : y ∈ B) (hxy : f x = f y) :
    L.length - (L.map f).toFinset.card < c.length - (c.map f).toFinset.card := by
  have hLA : (L.map f).toFinset = (A.map f).toFinset :=
    List.toFinset_eq_of_perm _ _ (hL.map f)
  have hcAB : (c.map f).toFinset = (A.map f).toFinset ∪ (B.map f).toFinset := by
    rw [← List.toFinset_append, ← List.map_append]
    exact List.toFinset_eq_of_perm _ _ (hc.map f).symm
  have hlen : c.length = A.length + B.length := by
    rw [← hc.length_eq, List.length_append]
  have hLlen : L.length = A.length := hL.length_eq
  have hinter : 0 < ((A.map f).toFinset ∩ (B.map f).toFinset).card := by
    refine Finset.card_pos.mpr ⟨f x, Finset.mem_inter.mpr
      ⟨List.mem_toFinset.mpr (List.mem_map_of_mem hx), ?_⟩⟩
    rw [hxy]
    exact List.mem_toFinset.mpr (List.mem_map_of_mem hy)
  have hunion := Finset.card_union_add_card_inter (A.map f).toFinset (B.map f).toFinset
  have hA := List.toFinset_card_le (A.map f)
  have hB := List.toFinset_card_le (B.map f)
  rw [List.length_map] at hA hB
  rw [hLA, hcAB, hlen, hLlen]
  omega

/-! ## The rose step -/

/-- **The rose step from the sub-arc region move** (Osin Lemma 9.7(b), for `thm:hull`).  The moved
face set `flipFaces K.faces z`, with boundary cycle `s_1 t_1 s_2 t_2`, is a pocket in the same
diagram with strictly fewer repeated visits. -/
theorem rose_of_regionMoveSubArc (hsub : RoseRegionMoveSubArcStatement.{u, w, v}) :
    RoseStepStatement.{u, w, v} := by
  intro G _ Lambda D _ _ _ _ _ _ _ _ _
  refine ⟨0, fun eps _ => ⟨1, Nat.one_pos, fun _ _ _ _ X lo hi hLA hlabel K hK hFT hsrc htgt
    hpinch hcross => ?_⟩⟩
  obtain ⟨z, hz, hind, hout, ⟨y, hy, hpy⟩, source, kept, hsrcnot, hkeptin, t₁, t₂, s₁, s₂, hperm,
    hwalk, hs₁, hs₂, hlo, hhi, ht₁, ht₂⟩ :=
    hsub D eps X lo hi hLA hlabel K hK hFT hsrc htgt hpinch hcross
  obtain ⟨hne, hchain, hclose⟩ := hwalk
  obtain ⟨hKchain, hKclose⟩ := hK
  have hnodup : (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts).Nodup :=
    List.Nodup.perm (List.Nodup.sublist List.filter_sublist K.boundary.cycle_nodup) hperm.symm
  have hbd := isBoundaryDart_flipFaces_iff K.boundary.cycle_mem_iff hz hind
  have hmem : ∀ d, d ∈ s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts ↔
      Surgery.MapCollapse.IsBoundaryDart X.toCombMap (flipFaces X.toCombMap K.faces z) d :=
    fun d => (hperm.mem_iff.trans List.mem_filter).trans (hbd d).symm
  refine ⟨X,
    { faces := flipFaces X.toCombMap K.faces z
      outerFace_not_mem := hout
      source := source
      source_not_mem := hsrcnot
      kept := kept
      kept_mem := hkeptin
      sourceArc := t₁
      targetArc := t₂
      firstSide := s₁
      secondSide := s₂
      boundary := ⟨s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts, hne, hnodup, hmem⟩
      decomposition := rfl
      firstSide_length_le := hs₁
      secondSide_length_le := hs₂
      firstSide_norm_le := (PocketFaceSet.wordNorm_dartWord_le_length hlabel s₁).trans hs₁
      secondSide_norm_le := (PocketFaceSet.wordNorm_dartWord_le_length hlabel s₂).trans hs₂
      lo_le := hlo
      le_hi := hhi },
    ⟨OEquivalentDiscDiagram.refl X⟩, hlabel, ⟨hchain, hclose⟩, ht₁, ht₂, ?_⟩
  obtain ⟨ha, hpa⟩ := List.mem_filter.mp (hperm.mem_iff.mp (List.head_mem hne))
  obtain ⟨e, he, f, hf, hpe, hpf, hef⟩ :=
    exists_transition (p := GL05b.movePred X.toCombMap z) K.boundary.cycle_nonempty
      hKchain hKclose ha hpa hy hpy
  have hef' : X.toCombMap.vertexOf (X.toCombMap.alpha e) = X.toCombMap.vertexOf f := hef
  have heL : e ∈ s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts :=
    hperm.mem_iff.mpr (List.mem_filter.mpr ⟨he, hpe⟩)
  have hsucc : ∃ x ∈ s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts,
      X.toCombMap.vertexOf (X.toCombMap.alpha e) = X.toCombMap.vertexOf x := by
    rcases exists_succ_or_eq_getLast hchain hne heL with h | h
    · exact h
    · exact ⟨_, List.head_mem hne, by rw [h]; exact hclose⟩
  obtain ⟨x, hxL, hex⟩ := hsucc
  have hxA : x ∈ K.boundary.cycle.filter (GL05b.movePred X.toCombMap z) := hperm.mem_iff.mp hxL
  have hfB : f ∈ K.boundary.cycle.filter (fun d => !GL05b.movePred X.toCombMap z d) :=
    List.mem_filter.mpr ⟨hf, by simp only [hpf, Bool.not_false]⟩
  unfold PocketFaceSet.repeatedVisits
  exact length_sub_card_lt X.toCombMap.vertexOf (List.filter_append_perm _ _) hperm hxA hfB
    (hex.symm.trans hef')

end GroupApproximation.Full.GL06f

#audit_axioms GroupApproximation.Full.GL06f.eq_of_eqvGen_of_step
#audit_axioms GroupApproximation.Full.GL06f.mem_flipFaces_iff
#audit_axioms GroupApproximation.Full.GL06f.isBoundaryDart_flipFaces_iff
#audit_axioms GroupApproximation.Full.GL06f.exists_succ_or_eq_getLast
#audit_axioms GroupApproximation.Full.GL06f.exists_transition_of_getLast
#audit_axioms GroupApproximation.Full.GL06f.exists_transition_of_head
#audit_axioms GroupApproximation.Full.GL06f.exists_transition
#audit_axioms GroupApproximation.Full.GL06f.length_sub_card_lt
#audit_axioms GroupApproximation.Full.GL06f.rose_of_regionMoveSubArc
