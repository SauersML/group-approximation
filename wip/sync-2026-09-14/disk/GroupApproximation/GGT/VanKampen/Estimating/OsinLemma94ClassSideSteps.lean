import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassCornerMove
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassGapSpanModel
import GroupApproximation.Meta.AxiomGuard

/-!
# Class words: side letters, gap steps and the split point

Osin (math/0411039v3, §9), proof of Lemma 9.4, Case 1, on class words (route B1 of GapSpan).  A class word reads its
side words with the gap words between them.  The positions strictly inside no gap are the allowed positions.  Between
two consecutive allowed positions there is either one letter of a side word or a whole gap, which moves no vertex.

* `UnboundEstimate.exists_sideStep_lt`: the split point over allowed positions.  An antitone function that
  decreases from `a` to `a'`, and does not change across the steps that are no side letters, decreases strictly across
  some side letter.
* `UnboundEstimate.exists_split_of_lt_flatMap`, `OsinLemma94ClassPolygons.exists_block`: every letter lies in the block
  (side word and gap) of some side.
* `not_inGap_succ_of_side`, `step_side_or_gap`: the step between consecutive allowed positions.
* `not_side_of_gapStart`: a side letter does not start a nonempty gap.
* `exists_allowed_near`: every position between two allowed positions is within `⌈(c + 2) / λ⌉₊` of an allowed one
  between them.
* `exists_right_normal`, `exists_left_normal`: an endpoint moves along a gap to an allowed position with the same vertex,
  so that the step into it (out of it) is a side letter.

Model test: a class of one side has no gaps (`ofSides`), all positions are allowed, every step is a side letter, and
`exists_sideStep_lt` is `exists_step_lt_of_lt`.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, through Osin's Lemma 9.4 inside the proof of Lemma 4.4); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open GroupApproximation.WordMetric

/-- **The split point over allowed positions.**  If `f` is antitone up to `a'`, decreases strictly from `a` to `a'`,
and across every step between consecutive allowed positions either the step is one side letter or `f` does not change,
then `f` decreases strictly across some side letter between allowed positions. -/
theorem UnboundEstimate.exists_sideStep_lt (allow side : ℕ → Prop) (f : ℕ → ℕ) {a' : ℕ}
    (ha' : allow a') :
    ∀ (n a : ℕ), a' - a = n → a < a' → allow a → f a' < f a →
      (∀ g g', a ≤ g → g ≤ g' → g' ≤ a' → f g' ≤ f g) →
      (∀ g g', a ≤ g → g < g' → g' ≤ a' → allow g → allow g' →
        (∀ x, g < x → x < g' → ¬ allow x) → (g' = g + 1 ∧ side g) ∨ f g' = f g) →
      ∃ g, a ≤ g ∧ g + 1 ≤ a' ∧ allow g ∧ allow (g + 1) ∧ side g ∧ f (g + 1) < f g := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a hn haa' ha hlt hanti hstep
  have hex : ∃ x, a < x ∧ x ≤ a' ∧ allow x := ⟨a', haa', le_rfl, ha'⟩
  obtain ⟨hg1, hg2, hg3⟩ := Nat.find_spec hex
  have hbetween : ∀ x, a < x → x < Nat.find hex → ¬ allow x := fun x hx1 hx2 hx =>
    Nat.find_min hex hx2 ⟨hx1, by omega, hx⟩
  have hcase : (Nat.find hex = a + 1 ∧ side a ∧ f (Nat.find hex) < f a) ∨
      f (Nat.find hex) = f a := by
    rcases hstep a (Nat.find hex) le_rfl hg1 hg2 ha hg3 hbetween with ⟨hsucc, hside⟩ | heq
    · by_cases hdec : f (Nat.find hex) < f a
      · exact Or.inl ⟨hsucc, hside, hdec⟩
      · exact Or.inr (le_antisymm (hanti a _ le_rfl (by omega) hg2) (not_lt.mp hdec))
    · exact Or.inr heq
  rcases hcase with ⟨hsucc, hside, hdec⟩ | heq
  · refine ⟨a, le_rfl, by omega, ha, ?_, hside, ?_⟩
    · rw [← hsucc]
      exact hg3
    · rw [← hsucc]
      exact hdec
  · have hga' : Nat.find hex < a' := by
      rcases Nat.lt_or_ge (Nat.find hex) a' with h | h
      · exact h
      · have he : Nat.find hex = a' := le_antisymm hg2 h
        rw [he] at heq
        omega
    obtain ⟨g, hg, rest⟩ := ih (a' - Nat.find hex) (by omega) (Nat.find hex) rfl hga' hg3
      (by rw [heq]; exact hlt) (fun x y hx => hanti x y (by omega))
      (fun x y hx => hstep x y (by omega))
    exact ⟨g, by omega, rest⟩

/-- A position below the length of a `flatMap` lies in the block of some entry. -/
theorem UnboundEstimate.exists_split_of_lt_flatMap {β : Type*} (blk : ℕ → List β) :
    ∀ (L : List ℕ) {x : ℕ}, x < (L.flatMap blk).length →
      ∃ L1 s L2, L = L1 ++ s :: L2 ∧ (L1.flatMap blk).length ≤ x ∧
        x < (L1.flatMap blk).length + (blk s).length
  | [], x, hx => by simp at hx
  | s :: L, x, hx => by
    by_cases hs : x < (blk s).length
    · exact ⟨[], s, L, rfl, by simp, by simpa using hs⟩
    · have hx' : x - (blk s).length < (L.flatMap blk).length := by
        simp only [List.flatMap_cons, List.length_append] at hx
        omega
      obtain ⟨L1, t, L2, hL, h1, h2⟩ := UnboundEstimate.exists_split_of_lt_flatMap blk L hx'
      refine ⟨s :: L1, t, L2, by rw [hL]; rfl, ?_, ?_⟩
      · simp only [List.flatMap_cons, List.length_append]
        omega
      · simp only [List.flatMap_cons, List.length_append]
        omega

namespace OsinLemma94ClassPolygons

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

/-- **Every letter lies in the block of some side**: its side word and its gap. -/
theorem exists_block (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (i : ℕ) {x : ℕ}
    (hx : x < (Q.word k i).length) :
    ∃ s off, Q.SideAt k i s off ∧ off ≤ x ∧
      x < off + (P.word k s).length + (dartWord S.diagram (Q.gap k s)).length := by
  rw [Q.word_eq] at hx
  obtain ⟨L1, s, L2, hL, h1, h2⟩ := UnboundEstimate.exists_split_of_lt_flatMap
    (fun t => P.word k t ++ Embedded.dartWord S.diagram (Q.gap k t)) (Q.classSides k i) hx
  refine ⟨s, _, ⟨L1, L2, hL, rfl⟩, h1, ?_⟩
  simp only [List.length_append] at h2
  omega

/-- The word of a side of a class is not empty. -/
theorem one_le_length_word_of_sideAt (Q : OsinLemma94ClassPolygons P) {k : Fin P.count} {i s off : ℕ}
    (hi : i < Q.classCount k) (hs : Q.SideAt k i s off) : 1 ≤ (P.word k s).length := by
  have hlt := Q.lt_sideCount_of_mem k i hi s (Q.mem_of_sideAt hs)
  have hne := P.side_ne_nil k s hlt
  rw [OsinLemma94RealizedPolygons.word, dartWord_length]
  exact List.length_pos_of_ne_nil hne

/-- **A side letter keeps the next position out of the gaps.** -/
theorem not_inGap_succ_of_side (Q : OsinLemma94ClassPolygons P) {k : Fin P.count} {i s off x : ℕ}
    (hs : Q.SideAt k i s off) (h1 : off ≤ x) (h2 : x < off + (P.word k s).length) :
    ¬ Q.InGap k i (x + 1) := by
  rintro ⟨t, off', ht, h3, h4⟩
  rcases hs.eq_or_block_le ht with ⟨rfl, rfl⟩ | hle | hle <;> omega

/-- **A side letter does not start a nonempty gap.** -/
theorem not_side_of_gapStart (Q : OsinLemma94ClassPolygons P) {k : Fin P.count} {i s t off off' g : ℕ}
    (hs : Q.SideAt k i s off) (hg : g = off + (P.word k s).length)
    (hγ : 0 < (dartWord S.diagram (Q.gap k s)).length)
    (ht : Q.SideAt k i t off') (h1 : off' ≤ g) (h2 : g + 1 ≤ off' + (P.word k t).length) : False := by
  rcases hs.eq_or_block_le ht with ⟨rfl, rfl⟩ | hle | hle <;> omega

/-- **The step between consecutive allowed positions** is one side letter, or a whole gap with one vertex at its two
corners. -/
theorem step_side_or_gap (Q : OsinLemma94ClassPolygons P) {k : Fin P.count} {i g g' : ℕ}
    (hi : i < Q.classCount k) (hg'len : g' ≤ (Q.word k i).length) (hgg' : g < g')
    (hg : ¬ Q.InGap k i g) (hg' : ¬ Q.InGap k i g') (hbetween : ∀ x, g < x → x < g' → Q.InGap k i x) :
    (g' = g + 1 ∧ ∃ s off, Q.SideAt k i s off ∧ off ≤ g ∧ g + 1 ≤ off + (P.word k s).length) ∨
      (∃ s off, Q.SideAt k i s off ∧ g = off + (P.word k s).length ∧
        g' = off + (P.word k s).length + (dartWord S.diagram (Q.gap k s)).length ∧
        OsinComponents.vertex (Q.corner k i) (Q.word k i) g =
          OsinComponents.vertex (Q.corner k i) (Q.word k i) g') := by
  obtain ⟨s, off, hs, h1, h2⟩ := Q.exists_block k i (show g < (Q.word k i).length by omega)
  by_cases hside : g < off + (P.word k s).length
  · refine Or.inl ⟨?_, s, off, hs, h1, by omega⟩
    by_contra hne
    exact Q.not_inGap_succ_of_side hs h1 hside (hbetween (g + 1) (by omega) (by omega))
  · have hgs : g = off + (P.word k s).length := by
      by_contra hne
      exact hg ⟨s, off, hs, by omega, h2⟩
    have hle : g' ≤ off + (P.word k s).length + (dartWord S.diagram (Q.gap k s)).length := by
      by_contra hgt
      exact not_inGap_corner hs (Or.inr rfl) (hbetween _ (by omega) (by omega))
    have hge : off + (P.word k s).length + (dartWord S.diagram (Q.gap k s)).length ≤ g' := by
      by_contra hlt
      exact hg' ⟨s, off, hs, by omega, by omega⟩
    have hg'e : g' = off + (P.word k s).length + (dartWord S.diagram (Q.gap k s)).length :=
      le_antisymm hle hge
    refine Or.inr ⟨s, off, hs, hgs, hg'e, ?_⟩
    rw [hgs, hg'e]
    exact (Q.vertex_gap_end_eq hi hs).symm

/-- **Allowed positions nearby.**  Between two allowed positions `b' ≤ b`, every position is within
`⌈(c + 2) / λ⌉₊` of an allowed position between them: a gap position moves to the start of its gap. -/
theorem exists_allowed_near (Q : OsinLemma94ClassPolygons P) (hlambda : 0 < lambda) {k : Fin P.count}
    {i b' b p : ℕ} (hi : i < Q.classCount k) (hmem : i ∈ Q.relatorClasses k ∨ i ∈ Q.longClasses k)
    (hadm : HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) (Q.word k i))
    (hb'n : ¬ Q.InGap k i b') (hblen : b ≤ (Q.word k i).length) (hp1 : b' ≤ p) (hp2 : p ≤ b) :
    ∃ p', b' ≤ p' ∧ p' ≤ b ∧ ¬ Q.InGap k i p' ∧
      wordDist (symmetricLabelAlphabet D).alphabet.carrier
        (OsinComponents.vertex (Q.corner k i) (Q.word k i) p)
        (OsinComponents.vertex (Q.corner k i) (Q.word k i) p') ≤ ⌈(c + 2) / lambda⌉₊ := by
  by_cases hin : Q.InGap k i p
  · obtain ⟨s, off, hs, h1, h2⟩ := hin
    have hgap := Q.gap_length_le hlambda hi hmem hs
    have hb'le : b' ≤ off + (P.word k s).length := by
      by_contra hgt
      exact hb'n ⟨s, off, hs, by omega, by omega⟩
    refine ⟨off + (P.word k s).length, hb'le, by omega, not_inGap_corner hs (Or.inl rfl), ?_⟩
    exact wordDist_vertex_le_of_near hadm _ (by omega) (by omega) (by omega) (by omega)
  · refine ⟨p, hp1, hp2, hin, ?_⟩
    exact le_trans (wordDist_vertex_le_of_near hadm _ (by omega) (by omega) (by omega) (by omega))
      (Nat.zero_le _)

/-- **The right endpoint off a trailing gap.**  An allowed endpoint `a'` above an allowed `a` moves back along a gap
to an allowed `a''` with the same vertex, so that the step into `a''` from the allowed position before it is one side
letter. -/
theorem exists_right_normal (Q : OsinLemma94ClassPolygons P) {k : Fin P.count} {i a a' : ℕ}
    (hi : i < Q.classCount k) (ha'len : a' ≤ (Q.word k i).length) (haa' : a < a')
    (ha : ¬ Q.InGap k i a) (ha' : ¬ Q.InGap k i a') :
    ∃ a'', a ≤ a'' ∧ a'' ≤ a' ∧ ¬ Q.InGap k i a'' ∧
      OsinComponents.vertex (Q.corner k i) (Q.word k i) a'' =
        OsinComponents.vertex (Q.corner k i) (Q.word k i) a' ∧
      (a'' = a' ∨ ∃ s off, Q.SideAt k i s off ∧ a'' = off + (P.word k s).length ∧
        a' = off + (P.word k s).length + (dartWord S.diagram (Q.gap k s)).length ∧ a'' < a') ∧
      ∀ g, a ≤ g → g < a'' → ¬ Q.InGap k i g → (∀ x, g < x → x < a'' → Q.InGap k i x) →
        a'' = g + 1 ∧ ∃ s off, Q.SideAt k i s off ∧ off ≤ g ∧ g + 1 ≤ off + (P.word k s).length := by
  classical
  have hspec : a ≤ a ∧ ¬ Q.InGap k i a := ⟨le_rfl, ha⟩
  have hg0 := Nat.findGreatest_spec (P := fun x => a ≤ x ∧ ¬ Q.InGap k i x) (show a ≤ a' - 1 by omega)
    hspec
  have hg0le := Nat.findGreatest_le (P := fun x => a ≤ x ∧ ¬ Q.InGap k i x) (a' - 1)
  set g0 := Nat.findGreatest (fun x => a ≤ x ∧ ¬ Q.InGap k i x) (a' - 1) with hg0def
  have hbetween : ∀ x, g0 < x → x < a' → Q.InGap k i x := by
    intro x hx1 hx2
    by_contra hx
    exact Nat.findGreatest_is_greatest hx1 (show x ≤ a' - 1 by omega) ⟨by omega, hx⟩
  rcases Q.step_side_or_gap hi ha'len (show g0 < a' by omega) hg0.2 ha' hbetween with
    ⟨hsucc, hsidew⟩ | ⟨s, off, hs, hg0s, ha's, hveq⟩
  · refine ⟨a', haa'.le, le_rfl, ha', rfl, Or.inl rfl, fun g hg hga'' hgn hbet => ?_⟩
    have hgg0 : g = g0 := by
      rcases Nat.lt_trichotomy g g0 with h | h | h
      · exact absurd (hbet g0 h (by omega)) hg0.2
      · exact h
      · exact absurd (hbetween g h hga'') hgn
    rw [hgg0]
    exact ⟨hsucc, hsidew⟩
  · refine ⟨g0, hg0.1, by omega, hg0.2, hveq, Or.inr ⟨s, off, hs, hg0s, ha's, by omega⟩,
      fun g hg hgg0 hgn hbet => ?_⟩
    rcases Q.step_side_or_gap hi (show g0 ≤ (Q.word k i).length by omega) hgg0 hgn hg0.2 hbet with
      hside | ⟨t, off', ht, hgt, hg0t, -⟩
    · exact hside
    · have hsl := Q.one_le_length_word_of_sideAt hi hs
      rcases hs.eq_or_block_le ht with ⟨rfl, rfl⟩ | hle | hle <;> omega

/-- **The left endpoint off a leading gap.**  An allowed endpoint `b'` below an allowed `b` moves forward along a gap
to an allowed `b''` with the same vertex, so that the step out of `b''` to the next allowed position is one side
letter. -/
theorem exists_left_normal (Q : OsinLemma94ClassPolygons P) {k : Fin P.count} {i b' b : ℕ}
    (hi : i < Q.classCount k) (hblen : b ≤ (Q.word k i).length) (hbb' : b' < b)
    (hb' : ¬ Q.InGap k i b') (hb : ¬ Q.InGap k i b) :
    ∃ b'', b' ≤ b'' ∧ b'' ≤ b ∧ ¬ Q.InGap k i b'' ∧
      OsinComponents.vertex (Q.corner k i) (Q.word k i) b'' =
        OsinComponents.vertex (Q.corner k i) (Q.word k i) b' ∧
      ∀ g', b'' < g' → g' ≤ b → ¬ Q.InGap k i g' → (∀ x, b'' < x → x < g' → Q.InGap k i x) →
        g' = b'' + 1 ∧ ∃ s off, Q.SideAt k i s off ∧ off ≤ b'' ∧ b'' + 1 ≤ off + (P.word k s).length := by
  classical
  have hex : ∃ x, b' < x ∧ x ≤ b ∧ ¬ Q.InGap k i x := ⟨b, hbb', le_rfl, hb⟩
  obtain ⟨hg1, hg2, hg3⟩ := Nat.find_spec hex
  have hbetween : ∀ x, b' < x → x < Nat.find hex → Q.InGap k i x := by
    intro x hx1 hx2
    by_contra hx
    exact Nat.find_min hex hx2 ⟨hx1, by omega, hx⟩
  rcases Q.step_side_or_gap hi (show Nat.find hex ≤ (Q.word k i).length by omega) hg1 hb' hg3
      hbetween with ⟨hsucc, hsidew⟩ | ⟨s, off, hs, hb's, hg1s, hveq⟩
  · refine ⟨b', le_rfl, hbb'.le, hb', rfl, fun g' hg' hg'b hg'n hbet => ?_⟩
    have hgg1 : g' = Nat.find hex := by
      rcases Nat.lt_trichotomy g' (Nat.find hex) with h | h | h
      · exact absurd (hbetween g' hg' h) hg'n
      · exact h
      · exact absurd (hbet _ hg1 h) hg3
    rw [hgg1]
    exact ⟨hsucc, hsidew⟩
  · refine ⟨Nat.find hex, hg1.le, hg2, hg3, hveq.symm, fun g' hg' hg'b hg'n hbet => ?_⟩
    rcases Q.step_side_or_gap hi (show g' ≤ (Q.word k i).length by omega) hg' hg3 hg'n hbet with
      hside | ⟨t, off', ht, hg1t, -, -⟩
    · exact hside
    · have htl := Q.one_le_length_word_of_sideAt hi ht
      rcases hs.eq_or_block_le ht with ⟨rfl, rfl⟩ | hle | hle <;> omega

end OsinLemma94ClassPolygons

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.exists_sideStep_lt
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.step_side_or_gap
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.exists_allowed_near
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.exists_right_normal
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.exists_left_normal
