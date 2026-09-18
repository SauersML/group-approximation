import Mathlib.Data.List.Infix
import GroupApproximation.Meta.AxiomGuard

/-!
# Placement of a contiguous removed block: list lemmas

Lane gl-p10-56.  Pure list facts behind `PlaceBlock`: if a Boolean predicate `P` is constant on
each of the three pieces of `L = A ++ B ++ C`, with the same value on `A` and `C`, then for every
infix `I` of `L` the filtered list `I.filter P` is again an infix of `I`, unless `P` removes the
middle piece `B` and `B` lies strictly inside `I` (`roseLobePlace_filter_infix`).  The escape
hypothesis asks for one dart of `B` outside `I`, which rules out exactly this "bubble" case.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

section Lists

variable {α : Type*}

/-- An equality gives an infix. -/
theorem roseLobePlace_infix_of_eq {l m : List α} (h : l = m) : l <:+: m := by
  subst h
  exact List.infix_refl l

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobePlace_infix_of_eq

/-- Rewrite the left side of an infix. -/
theorem roseLobePlace_infix_congr {l l' m : List α} (h : l = l') (h' : l' <:+: m) :
    l <:+: m := by
  subst h
  exact h'

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobePlace_infix_congr

/-- A predicate false on a list filters it to `[]`. -/
theorem roseLobePlace_filter_nil {P : α → Bool} {U : List α} (h : ∀ a ∈ U, P a = false) :
    U.filter P = [] :=
  List.filter_eq_nil_iff.mpr fun a ha => by simp [h a ha]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobePlace_filter_nil

/-- A predicate true on a list keeps it. -/
theorem roseLobePlace_filter_self {P : α → Bool} {U : List α} (h : ∀ a ∈ U, P a = true) :
    U.filter P = U :=
  List.filter_eq_self.mpr h

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobePlace_filter_self

/-- **One constant piece**: the filter is `[]` or everything. -/
theorem roseLobePlace_filter_one {P : α → Bool} {U : List α} {v : Bool}
    (hU : ∀ a ∈ U, P a = v) : U.filter P <:+: U := by
  cases v
  · exact roseLobePlace_infix_congr (roseLobePlace_filter_nil hU) List.nil_infix
  · exact roseLobePlace_infix_congr (roseLobePlace_filter_self hU) (List.infix_refl U)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobePlace_filter_one

/-- **Two constant pieces**: the filter of `U ++ V` is `[]`, `U`, `V` or everything. -/
theorem roseLobePlace_filter_two {P : α → Bool} {U V : List α} {v w : Bool}
    (hU : ∀ a ∈ U, P a = v) (hV : ∀ a ∈ V, P a = w) : (U ++ V).filter P <:+: U ++ V := by
  cases v <;> cases w
  · have e : (U ++ V).filter P = [] := by
      simp only [List.filter_append, roseLobePlace_filter_nil hU, roseLobePlace_filter_nil hV,
        List.append_nil]
    exact roseLobePlace_infix_congr e List.nil_infix
  · have e : (U ++ V).filter P = V := by
      simp only [List.filter_append, roseLobePlace_filter_nil hU, roseLobePlace_filter_self hV,
        List.nil_append]
    exact roseLobePlace_infix_congr e (List.suffix_append U V).isInfix
  · have e : (U ++ V).filter P = U := by
      simp only [List.filter_append, roseLobePlace_filter_self hU, roseLobePlace_filter_nil hV,
        List.append_nil]
    exact roseLobePlace_infix_congr e (List.prefix_append U V).isInfix
  · have e : (U ++ V).filter P = U ++ V := by
      simp only [List.filter_append, roseLobePlace_filter_self hU, roseLobePlace_filter_self hV]
    exact roseLobePlace_infix_of_eq e

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobePlace_filter_two

/-- **Three constant pieces, equal outer values**: the filter of `U ++ V ++ Z` is an infix,
unless `P` keeps the outer pieces and removes a nonempty middle piece. -/
theorem roseLobePlace_filter_three {P : α → Bool} {U V Z : List α} {v w : Bool}
    (hU : ∀ a ∈ U, P a = v) (hV : ∀ a ∈ V, P a = w) (hZ : ∀ a ∈ Z, P a = v)
    (hesc : v = true → w = false → V = []) :
    (U ++ V ++ Z).filter P <:+: U ++ V ++ Z := by
  cases v <;> cases w
  · have e : (U ++ V ++ Z).filter P = [] := by
      simp only [List.filter_append, roseLobePlace_filter_nil hU, roseLobePlace_filter_nil hV,
        roseLobePlace_filter_nil hZ, List.append_nil]
    exact roseLobePlace_infix_congr e List.nil_infix
  · have e : (U ++ V ++ Z).filter P = V := by
      simp only [List.filter_append, roseLobePlace_filter_nil hU, roseLobePlace_filter_self hV,
        roseLobePlace_filter_nil hZ, List.nil_append, List.append_nil]
    exact roseLobePlace_infix_congr e (List.infix_append U V Z)
  · obtain rfl := hesc rfl rfl
    have e : (U ++ [] ++ Z).filter P = U ++ [] ++ Z := by
      simp only [List.filter_append, roseLobePlace_filter_self hU, List.filter_nil,
        roseLobePlace_filter_self hZ]
    exact roseLobePlace_infix_of_eq e
  · have e : (U ++ V ++ Z).filter P = U ++ V ++ Z := by
      simp only [List.filter_append, roseLobePlace_filter_self hU, roseLobePlace_filter_self hV,
        roseLobePlace_filter_self hZ]
    exact roseLobePlace_infix_of_eq e

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobePlace_filter_three

/-- **The filter of an infix of three constant pieces.**  If `S ++ I ++ T = A ++ B ++ C` and `P`
is constant `v` on `A` and `C` and constant `w` on `B`, then `I.filter P` is an infix of `I`,
provided some dart of `B` lies outside `I` whenever `P` keeps `A`, `C` and removes `B`. -/
theorem roseLobePlace_filter_infix {P : α → Bool} {S I T A B C : List α}
    (h : S ++ I ++ T = A ++ B ++ C) {v w : Bool} (hA : ∀ a ∈ A, P a = v)
    (hB : ∀ a ∈ B, P a = w) (hC : ∀ a ∈ C, P a = v)
    (hesc : v = true → w = false → ∃ d ∈ B, d ∉ I) :
    I.filter P <:+: I := by
  rcases List.append_eq_append_iff.mp h with ⟨as, h1, -⟩ | ⟨bs, h1, h2⟩
  · rcases List.append_eq_append_iff.mp h1 with ⟨e, h3, h4⟩ | ⟨e, h3, -⟩
    · rcases List.append_eq_append_iff.mp h3 with ⟨f, h5, h6⟩ | ⟨f, -, h6⟩
      · rw [h6]
        refine roseLobePlace_filter_two (fun a ha => hA a ?_) (fun a ha => hB a ?_)
        · rw [h5]
          exact List.mem_append_right S ha
        · rw [h4]
          exact List.mem_append_left as ha
      · refine roseLobePlace_filter_one (fun a ha => hB a ?_)
        rw [h4, h6]
        exact List.mem_append_left as (List.mem_append_right f ha)
    · refine roseLobePlace_filter_one (fun a ha => hA a ?_)
      rw [h3]
      exact List.mem_append_left e (List.mem_append_right S ha)
  · rcases List.append_eq_append_iff.mp h1 with ⟨e, h3, h4⟩ | ⟨e, -, h4⟩
    · rcases List.append_eq_append_iff.mp h3 with ⟨f, -, h6⟩ | ⟨f, h5, h6⟩
      · rw [h4]
        refine roseLobePlace_filter_two (fun a ha => hB a ?_) (fun a ha => hC a ?_)
        · rw [h6]
          exact List.mem_append_right f ha
        · rw [h2]
          exact List.mem_append_left T ha
      · have hesc' : v = true → w = false → B = [] := by
          intro hv hw
          obtain ⟨d, hd, hdI⟩ := hesc hv hw
          refine absurd ?_ hdI
          rw [h4, h6]
          exact List.mem_append_left bs (List.mem_append_right f hd)
        rw [h4, h6]
        refine roseLobePlace_filter_three (fun a ha => hA a ?_) hB (fun a ha => hC a ?_) hesc'
        · rw [h5]
          exact List.mem_append_right S ha
        · rw [h2]
          exact List.mem_append_left T ha
    · refine roseLobePlace_filter_one (fun a ha => hC a ?_)
      rw [h2, h4]
      exact List.mem_append_left T (List.mem_append_right e ha)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobePlace_filter_infix

/-- **The block form.**  If the cycle `S ++ I ++ T` is `A ++ B ++ C`, where `P` removes all of
`B` and keeps all of `A ++ C`, or keeps all of `B` and removes all of `A ++ C`, and some dart of
`B` lies outside `I`, then `I.filter P` is an infix of `I`. -/
theorem roseLobePlace_filter_block {P : α → Bool} {S I T A B C : List α}
    (h : S ++ I ++ T = A ++ B ++ C)
    (hblk : (B.filter P = [] ∧ (A ++ C).filter P = A ++ C ∧ A ++ C ≠ []) ∨
      (B.filter P = B ∧ (A ++ C).filter P = [] ∧ B ≠ []))
    (hesc : ∃ d ∈ B, d ∉ I) : I.filter P <:+: I := by
  rcases hblk with ⟨hB, hAC, -⟩ | ⟨hB, hAC, -⟩
  · exact roseLobePlace_filter_infix h (v := true) (w := false)
      (fun a ha => List.filter_eq_self.mp hAC a (List.mem_append_left C ha))
      (fun a ha => Bool.eq_false_iff.mpr (List.filter_eq_nil_iff.mp hB a ha))
      (fun a ha => List.filter_eq_self.mp hAC a (List.mem_append_right A ha))
      (fun _ _ => hesc)
  · exact roseLobePlace_filter_infix h (v := false) (w := true)
      (fun a ha => Bool.eq_false_iff.mpr
        (List.filter_eq_nil_iff.mp hAC a (List.mem_append_left C ha)))
      (fun a ha => List.filter_eq_self.mp hB a ha)
      (fun a ha => Bool.eq_false_iff.mpr
        (List.filter_eq_nil_iff.mp hAC a (List.mem_append_right A ha)))
      (fun hv _ => absurd hv (by decide))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobePlace_filter_block

/-- **An infix is a prefix of a drop.** -/
theorem roseLobePlace_prefix_drop {f t : List α} (h : f <:+: t) :
    ∃ k, k ≤ t.length ∧ f <+: t.drop k := by
  obtain ⟨s, u, rfl⟩ := h
  refine ⟨s.length, ?_, u, ?_⟩
  · rw [List.length_append, List.length_append]
    omega
  · rw [List.append_assoc, List.drop_left]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobePlace_prefix_drop

end Lists

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
