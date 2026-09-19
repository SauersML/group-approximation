import GroupApproximation.GGT.RelHypOsin24PowerUnbounded

/-!
# Finite labelled word patterns in Osin's bounded-power argument

Osin's Lemma 4.2-type argument starts with relative geodesic words for a
bounded family of powers.  The finite relative base and the finite peripheral
index imply that, after forgetting the values of peripheral letters but
retaining their labels, only finitely many word patterns occur at a fixed
length.  The source then uses its component and centralizer estimates to turn
one repeated pattern into a fixed slice `K h H_λ`; that geometric conversion is
the separate `RelativeBoundedPowerExtractionStatement` in
`RelHypOsin24BoundedPenetration`.

This file proves the finite pattern step itself.  It uses no unproved relative
geodesic or centralizer theorem.  The source correspondence is the finite
relative-word pigeonhole preceding Memoirs Lemmas `cyc1`, `qc1`, and `qc-hyp`
in the proof of Theorem 1.10.  The final component estimate remains named at
the smaller extraction frontier.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

universe u v

/-! ## Patterns and a generic finite-list lemma -/

/-- A relative word pattern retains a base-letter value and a peripheral label,
while forgetting the value of a peripheral letter. -/
abbrev RelativeWordPattern (G : Type u) (I : Type v) := List (Sum G I)

/-- The pattern of one labelled relative letter. -/
def relativeLetterPattern {G : Type u} {I : Type v} :
    RelLetter G I → Sum G I
  | RelLetter.base x => Sum.inl x
  | RelLetter.comp i _ => Sum.inr i

/-- The pattern obtained by reading a relative word. -/
def relativeWordPattern {G : Type u} {I : Type v}
    (w : List (RelLetter G I)) : RelativeWordPattern G I :=
  w.map relativeLetterPattern

/-- The finite support of patterns allowed by a relative generating set. -/
def relativePatternSupport {G : Type u} {I : Type v} [Group G]
    (D : RelGenSet G I) : Set (Sum G I) :=
  Sum.inl '' D.base ∪ Set.range (Sum.inr : I → Sum G I)

theorem relativeLetterPattern_mem_support {G : Type u} {I : Type v} [Group G]
    (D : RelGenSet G I) {a : RelLetter G I}
    (ha : D.IsLetter a) : relativeLetterPattern a ∈ relativePatternSupport D := by
  cases a with
  | base x =>
      exact Set.mem_union_left _ ⟨x, ha, rfl⟩
  | comp i h =>
      exact Set.mem_union_right _ ⟨i, rfl⟩

/-- Lists of bounded length whose entries lie in a finite set form a finite
set.  This elementary induction is the list-level finiteness used below; it
does not require the ambient type itself to be finite. -/
theorem finite_lists_of_finite_support {α : Type u} {F : Set α}
    (hF : F.Finite) (N : ℕ) :
    {p : List α | p.length ≤ N ∧ ∀ x ∈ p, x ∈ F}.Finite := by
  induction N with
  | zero =>
      refine Set.Finite.subset (Set.finite_singleton ([] : List α)) ?_
      intro p hp
      have hp0 : p.length = 0 := Nat.eq_zero_of_le_zero hp.1
      have hnil : p = [] := List.length_eq_zero_iff.mp hp0
      exact Set.mem_singleton_iff.mpr hnil
  | succ N ih =>
      have hcons :
          (Set.image2 (fun (x : α) (p : List α) => x :: p) F
            {p : List α | p.length ≤ N ∧ ∀ y ∈ p, y ∈ F}).Finite :=
        Set.Finite.image2 (fun (x : α) (p : List α) => x :: p) hF ih
      have hunion := (Set.finite_singleton ([] : List α)).union hcons
      refine Set.Finite.subset hunion ?_
      intro p hp
      cases p with
      | nil => exact Set.mem_union_left _ (Set.mem_singleton _)
      | cons x p =>
          have hx : x ∈ F := hp.2 x (by simp)
          have hpN : p.length ≤ N := by
            have hlen : p.length + 1 ≤ N + 1 := by
              simpa using hp.1
            omega
          have hpF : ∀ y ∈ p, y ∈ F := by
            intro y hy
            exact hp.2 y (List.mem_cons_of_mem x hy)
          exact Set.mem_union_right _ ⟨x, hx, p, ⟨hpN, hpF⟩, rfl⟩

/-! ## The finite pattern statement -/

/-- **Finite labelled relative-word patterns.**  At a fixed length, all
admissible relative words over a finite base and finite peripheral index have
only finitely many patterns.  Peripheral values may still range over infinite
subgroups; only their labels are forgotten. -/
def FiniteRelativeWordPatternStatement : Prop :=
  ∀ (G : Type u) (_ : Group G) (I : Type v) [Finite I]
    (D : RelGenSet G I),
    D.base.Finite → ∀ N : ℕ,
      {p : RelativeWordPattern G I |
        p.length ≤ N ∧
          ∃ w : List (RelLetter G I),
            (∀ a ∈ w, D.IsLetter a) ∧ relativeWordPattern w = p}.Finite

theorem finiteRelativeWordPattern_proved :
    FiniteRelativeWordPatternStatement.{u, v} := by
  intro G instG I _ D hbase N
  letI : Group G := instG
  let F : Set (Sum G I) := relativePatternSupport D
  have hF : F.Finite := by
    exact (hbase.image (Sum.inl : G → Sum G I)).union (Set.finite_range _)
  have hlist := finite_lists_of_finite_support hF N
  refine Set.Finite.subset hlist ?_
  intro p hp
  refine ⟨hp.1, ?_⟩
  obtain ⟨w, hw, hpat⟩ := hp.2
  rw [← hpat]
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  exact relativeLetterPattern_mem_support D (hw a ha)

/-- Trivial-family model test for the finite pattern statement.  The pattern
support is the finite base image; no peripheral values are present. -/
theorem finiteRelativeWordPattern_trivialModel
    {I : Type v} [Finite I] (D : RelGenSet PUnit I)
    (hbase : D.base.Finite) (N : ℕ) :
    {p : RelativeWordPattern PUnit I |
      p.length ≤ N ∧
        ∃ w : List (RelLetter PUnit I),
          (∀ a ∈ w, D.IsLetter a) ∧ relativeWordPattern w = p}.Finite :=
  finiteRelativeWordPattern_proved PUnit inferInstance I D hbase N

/-! ## Infinite repeated patterns for bounded admissible powers -/

/-- The pattern-level pigeonhole statement preceding Osin's geometric
double-coset extraction.  It assumes the bounded family already comes with
admissible relative spellings, so it is independent of the absent conversion
from a vertex word metric bound to a labelled relative word. -/
def InfiniteRepeatedRelativePatternStatement : Prop :=
  ∀ (G : Type u) (_ : Group G) (I : Type v) [Finite I]
    (D : RelGenSet G I),
    D.base.Finite → ∀ N : ℕ, ∀ (g : G) (S : Set ℕ), S.Infinite →
      (∀ q : ℕ, q ∈ S →
        ∃ w : List (RelLetter G I),
          (∀ a ∈ w, D.IsLetter a) ∧ w.length ≤ N ∧
            RelLetter.listVal w = g ^ q) →
      ∃ p : RelativeWordPattern G I, ∃ T : Set ℕ,
        T ⊆ S ∧ T.Infinite ∧
          ∀ q : ℕ, q ∈ T → ∃ w : List (RelLetter G I),
            (∀ a ∈ w, D.IsLetter a) ∧ w.length ≤ N ∧
              relativeWordPattern w = p ∧ RelLetter.listVal w = g ^ q

theorem infiniteRepeatedRelativePattern_proved :
    InfiniteRepeatedRelativePatternStatement.{u, v} := by
  intro G instG I _ D hbase N g S hS hwords
  letI : Group G := instG
  let P : Set (RelativeWordPattern G I) :=
    {p | p.length ≤ N ∧
      ∃ w : List (RelLetter G I),
        (∀ a ∈ w, D.IsLetter a) ∧ relativeWordPattern w = p}
  have hP : P.Finite := finiteRelativeWordPattern_proved G instG I D hbase N
  letI : Infinite S := hS.to_subtype
  letI : Finite P := hP.to_subtype
  let w : S → List (RelLetter G I) := fun q =>
    Classical.choose (hwords q.1 q.2)
  have hw (q : S) :
      (∀ a ∈ w q, D.IsLetter a) ∧ (w q).length ≤ N ∧
        RelLetter.listVal (w q) = g ^ q.1 := by
    exact Classical.choose_spec (hwords q.1 q.2)
  let f : S → P := fun q =>
    ⟨relativeWordPattern (w q),
      ⟨by simpa [relativeWordPattern] using (hw q).2.1,
        ⟨w q, (hw q).1, rfl⟩⟩⟩
  obtain ⟨p, hp⟩ := Finite.exists_infinite_fiber f
  let U : Set S := f ⁻¹' ({p} : Set P)
  haveI : Infinite U := hp
  let T : Set ℕ := {q | ∃ hq : q ∈ S, f ⟨q, hq⟩ ∈ ({p} : Set P)}
  have hT : T.Infinite := by
    apply Set.infinite_of_injective_forall_mem (α := U) (β := ℕ)
      (f := fun q : U => (q.1.1 : ℕ))
      (by
        intro q r h
        apply Subtype.ext
        apply Subtype.ext
        exact h)
    intro q
    exact ⟨q.1.2, q.2⟩
  refine ⟨(p : RelativeWordPattern G I), T, ?_, hT, ?_⟩
  · intro q hq
    exact hq.choose
  · intro q hq
    obtain ⟨hqS, hqmem⟩ := hq
    have hfp : f ⟨q, hqS⟩ = p := Set.mem_singleton_iff.mp hqmem
    refine ⟨w ⟨q, hqS⟩, (hw ⟨q, hqS⟩).1, (hw ⟨q, hqS⟩).2.1, ?_,
      (hw ⟨q, hqS⟩).2.2⟩
    exact congrArg Subtype.val hfp

/-- The repeated-pattern statement is model-tested in the one-point group:
the order-free spelling hypothesis is witnessed by the empty word. -/
theorem infiniteRepeatedRelativePattern_trivialModel
    {I : Type v} [Finite I] (D : RelGenSet PUnit I) (hbase : D.base.Finite)
    (N : ℕ) (S : Set ℕ) (hS : S.Infinite) :
    ∃ p : RelativeWordPattern PUnit I, ∃ T : Set ℕ,
      T ⊆ S ∧ T.Infinite ∧
        ∀ q : ℕ, q ∈ T → ∃ w : List (RelLetter PUnit I),
          (∀ a ∈ w, D.IsLetter a) ∧ w.length ≤ N ∧
            relativeWordPattern w = p ∧ RelLetter.listVal w = (1 : PUnit) ^ q := by
  apply infiniteRepeatedRelativePattern_proved PUnit inferInstance I D hbase N
    (1 : PUnit) S hS
  intro q hq
  refine ⟨[], by simp, by simp, by simp [RelLetter.listVal]⟩

end RelHyp
end GGT
end GroupApproximation
