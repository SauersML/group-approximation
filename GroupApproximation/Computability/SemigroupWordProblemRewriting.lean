import Mathlib.Data.List.Infix
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Logic.Relation

/-!
# String rewriting, Thue equivalence, and a local determinism criterion

This is the machine-independent half of the **Markov--Post theorem**: the word
problem for finitely presented semigroups (monoids) is undecidable.  Nothing in
this file mentions a machine; it develops the rewriting theory that the
simulation in `SemigroupWordProblemSimulation` consumes.

## Where this sits in the project

`GroupApproximation/Computability/AdianRabinMarkovProperty.lean` records the
debt of the manuscript's undecidability corollary --- `\label{cor:undecidable}`
inside `\subsection{Undecidability of MF recognition}` of `sec:consequences` in
`non_mf_group_notes.tex` --- as five items `D1`--`D5`.  Item **`D3`** is:

> **D3. Undecidability of the word problem for finitely presented semigroups**
> (Markov--Post).  Simulate a Turing machine [...] by a semi-Thue system; prove
> both directions of the simulation.

This file, `SemigroupWordProblemMachine` and `SemigroupWordProblemSimulation`
attack `D3`.  **No declaration in any of the three files certifies a manuscript
statement**; they are infrastructure for a literature input the manuscript
declares and does not use elsewhere.  The precise remaining debt, after
everything these files prove, is catalogued in the module docstring of
`SemigroupWordProblem.lean`.

## The mathematical point of this file

The classical difficulty in Markov--Post is not the easy direction (a halting
computation yields a chain of rewrites, hence an equality of words) but the
hard one: an *equality in the monoid* is an arbitrary zig-zag of forward and
backward rewrites, and one must show it cannot accidentally connect two words
whose machine never halts.  The standard cure is a confluence argument.  Here
the confluence is obtained in the cheapest honest way:

* every rewriting rule has a left-hand side of the shape `pre ++ s :: post`
  where `s` is a letter of **weight one** and `pre`, `post` consist of letters
  of weight zero (`IsLocal`);
* consequently a rewrite step preserves the total weight of a word
  (`Step.weight_eq`), so the set of words of weight one is closed under
  rewriting in *both* directions;
* on a word of weight `1` the position of the redex is pinned by the unique
  weight-one letter (`split_unique`), so at most one rule fires at one place:
  the one-step relation is a **partial function** there (`Step.det`);
* a partial function is trivially confluent, so the Church--Rosser property
  (`reflTransGen_churchRosser`) follows from a bare linearity argument
  (`reflTransGen_linear`) with no critical-pair or Newman machinery.

`thueEquiv_iff_derives` is the resulting interface: if the target word admits
no rewrite at all, then a two-sided Thue equivalence into it is already a
one-sided derivation.

The closure operator is Mathlib's `Relation.ReflTransGen`.  Mathlib's own
confluence lemmas (`Relation.ReflTransGen.total_of_right_unique`,
`Relation.church_rosser`) are not applicable as they stand, because they
require the one-step relation to be right-unique *globally*, whereas here it is
right-unique only on the invariant set of words of weight one; the two lemmas
proved below are those statements relativised to such a set.
-/

namespace GroupApproximation
namespace SemigroupWordProblem

open Relation

/-! ## Confluence relative to an invariant set

The reflexive--transitive closure is Mathlib's `Relation.ReflTransGen`, and its
basic API (`refl`, `single`, `tail`, `head`, `trans`, `mono`, `cases_head`) is
used as it stands.  What Mathlib does not have, and what this section supplies,
is the *relative* form of the confluence argument: Mathlib's
`Relation.ReflTransGen.total_of_right_unique` and `Relation.church_rosser` ask
for global hypotheses, whereas the rewriting system below is a partial function
only on the words of weight one.  Those words are an invariant set, closed
under rewriting in both directions, and that is exactly the hypothesis shape
here. -/

/-- The symmetric closure of a relation.  (`Relation.SymmGen` is the same
relation; this abbreviation is kept so that the `Or` structure is available by
`rcases` without unfolding.) -/
def symClosure {β : Type} (r : β → β → Prop) : β → β → Prop :=
  fun x y => r x y ∨ r y x

section Closure

variable {β : Type} {r : β → β → Prop} {a b c : β}

/-- Chains of a symmetric relation are symmetric. -/
theorem reflTransGen_symm (hsymm : ∀ x y, r x y → r y x) (h : ReflTransGen r a b) :
    ReflTransGen r b a := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail had hstep ih => exact (ReflTransGen.single (hsymm _ _ hstep)).trans ih

/-- A predicate closed under one step is closed along chains. -/
theorem reflTransGen_closure {S : β → Prop} (hcl : ∀ x y, S x → r x y → S y) (ha : S a)
    (h : ReflTransGen r a b) : S b := by
  induction h with
  | refl => exact ha
  | tail had hstep ih => exact hcl _ _ ih hstep

/-- Nothing is reachable from a normal form except itself. -/
theorem eq_of_normalForm (hnf : ∀ x, ¬ r a x) (h : ReflTransGen r a b) : a = b := by
  rcases h.cases_head with h' | ⟨d, hd, _⟩
  · exact h'
  · exact absurd hd (hnf d)

/-- **Linearity.**  If `r` is a partial function on a set `S` closed under `r`,
then any two chains out of a point of `S` are comparable: one of the two
endpoints is reachable from the other.  This is the whole confluence content of
a deterministic rewriting system.  It is
`Relation.ReflTransGen.total_of_right_unique` with the right-uniqueness
hypothesis relativised to `S`. -/
theorem reflTransGen_linear {S : β → Prop}
    (hcl : ∀ x y, S x → r x y → S y)
    (hfun : ∀ x y z, S x → r x y → r x z → y = z)
    (ha : S a) (hab : ReflTransGen r a b) (hac : ReflTransGen r a c) :
    ReflTransGen r b c ∨ ReflTransGen r c b := by
  induction hab with
  | refl => exact Or.inl hac
  | tail had hstep ih =>
      rcases ih with hcase | hcase
      · rcases hcase.cases_head with rfl | ⟨f, hf, hfc⟩
        · exact Or.inr (ReflTransGen.single hstep)
        · have hSd := reflTransGen_closure hcl ha had
          have hfe := hfun _ _ _ hSd hf hstep
          subst hfe
          exact Or.inl hfc
      · exact Or.inr (hcase.tail hstep)

/-- **Church--Rosser from determinism.**  If `r` is a partial function on a set
`S` closed under `r` in both directions, then any zig-zag of forward and
backward steps between points of `S` can be completed to a common reduct. -/
theorem reflTransGen_churchRosser {S : β → Prop}
    (hcl : ∀ x y, S x → r x y → S y)
    (hcl' : ∀ x y, S y → r x y → S x)
    (hfun : ∀ x y z, S x → r x y → r x z → y = z)
    (ha : S a) (hab : ReflTransGen (symClosure r) a b) :
    ∃ d, ReflTransGen r a d ∧ ReflTransGen r b d := by
  have hclSym : ∀ x y, S x → symClosure r x y → S y := by
    intro x y hx hxy
    rcases hxy with hxy | hxy
    · exact hcl x y hx hxy
    · exact hcl' y x hx hxy
  induction hab with
  | refl => exact ⟨a, ReflTransGen.refl, ReflTransGen.refl⟩
  | tail hae hstep ih =>
      obtain ⟨d, had, hed⟩ := ih
      have hSe := reflTransGen_closure hclSym ha hae
      rcases hstep with hstep | hstep
      · rcases reflTransGen_linear hcl hfun hSe hed (ReflTransGen.single hstep) with
          hcase | hcase
        · exact ⟨_, had.trans hcase, ReflTransGen.refl⟩
        · exact ⟨d, had, hcase⟩
      · exact ⟨d, had, (ReflTransGen.single hstep).trans hed⟩

end Closure

/-! ## Weights of words

A *weight* is a function from letters to natural numbers; the weight of a word
is the sum of the weights of its letters.  Weight one will mean "contains
exactly one control letter".  Working with `ℕ`-valued weights rather than with
`List.countP` keeps every side condition inside `omega`. -/

/-- The total weight of a word. -/
def weight {α : Type} (w : α → ℕ) : List α → ℕ
  | [] => 0
  | a :: l => w a + weight w l

@[simp] theorem weight_nil {α : Type} (w : α → ℕ) : weight w ([] : List α) = 0 := by
  simp [weight]

@[simp] theorem weight_cons {α : Type} (w : α → ℕ) (a : α) (l : List α) :
    weight w (a :: l) = w a + weight w l := by
  simp [weight]

@[simp] theorem weight_append {α : Type} (w : α → ℕ) (l₁ l₂ : List α) :
    weight w (l₁ ++ l₂) = weight w l₁ + weight w l₂ := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simp [ih, Nat.add_assoc]

/-- **Unique splitting at a distinguished letter.**  A word containing exactly
one letter of positive weight can be cut at that letter in exactly one way.
This is the combinatorial heart of the determinism criterion below. -/
theorem split_unique {α : Type} {w : α → ℕ} (A : List α) :
    ∀ (A' B B' : List α) (s s' : α),
      weight w A = 0 → weight w A' = 0 → w s = 1 → w s' = 1 →
      A ++ s :: B = A' ++ s' :: B' → A = A' ∧ s = s' ∧ B = B' := by
  induction A with
  | nil =>
      intro A' B B' s s' _ hA' hs hs' h
      cases A' with
      | nil =>
          simp only [List.nil_append] at h
          exact ⟨rfl, (List.cons.inj h).1, (List.cons.inj h).2⟩
      | cons a' t' =>
          exfalso
          simp only [List.nil_append, List.cons_append] at h
          have hsa : s = a' := (List.cons.inj h).1
          rw [weight_cons] at hA'
          rw [hsa] at hs
          omega
  | cons a t ih =>
      intro A' B B' s s' hA hA' hs hs' h
      cases A' with
      | nil =>
          exfalso
          simp only [List.nil_append, List.cons_append] at h
          have hsa : a = s' := (List.cons.inj h).1
          rw [weight_cons] at hA
          rw [hsa] at hA
          omega
      | cons a' t' =>
          simp only [List.cons_append] at h
          have hh : a = a' := (List.cons.inj h).1
          have ht : t ++ s :: B = t' ++ s' :: B' := (List.cons.inj h).2
          rw [weight_cons] at hA hA'
          obtain ⟨h1, h2, h3⟩ := ih t' B B' s s' (by omega) (by omega) hs hs' ht
          exact ⟨by rw [hh, h1], h2, h3⟩

/-! ## Local rewriting systems

A rewriting system is given by an index type `ι` of rules; rule `i` rewrites
the word `pre i ++ sp i :: post i` to `rhs i`.  The system is *local* for a
weight `w` when the conditions of `IsLocal` hold. -/

section Rewriting

variable {α : Type} {ι : Type} {w : α → ℕ} {sp : ι → α} {pre post rhs : ι → List α}
  {u v : List α}

/-- The left-hand word of rule `i`. -/
def lhsWord (sp : ι → α) (pre post : ι → List α) (i : ι) : List α :=
  pre i ++ sp i :: post i

/-- One step of rewriting: replace one occurrence of a left-hand word by the
corresponding right-hand word. -/
def Step (sp : ι → α) (pre post rhs : ι → List α) (u v : List α) : Prop :=
  ∃ (i : ι) (x y : List α),
    u = x ++ lhsWord sp pre post i ++ y ∧ v = x ++ rhs i ++ y

/-- The defining relations of the presented monoid attached to the system: the
set of pairs (left-hand word, right-hand word). -/
def Rules (sp : ι → α) (pre post rhs : ι → List α) (p q : List α) : Prop :=
  ∃ i, p = lhsWord sp pre post i ∧ q = rhs i

/-- `Step` is exactly the closure of `Rules` under two-sided context. -/
theorem step_iff_context (sp : ι → α) (pre post rhs : ι → List α) (u v : List α) :
    Step sp pre post rhs u v ↔
      ∃ p q x y, Rules sp pre post rhs p q ∧ u = x ++ p ++ y ∧ v = x ++ q ++ y := by
  constructor
  · rintro ⟨i, x, y, hu, hv⟩
    exact ⟨lhsWord sp pre post i, rhs i, x, y, ⟨i, rfl, rfl⟩, hu, hv⟩
  · rintro ⟨p, q, x, y, ⟨i, rfl, rfl⟩, hu, hv⟩
    exact ⟨i, x, y, hu, hv⟩

/-- Finitely many rules, if there are finitely many rule indices. -/
theorem rules_finite [Finite ι] (sp : ι → α) (pre post rhs : ι → List α) :
    {pq : List α × List α | Rules sp pre post rhs pq.1 pq.2}.Finite := by
  refine Set.Finite.subset
    (Set.finite_range (fun i => (lhsWord sp pre post i, rhs i))) ?_
  rintro ⟨p, q⟩ hpq
  obtain ⟨i, h1, h2⟩ := hpq
  have h1' : p = lhsWord sp pre post i := h1
  have h2' : q = rhs i := h2
  exact ⟨i, by rw [h1', h2']⟩

/-- The structural conditions making a rewriting system *local*: every rule
consumes exactly one letter of weight one, produces exactly one letter of
weight one, all context letters have weight zero, the shape of a rule is
determined by its control letter, and a rule is determined by its left-hand
word. -/
structure IsLocal (w : α → ℕ) (sp : ι → α) (pre post rhs : ι → List α) : Prop where
  /-- The control letter of a rule has weight one. -/
  sp_weight : ∀ i, w (sp i) = 1
  /-- The left context of a rule has weight zero. -/
  pre_weight : ∀ i, weight w (pre i) = 0
  /-- The right context of a rule has weight zero. -/
  post_weight : ∀ i, weight w (post i) = 0
  /-- The right-hand word of a rule has weight one. -/
  rhs_weight : ∀ i, weight w (rhs i) = 1
  /-- The length of the left context depends only on the control letter. -/
  pre_length : ∀ i j, sp i = sp j → (pre i).length = (pre j).length
  /-- The length of the right context depends only on the control letter. -/
  post_length : ∀ i j, sp i = sp j → (post i).length = (post j).length
  /-- A rule is determined by its left-hand word. -/
  rhs_eq : ∀ i j, pre i = pre j → sp i = sp j → post i = post j → rhs i = rhs j

/-- Every left-hand word of a local system has weight one. -/
theorem weight_lhsWord (w : α → ℕ) (h : IsLocal w sp pre post rhs) (i : ι) :
    weight w (lhsWord sp pre post i) = 1 := by
  simp [lhsWord, h.pre_weight i, h.post_weight i, h.sp_weight i]

/-- Rewriting preserves the total weight. -/
theorem Step.weight_eq (h : IsLocal w sp pre post rhs) (hst : Step sp pre post rhs u v) :
    weight w v = weight w u := by
  obtain ⟨i, x, y, hu, hv⟩ := hst
  have h1 : weight w (lhsWord sp pre post i) = 1 := weight_lhsWord w h i
  have h2 : weight w (rhs i) = 1 := h.rhs_weight i
  subst hu
  subst hv
  simp only [weight_append, h1, h2]

/-- **Determinism.**  On a word of weight one, at most one rule fires, at one
place: the one-step relation is a partial function there. -/
theorem Step.det (h : IsLocal w sp pre post rhs) {v₁ v₂ : List α} (hu : weight w u = 1)
    (h₁ : Step sp pre post rhs u v₁) (h₂ : Step sp pre post rhs u v₂) : v₁ = v₂ := by
  obtain ⟨i, x₁, y₁, hu₁, hv₁⟩ := h₁
  obtain ⟨j, x₂, y₂, hu₂, hv₂⟩ := h₂
  have e₁ : u = (x₁ ++ pre i) ++ sp i :: (post i ++ y₁) := by
    rw [hu₁]; simp [lhsWord]
  have e₂ : u = (x₂ ++ pre j) ++ sp j :: (post j ++ y₂) := by
    rw [hu₂]; simp [lhsWord]
  have hw₁ : weight w (x₁ ++ pre i) = 0 ∧ weight w (post i ++ y₁) = 0 := by
    have hx : weight w u = 1 := hu
    rw [e₁] at hx
    simp only [weight_append, weight_cons, h.sp_weight i, h.pre_weight i,
      h.post_weight i] at hx ⊢
    omega
  have hw₂ : weight w (x₂ ++ pre j) = 0 ∧ weight w (post j ++ y₂) = 0 := by
    have hx : weight w u = 1 := hu
    rw [e₂] at hx
    simp only [weight_append, weight_cons, h.sp_weight j, h.pre_weight j,
      h.post_weight j] at hx ⊢
    omega
  obtain ⟨hA, hs, hB⟩ :=
    split_unique (w := w) (x₁ ++ pre i) (x₂ ++ pre j) (post i ++ y₁) (post j ++ y₂)
      (sp i) (sp j) hw₁.1 hw₂.1 (h.sp_weight i) (h.sp_weight j) (e₁.symm.trans e₂)
  have hplen : (pre i).length = (pre j).length := h.pre_length i j hs
  have hqlen : (post i).length = (post j).length := h.post_length i j hs
  have hxlen : x₁.length = x₂.length := by
    have hlen := congrArg List.length hA
    simp only [List.length_append] at hlen
    omega
  have hx : x₁ = x₂ := List.append_inj_left hA hxlen
  have hpre : pre i = pre j := List.append_inj_right hA hxlen
  have hpost : post i = post j := List.append_inj_left hB hqlen
  have hy : y₁ = y₂ := List.append_inj_right hB hqlen
  have hrhs : rhs i = rhs j := h.rhs_eq i j hpre hs hpost
  rw [hv₁, hv₂, hx, hy, hrhs]

/-! ## Derivations and the Thue equivalence -/

/-- Multi-step rewriting. -/
def Derives (sp : ι → α) (pre post rhs : ι → List α) (u v : List α) : Prop :=
  ReflTransGen (Step sp pre post rhs) u v

/-- The Thue equivalence generated by the rules: the reflexive, symmetric and
transitive closure of one-step rewriting.  This is equality in the presented
monoid. -/
def ThueEquiv (sp : ι → α) (pre post rhs : ι → List α) (u v : List α) : Prop :=
  ReflTransGen (symClosure (Step sp pre post rhs)) u v

theorem Derives.refl (sp : ι → α) (pre post rhs : ι → List α) (u : List α) :
    Derives sp pre post rhs u u := ReflTransGen.refl

theorem Derives.single (h : Step sp pre post rhs u v) : Derives sp pre post rhs u v :=
  ReflTransGen.single h

theorem Derives.trans {t : List α} (h₁ : Derives sp pre post rhs u v)
    (h₂ : Derives sp pre post rhs v t) : Derives sp pre post rhs u t :=
  ReflTransGen.trans h₁ h₂

theorem Derives.head (h : Step sp pre post rhs u v) {t : List α}
    (h' : Derives sp pre post rhs v t) : Derives sp pre post rhs u t :=
  ReflTransGen.head h h'

/-- A derivation is in particular a Thue equivalence. -/
theorem Derives.toThueEquiv (h : Derives sp pre post rhs u v) :
    ThueEquiv sp pre post rhs u v :=
  ReflTransGen.mono (fun _ _ hxy => Or.inl hxy) u v h

theorem ThueEquiv.refl (sp : ι → α) (pre post rhs : ι → List α) (u : List α) :
    ThueEquiv sp pre post rhs u u := ReflTransGen.refl

theorem ThueEquiv.symm (h : ThueEquiv sp pre post rhs u v) :
    ThueEquiv sp pre post rhs v u :=
  reflTransGen_symm (fun _ _ hxy => hxy.elim Or.inr Or.inl) h

theorem ThueEquiv.trans {t : List α} (h₁ : ThueEquiv sp pre post rhs u v)
    (h₂ : ThueEquiv sp pre post rhs v t) : ThueEquiv sp pre post rhs u t :=
  ReflTransGen.trans h₁ h₂

/-- Rewriting in a context: a step survives multiplication on both sides. -/
theorem Step.append (x y : List α) (h : Step sp pre post rhs u v) :
    Step sp pre post rhs (x ++ u ++ y) (x ++ v ++ y) := by
  obtain ⟨i, x₀, y₀, hu, hv⟩ := h
  refine ⟨i, x ++ x₀, y₀ ++ y, ?_, ?_⟩
  · rw [hu]; simp [List.append_assoc]
  · rw [hv]; simp [List.append_assoc]

/-- A defining relation is a rewrite step, taken with empty context. -/
theorem step_of_rules {p q : List α} (h : Rules sp pre post rhs p q) :
    Step sp pre post rhs p q := by
  obtain ⟨i, hp, hq⟩ := h
  refine ⟨i, [], [], ?_, ?_⟩
  · simp [hp]
  · simp [hq]

/-- Thue equivalence is a congruence for concatenation. -/
theorem ThueEquiv.append (x y : List α) (h : ThueEquiv sp pre post rhs u v) :
    ThueEquiv sp pre post rhs (x ++ u ++ y) (x ++ v ++ y) := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail hd hstep ih =>
      refine ReflTransGen.tail ih ?_
      rcases hstep with hstep | hstep
      · exact Or.inl (Step.append x y hstep)
      · exact Or.inr (Step.append x y hstep)

/-- Thue equivalence survives appending a word on the right. -/
theorem ThueEquiv.appendRight (y : List α) (h : ThueEquiv sp pre post rhs u v) :
    ThueEquiv sp pre post rhs (u ++ y) (v ++ y) := by
  have h' := ThueEquiv.append (sp := sp) (pre := pre) (post := post) (rhs := rhs) [] y h
  simpa using h'

/-- Thue equivalence survives appending a word on the left. -/
theorem ThueEquiv.appendLeft (x : List α) (h : ThueEquiv sp pre post rhs u v) :
    ThueEquiv sp pre post rhs (x ++ u) (x ++ v) := by
  have h' := ThueEquiv.append (sp := sp) (pre := pre) (post := post) (rhs := rhs) x [] h
  simpa using h'

/-- **Thue equivalence is a monoid congruence.**  This is the compatibility
condition that makes the quotient of the free monoid by `ThueEquiv` the monoid
presented by the rules. -/
theorem ThueEquiv.mul {u' v' : List α} (h : ThueEquiv sp pre post rhs u u')
    (h' : ThueEquiv sp pre post rhs v v') :
    ThueEquiv sp pre post rhs (u ++ v) (u' ++ v') :=
  ThueEquiv.trans (ThueEquiv.appendRight v h) (ThueEquiv.appendLeft u' h')

/-- **The interface theorem.**  If the target word admits no rewrite, a
two-sided Thue equivalence into it is already a one-sided derivation.  This is
the step that turns "the words are equal in the monoid" into "the machine
halts". -/
theorem thueEquiv_iff_derives (h : IsLocal w sp pre post rhs) (hu : weight w u = 1)
    (hnf : ∀ z, ¬ Step sp pre post rhs v z) :
    ThueEquiv sp pre post rhs u v ↔ Derives sp pre post rhs u v := by
  constructor
  · intro hEq
    obtain ⟨d, hud, hvd⟩ :=
      reflTransGen_churchRosser (r := Step sp pre post rhs)
        (S := fun z => weight w z = 1)
        (fun _ _ hx hxy => (Step.weight_eq h hxy).trans hx)
        (fun _ _ hy hxy => (Step.weight_eq h hxy).symm.trans hy)
        (fun _ _ _ hx h1 h2 => Step.det h hx h1 h2)
        hu hEq
    have hvd' : v = d := eq_of_normalForm hnf hvd
    rw [hvd']
    exact hud
  · exact Derives.toThueEquiv

end Rewriting

end SemigroupWordProblem
end GroupApproximation
