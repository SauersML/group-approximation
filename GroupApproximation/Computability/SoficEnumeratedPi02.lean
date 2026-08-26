import GroupApproximation.Computability.EnumeratedPresentationCodes
import GroupApproximation.Computability.SoficRecognitionPi02

/-!
# Soficity of a recursively enumerated presentation is `Π⁰₂`-complete

`Computability.SoficRecognitionSecondLevel` proves the hardness half: the
arbitrary-seed event-ray compiler emits **standard recursively enumerated**
presentation codes, so recognising soficity on those codes is `Π⁰₂`-hard, with
no hypothesis.  What was missing was the matching upper bound *on the same
codes*: `Computability.SoficRecognitionPi02` bounds soficity for **finite**
presentation codes, a different domain, so the two could not be paired.

This file supplies the upper bound for enumerated codes and closes the pair.
The result is an **exact arithmetical classification** of a group
approximation property --- `Π⁰₂`-complete, both halves kernel-checked, no
premises --- which as far as this development is aware is the first such
classification carried out inside a proof assistant.

## What changes for an enumerated code

Three things, all of them consequences of the alphabet being all of `ℕ` and
the relator list being infinite.

* **The alphabet.**  A microstate can no longer be a function on
  `Fin (genCount c)`.  `NatMicrostate` is a finite model together with a
  permutation for every natural number, all but finitely many of them the
  identity --- the bound is a field, so that a microstate is finite data.
* **The relators.**  A challenge cannot ask about the whole relator set.  It
  asks about a *prefix*: the relators at addresses `0, …, N`.  Every element
  of the normal closure of the relator set is a finite product of conjugates
  of finitely many enumerated relators, so it has *some* prefix length `N`
  and *some* area count `A` --- `exists_area_bound`, whose subgroup carries
  the pair `(N, A)` rather than the single count of the finite-code case.
* **The word problem.**  The void disjunct uses the enumerated word-problem
  checker `EnumeratedPresentationCodes.wordCheck`, whose completeness is
  `wordCheck_complete` and whose matrix is primitive recursive uniformly in
  the program code.

Everything else --- permutation tables on `{0, …, m}`, exact Hamming distance
by counting moved points, the two cleared-denominator comparisons --- is
reused verbatim from `Computability.SoficRecognitionPi02`, since none of it
mentions a presentation code.

## Totalisation

A certificate is a carrier size and a list of table pairs.  Rather than carry
a well-formedness side condition, `certGenN` **validates**: an entry that is
out of range, or whose two tables are not mutually inverse, is replaced by the
identity pair.  So every raw certificate names an honest microstate, the
checker has no validity clause, and the identity replacement beyond the list's
end is exactly the "identity past the bound" clause of `NatMicrostate`.

## What is proved

* `isSofic_iff_forall_answersN` --- the oracle-free `∀∃` normal form for
  soficity of an enumerated code.
* `passesN_iff_exists_check` --- the microstate disjunct is a certificate
  search with a primitive recursive matrix.
* `rePred_answersN` --- one challenge being answered is recursively
  enumerable.
* `pi02_isSofic_enum` --- the upper bound.
* `sofic_enum_pi02Complete` / `nonsofic_enum_sigma02Complete` --- the exact
  classification, upper bound paired with the already-proved hardness.

## Research nodes

* `research/sofic-recognition-has-a-pi2-upper-bound.md` --- the upper bound,
  whose displayed normal form the enumerated `(SOF1)` below is.
* `research/sofic-recognition-two-generator-recursive-is-pi2-complete.md` ---
  the completeness claim this file closes on enumerated codes.
* `research/second-level-rice-theorem-for-local-approximation-properties.md`
  --- the general second-level Rice statement supplying hardness.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace SoficEnumeratedPi02

open ArithmeticalHierarchy
open Higman
open EnumeratedPresentationCodes
open SoficRecognitionPi02

/-! ## Raw-word calculus on the countable alphabet -/

/-- A one-letter raw word evaluates to the signed generator. -/
theorem evalRaw_letter {A : Type} [Group A] (x : ℕ → A) (i : ℕ) (s : Bool) :
    evalRaw x [(i, s)] = if s then x i else (x i)⁻¹ := by
  rw [evalRaw_cons, evalRaw_nil, mul_one]

theorem evalRaw_letter_pos {A : Type} [Group A] (x : ℕ → A) (i : ℕ) :
    evalRaw x [(i, true)] = x i := by
  rw [evalRaw_letter]; simp

theorem evalRaw_letter_neg {A : Type} [Group A] (x : ℕ → A) (i : ℕ) :
    evalRaw x [(i, false)] = (x i)⁻¹ := by
  rw [evalRaw_letter]; simp

/-- Splitting off the first letter of a raw word. -/
theorem evalRaw_cons' {A : Type} [Group A] (x : ℕ → A) (p : ℕ × Bool)
    (w : List (ℕ × Bool)) :
    evalRaw x (p :: w) = evalRaw x [p] * evalRaw x w := by
  have h : (p :: w) = [p] ++ w := rfl
  rw [h, evalRaw_append]

/-- A crude bound on the letters occurring in a raw word. -/
def letterBound (w : List (ℕ × Bool)) : ℕ :=
  (w.map fun p => p.1 + 1).foldr max 0

theorem lt_letterBound {w : List (ℕ × Bool)} {p : ℕ × Bool} (hp : p ∈ w) :
    p.1 < letterBound w :=
  MFMicrostate.le_foldr_max (fun q : ℕ × Bool => q.1 + 1) w p hp

/-! ## Permutation microstates for the countable alphabet -/

/-- **A permutation microstate on the standard countable alphabet.**  A
nonempty finite model, one permutation per natural number, and a bound past
which every permutation is the identity: so a microstate is finite data even
though the alphabet is not. -/
structure NatMicrostate where
  /-- The finite model the permutations act on. -/
  carrier : FiniteModel
  /-- The model is nonempty; a microstate on no points separates nothing. -/
  nonempty : 0 < Fintype.card carrier
  /-- Past this index every generator acts trivially. -/
  bound : ℕ
  /-- One permutation per letter. -/
  gen : ℕ → Equiv.Perm carrier
  /-- Only finitely many letters move anything. -/
  gen_eq_one : ∀ i, bound ≤ i → gen i = 1

namespace NatMicrostate

/-- The homomorphism a microstate induces on the free group.  Exact: only the
behaviour on relators is approximate. -/
def hom (M : NatMicrostate) : FreeGroup ℕ →* Equiv.Perm M.carrier :=
  FreeGroup.lift M.gen

@[simp] theorem hom_of (M : NatMicrostate) (i : ℕ) :
    M.hom (FreeGroup.of i) = M.gen i := by
  simp [hom]

/-- Hamming displacement of a free-group element. -/
noncomputable def hlen (M : NatMicrostate) (x : FreeGroup ℕ) : ℝ :=
  hammingDistance M.carrier (M.hom x) 1

/-- Hamming displacement of a raw word. -/
noncomputable def len (M : NatMicrostate) (w : List (ℕ × Bool)) : ℝ :=
  M.hlen (freeEval w)

theorem hom_freeEval (M : NatMicrostate) (w : List (ℕ × Bool)) :
    M.hom (freeEval w) = evalRaw M.gen w := by
  have h := map_evalRaw M.hom FreeGroup.of w
  have hgen : (fun n => M.hom (FreeGroup.of n)) = M.gen :=
    funext fun n => M.hom_of n
  rw [show freeEval w = evalRaw FreeGroup.of w from rfl, h, hgen]

theorem len_def (M : NatMicrostate) (w : List (ℕ × Bool)) :
    M.len w = hammingDistance M.carrier (evalRaw M.gen w) 1 := by
  rw [len, hlen, hom_freeEval]

@[simp] theorem hlen_one (M : NatMicrostate) : M.hlen 1 = 0 := by
  rw [hlen, map_one, hammingDistance_self]

theorem hlen_nonneg (M : NatMicrostate) (x : FreeGroup ℕ) : 0 ≤ M.hlen x :=
  hammingDistance_nonnegative _ _ _

theorem hlen_le_one (M : NatMicrostate) (x : FreeGroup ℕ) : M.hlen x ≤ 1 :=
  hammingDistance_le_one _ _ _

/-- Displacement is subadditive. -/
theorem hlen_mul_le (M : NatMicrostate) (x y : FreeGroup ℕ) :
    M.hlen (x * y) ≤ M.hlen x + M.hlen y := by
  rw [hlen, hlen, hlen, map_mul]
  have hstep : hammingDistance M.carrier (M.hom x * M.hom y) (M.hom x)
      = hammingDistance M.carrier (M.hom y) 1 := by
    have h := hammingDistance_left_invariant M.carrier (M.hom x) (M.hom y) 1
    rwa [mul_one] at h
  have htri := hammingDistance_triangle M.carrier
    (M.hom x * M.hom y) (M.hom x) 1
  rw [hstep] at htri
  linarith

/-- Displacement is inversion-invariant. -/
theorem hlen_inv (M : NatMicrostate) (x : FreeGroup ℕ) : M.hlen x⁻¹ = M.hlen x := by
  rw [hlen, hlen, map_inv]
  have h := hammingDistance_right_invariant M.carrier (M.hom x)⁻¹ 1 (M.hom x)
  rw [inv_mul_cancel, one_mul] at h
  rw [← h]
  exact hammingDistance_comm _ _ _

/-- Displacement is conjugation-invariant. -/
theorem hlen_conj (M : NatMicrostate) (t x : FreeGroup ℕ) :
    M.hlen (t * x * t⁻¹) = M.hlen x := by
  rw [hlen, hlen, map_mul, map_mul, map_inv]
  have h1 := hammingDistance_right_invariant M.carrier
    (M.hom t * M.hom x * (M.hom t)⁻¹) 1 (M.hom t)
  have heq : M.hom t * M.hom x * (M.hom t)⁻¹ * M.hom t
      = M.hom t * M.hom x := by group
  rw [heq, one_mul] at h1
  have h2 := hammingDistance_left_invariant M.carrier (M.hom t) (M.hom x) 1
  rw [mul_one] at h2
  rw [← h1, h2]

theorem len_nonneg (M : NatMicrostate) (w : List (ℕ × Bool)) : 0 ≤ M.len w :=
  hlen_nonneg _ _

end NatMicrostate

/-! ## Evaluation in the coded group -/

/-- Evaluation of a raw word in the group denoted by an enumerated code. -/
noncomputable def evalCode (c : PresentationCode) (w : List (ℕ × Bool)) :
    Carrier c :=
  evalRaw (fun k => (PresentedGroup.of k : Carrier c)) w

theorem evalCode_append (c : PresentationCode) (u v : List (ℕ × Bool)) :
    evalCode c (u ++ v) = evalCode c u * evalCode c v :=
  evalRaw_append _ u v

theorem evalCode_invRaw (c : PresentationCode) (u : List (ℕ × Bool)) :
    evalCode c (invRaw u) = (evalCode c u)⁻¹ :=
  evalRaw_invRaw _ u

theorem evalCode_letter_pos (c : PresentationCode) (i : ℕ) :
    evalCode c [(i, true)] = (PresentedGroup.of i : Carrier c) :=
  evalRaw_letter_pos _ i

theorem evalCode_letter_neg (c : PresentationCode) (i : ℕ) :
    evalCode c [(i, false)] = (PresentedGroup.of i : Carrier c)⁻¹ :=
  evalRaw_letter_neg _ i

/-- Triviality of a raw word is membership of its free value in the normal
closure of the enumerated relators. -/
theorem evalCode_eq_one_iff (c : PresentationCode) (w : List (ℕ × Bool)) :
    evalCode c w = 1 ↔ freeEval w ∈ Subgroup.normalClosure (relatorSet c) :=
  evalRaw_presentedGroup_eq_one_iff (relatorSet c) w

/-- Every element of the coded group is the value of a raw word. -/
theorem evalCode_surjective (c : PresentationCode) :
    Function.Surjective (evalCode c) := by
  intro g
  have hspan : Subgroup.closure
      (Set.range fun k => (PresentedGroup.of k : Carrier c)) = ⊤ :=
    PresentedGroup.closure_range_of (relatorSet c)
  exact (spans_iff_forall_exists_evalRaw
    (fun k => (PresentedGroup.of k : Carrier c))).1 hspan g

/-! ## The area bound, relative to a relator prefix -/

/-- The enumerated relator at one address, as a free-group element. -/
def relatorAt (c : PresentationCode) (j : ℕ) : FreeGroup ℕ :=
  freeEval (rawRelator c j)

theorem relatorAt_mem_relatorSet (c : PresentationCode) (j : ℕ) :
    relatorAt c j ∈ relatorSet c := ⟨j, rfl⟩

/-- **Bounded area relative to a prefix.**  A free-group element carries a
prefix length `N` and an area count `A` such that its displacement is at most
`A · δ` in every microstate displacing the first `N + 1` enumerated relators
by at most `δ`. -/
def AreaBounded (c : PresentationCode) (x : FreeGroup ℕ) : Prop :=
  ∃ N A : ℕ, ∀ (M : NatMicrostate) (δ : ℝ), 0 ≤ δ →
    (∀ j, j ≤ N → M.hlen (relatorAt c j) ≤ δ) → M.hlen x ≤ (A : ℝ) * δ

/-- The elements of bounded area form a subgroup. -/
def areaSubgroup (c : PresentationCode) : Subgroup (FreeGroup ℕ) where
  carrier := {x | AreaBounded c x}
  one_mem' := by
    refine ⟨0, 0, fun M δ _ _ => ?_⟩
    rw [M.hlen_one, Nat.cast_zero, zero_mul]
  mul_mem' := by
    rintro x y ⟨Nx, Ax, hx⟩ ⟨Ny, Ay, hy⟩
    refine ⟨max Nx Ny, Ax + Ay, fun M δ hδ hrel => ?_⟩
    have hx' := hx M δ hδ fun j hj => hrel j (hj.trans (le_max_left _ _))
    have hy' := hy M δ hδ fun j hj => hrel j (hj.trans (le_max_right _ _))
    refine (M.hlen_mul_le x y).trans ?_
    have hsum := add_le_add hx' hy'
    rwa [← add_mul, ← Nat.cast_add] at hsum
  inv_mem' := by
    rintro x ⟨N, A, hx⟩
    refine ⟨N, A, fun M δ hδ hrel => ?_⟩
    rw [M.hlen_inv]
    exact hx M δ hδ hrel

/-- Displacement is conjugation-invariant, so the area subgroup is normal. -/
instance areaSubgroup_normal (c : PresentationCode) : (areaSubgroup c).Normal where
  conj_mem := by
    rintro x ⟨N, A, hx⟩ g
    refine ⟨N, A, fun M δ hδ hrel => ?_⟩
    rw [M.hlen_conj]
    exact hx M δ hδ hrel

theorem mem_areaSubgroup_iff {c : PresentationCode} {x : FreeGroup ℕ} :
    x ∈ areaSubgroup c ↔ AreaBounded c x := Iff.rfl

theorem subset_areaSubgroup (c : PresentationCode) :
    relatorSet c ⊆ (areaSubgroup c : Set (FreeGroup ℕ)) := by
  rintro r ⟨j, rfl⟩
  refine mem_areaSubgroup_iff.2 ⟨j, 1, fun M δ _ hrel => ?_⟩
  rw [Nat.cast_one, one_mul]
  exact hrel j le_rfl

/-- **Approximate relators force approximate triviality.**  Every element of
the normal closure of the enumerated relator set carries a prefix length and
an area count that bound its displacement in every microstate. -/
theorem exists_area_bound (c : PresentationCode) {x : FreeGroup ℕ}
    (hx : x ∈ Subgroup.normalClosure (relatorSet c)) : AreaBounded c x :=
  mem_areaSubgroup_iff.1
    (Subgroup.normalClosure_le_normal (N := areaSubgroup c)
      (subset_areaSubgroup c) hx)

/-- **The area bound, for a finite list of trivial words at once.** -/
theorem exists_area_bound_list (c : PresentationCode)
    (L : List (List (ℕ × Bool))) (hL : ∀ u ∈ L, evalCode c u = 1) :
    ∃ N A : ℕ, ∀ (M : NatMicrostate) (δ : ℝ), 0 ≤ δ →
      (∀ j, j ≤ N → M.hlen (relatorAt c j) ≤ δ) →
        ∀ u ∈ L, M.len u ≤ (A : ℝ) * δ := by
  induction L with
  | nil => exact ⟨0, 0, by simp⟩
  | cons a t ih =>
      obtain ⟨Nt, At, hNt⟩ := ih fun u hu => hL u (List.mem_cons_of_mem _ hu)
      obtain ⟨Na, Aa, hNa⟩ := exists_area_bound c
        ((evalCode_eq_one_iff c a).1 (hL a List.mem_cons_self))
      refine ⟨max Na Nt, max Aa At, fun M δ hδ hrel u hu => ?_⟩
      have hmono : ∀ A : ℕ, A ≤ max Aa At →
          ∀ y : ℝ, y ≤ (A : ℝ) * δ → y ≤ ((max Aa At : ℕ) : ℝ) * δ := by
        intro A hA y hy
        refine hy.trans (mul_le_mul_of_nonneg_right ?_ hδ)
        exact_mod_cast hA
      rcases List.mem_cons.1 hu with rfl | hu'
      · exact hmono Aa (le_max_left _ _) _
          (hNa M δ hδ fun j hj => hrel j (hj.trans (le_max_left _ _)))
      · exact hmono At (le_max_right _ _) _
          (hNt M δ hδ (fun j hj => hrel j (hj.trans (le_max_right _ _))) u hu')

/-! ## Challenges and answers -/

/-- The word problem of an enumerated presentation code. -/
def EnumWordProblem (c : PresentationCode) (w : List (ℕ × Bool)) : Prop :=
  evalCode c w = 1

/-- The conditions a challenge asks a microstate for: the relators at the
first `N + 1` addresses are displaced by at most `1/(k+1)`, and every listed
word is displaced by at least `1/2`. -/
noncomputable def PassesN (c : PresentationCode) (W : List (List (ℕ × Bool)))
    (N k : ℕ) (M : NatMicrostate) : Prop :=
  (∀ j, j ≤ N → M.hlen (relatorAt c j) ≤ 1 / ((k : ℝ) + 1)) ∧
    (∀ w ∈ W, 1 / 2 ≤ M.len w)

/-- **One challenge, answered.**  Either the challenge is void because one of
its words is trivial in the coded group, or a microstate meets it. -/
noncomputable def AnswersN (c : PresentationCode) (W : List (List (ℕ × Bool)))
    (N k : ℕ) : Prop :=
  (∃ w ∈ W, EnumWordProblem c w) ∨ ∃ M : NatMicrostate, PassesN c W N k M

/-! ## Reading a microstate off a sofic model -/

section Forward

variable {c : PresentationCode} {F : Finset (Carrier c)} {ε : ℝ}

/-- The value at the identity is close to the identity. -/
theorem soficMap_one_le {G : Type} [Group G] {F : Finset G} {ε : ℝ}
    (SM : SoficModel G F ε) (h1 : (1 : G) ∈ F) :
    hammingDistance SM.carrier (SM.map 1) 1 ≤ ε := by
  have h := SM.multiplicative 1 h1 1 h1
  rw [mul_one] at h
  have hr := hammingDistance_right_invariant SM.carrier 1 (SM.map 1) (SM.map 1)
  rw [one_mul] at hr
  rw [hr] at h
  rwa [hammingDistance_comm]

/-- The value at an inverse is close to the inverse of the value. -/
theorem soficMap_inv_le {G : Type} [Group G] {F : Finset G} {ε : ℝ}
    (SM : SoficModel G F ε) (h1 : (1 : G) ∈ F) {g : G} (hg : g ∈ F)
    (hg' : g⁻¹ ∈ F) :
    hammingDistance SM.carrier (SM.map g⁻¹) (SM.map g)⁻¹ ≤ 2 * ε := by
  have h := SM.multiplicative g hg g⁻¹ hg'
  rw [mul_inv_cancel] at h
  have hone : hammingDistance SM.carrier 1 (SM.map 1) ≤ ε := by
    rw [hammingDistance_comm]
    exact soficMap_one_le SM h1
  have htri := hammingDistance_triangle SM.carrier 1 (SM.map 1)
    (SM.map g * SM.map g⁻¹)
  have hb : hammingDistance SM.carrier 1 (SM.map g * SM.map g⁻¹) ≤ 2 * ε := by
    linarith
  have hl := hammingDistance_left_invariant SM.carrier (SM.map g)⁻¹ 1
    (SM.map g * SM.map g⁻¹)
  have heq1 : (SM.map g)⁻¹ * 1 = (SM.map g)⁻¹ := mul_one _
  have heq2 : (SM.map g)⁻¹ * (SM.map g * SM.map g⁻¹) = SM.map g⁻¹ := by group
  rw [heq1, heq2] at hl
  rw [hammingDistance_comm, hl]
  exact hb

/-- The generator family a sofic model provides, truncated at a bound. -/
def truncGen (c : PresentationCode) {F : Finset (Carrier c)} {ε : ℝ}
    (SM : SoficModel (Carrier c) F ε) (b i : ℕ) : Equiv.Perm SM.carrier :=
  if i < b then SM.map (PresentedGroup.of i) else 1

theorem truncGen_of_lt (SM : SoficModel (Carrier c) F ε) {b i : ℕ} (hi : i < b) :
    truncGen c SM b i = SM.map (PresentedGroup.of i) := by
  rw [truncGen, if_pos hi]

/-- The microstate a sofic model determines, once a letter bound is chosen. -/
def modelMicrostate (c : PresentationCode) {F : Finset (Carrier c)} {ε : ℝ}
    (SM : SoficModel (Carrier c) F ε) (b : ℕ) : NatMicrostate where
  carrier := SM.carrier
  nonempty := SM.nonempty
  bound := b
  gen := truncGen c SM b
  gen_eq_one := fun i hi => by
    show (if i < b then SM.map (PresentedGroup.of i) else 1) = 1
    rw [if_neg (Nat.not_lt.2 hi)]

@[simp] theorem modelMicrostate_len (SM : SoficModel (Carrier c) F ε) (b : ℕ)
    (w : List (ℕ × Bool)) :
    (modelMicrostate c SM b).len w
      = hammingDistance SM.carrier (evalRaw (truncGen c SM b) w) 1 :=
  (modelMicrostate c SM b).len_def w

/-- The microstate's value on a one-letter word is within `2ε` of the model's,
provided the letter is below the bound. -/
theorem letter_gapN (SM : SoficModel (Carrier c) F ε) (b : ℕ) (hε : 0 ≤ ε)
    (h1 : (1 : Carrier c) ∈ F)
    (hgen : ∀ i, i < b → ∀ s : Bool, evalCode c [(i, s)] ∈ F)
    (p : ℕ × Bool) (hp : p.1 < b) :
    hammingDistance SM.carrier (SM.map (evalCode c [p]))
        (evalRaw (truncGen c SM b) [p]) ≤ 2 * ε := by
  obtain ⟨i, s⟩ := p
  have hi : i < b := hp
  cases s with
  | true =>
      rw [evalRaw_letter_pos, truncGen_of_lt SM hi, evalCode_letter_pos,
        hammingDistance_self]
      linarith
  | false =>
      have hgF : (PresentedGroup.of i : Carrier c) ∈ F := by
        have h := hgen i hi true
        rwa [evalCode_letter_pos] at h
      have hgF' : (PresentedGroup.of i : Carrier c)⁻¹ ∈ F := by
        have h := hgen i hi false
        rwa [evalCode_letter_neg] at h
      rw [evalRaw_letter_neg, truncGen_of_lt SM hi, evalCode_letter_neg]
      exact soficMap_inv_le SM h1 hgF hgF'

/-- **The word induction.**  Evaluating a raw word in the microstate and
evaluating it in the model differ by at most a multiple of the accuracy,
linear in the word's length. -/
theorem approxWordN (SM : SoficModel (Carrier c) F ε) (b : ℕ) (hε : 0 ≤ ε)
    (h1 : (1 : Carrier c) ∈ F)
    (hgen : ∀ i, i < b → ∀ s : Bool, evalCode c [(i, s)] ∈ F) :
    ∀ (u : List (ℕ × Bool)), (∀ p ∈ u, p.1 < b) →
      (∀ t ∈ u.tails, evalCode c t ∈ F) →
        hammingDistance SM.carrier (SM.map (evalCode c u))
          (evalRaw (truncGen c SM b) u) ≤ (3 * (u.length : ℝ) + 1) * ε
  | [], _, _ => by
      have hnil : evalCode c ([] : List (ℕ × Bool)) = 1 := rfl
      have hnil' : evalRaw (truncGen c SM b) ([] : List (ℕ × Bool)) = 1 := rfl
      rw [hnil, hnil']
      have h := soficMap_one_le SM h1
      simp only [List.length_nil, Nat.cast_zero, mul_zero, zero_add, one_mul]
      exact h
  | p :: t, hlet, hsuf => by
      have htail : ∀ s ∈ t.tails, evalCode c s ∈ F := by
        intro s hs
        exact hsuf s (by rw [List.tails_cons]; exact List.mem_cons_of_mem _ hs)
      have hlett : ∀ q ∈ t, q.1 < b := fun q hq =>
        hlet q (List.mem_cons_of_mem _ hq)
      have ih := approxWordN SM b hε h1 hgen t hlett htail
      have hpb : p.1 < b := hlet p List.mem_cons_self
      have hmemp : evalCode c [p] ∈ F := hgen p.1 hpb p.2
      have hmemt : evalCode c t ∈ F := hsuf t (by
        rw [List.tails_cons]
        exact List.mem_cons_of_mem _ (MFMicrostate.self_mem_tails t))
      have hevcons : evalCode c (p :: t) = evalCode c [p] * evalCode c t :=
        evalRaw_cons' _ p t
      have hgcons : evalRaw (truncGen c SM b) (p :: t)
          = evalRaw (truncGen c SM b) [p] * evalRaw (truncGen c SM b) t :=
        evalRaw_cons' _ p t
      have hfirst : hammingDistance SM.carrier (SM.map (evalCode c (p :: t)))
          (SM.map (evalCode c [p]) * SM.map (evalCode c t)) ≤ ε := by
        have h := SM.multiplicative (evalCode c [p]) hmemp (evalCode c t) hmemt
        rwa [← hevcons] at h
      have hsecond : hammingDistance SM.carrier
          (SM.map (evalCode c [p]) * SM.map (evalCode c t))
          (evalRaw (truncGen c SM b) [p] * SM.map (evalCode c t)) ≤ 2 * ε := by
        rw [hammingDistance_right_invariant]
        exact letter_gapN SM b hε h1 hgen p hpb
      have hthird : hammingDistance SM.carrier
          (evalRaw (truncGen c SM b) [p] * SM.map (evalCode c t))
          (evalRaw (truncGen c SM b) [p] * evalRaw (truncGen c SM b) t)
            ≤ (3 * (t.length : ℝ) + 1) * ε := by
        rw [hammingDistance_left_invariant]
        exact ih
      have htri1 := hammingDistance_triangle SM.carrier
        (SM.map (evalCode c (p :: t)))
        (SM.map (evalCode c [p]) * SM.map (evalCode c t))
        (evalRaw (truncGen c SM b) [p] * evalRaw (truncGen c SM b) t)
      have htri2 := hammingDistance_triangle SM.carrier
        (SM.map (evalCode c [p]) * SM.map (evalCode c t))
        (evalRaw (truncGen c SM b) [p] * SM.map (evalCode c t))
        (evalRaw (truncGen c SM b) [p] * evalRaw (truncGen c SM b) t)
      have hbound : hammingDistance SM.carrier (SM.map (evalCode c (p :: t)))
          (evalRaw (truncGen c SM b) (p :: t))
            ≤ ε + (2 * ε + (3 * (t.length : ℝ) + 1) * ε) := by
        rw [hgcons]
        linarith
      refine hbound.trans (le_of_eq ?_)
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      ring

end Forward

/-! ## The equivalence -/

/-- **Soficity of an enumerated coded group is exactly the assertion that
every challenge is answered.**

The right-hand side mentions the coded group only through `EnumWordProblem`,
a recursively enumerable predicate; the microstate disjunct mentions it not at
all. -/
theorem isSofic_iff_forall_answersN (c : PresentationCode) :
    IsSofic (Carrier c) ↔ ∀ W N k, AnswersN c W N k := by
  classical
  constructor
  · -- Forward: read a microstate off a sofic model of a large enough ball.
    intro hSofic W N k
    by_cases hvoid : ∃ w ∈ W, EnumWordProblem c w
    · exact Or.inl hvoid
    refine Or.inr ?_
    set relWords : List (List (ℕ × Bool)) :=
      (List.range (N + 1)).map (rawRelator c) with hrelW
    set allWords : List (List (ℕ × Bool)) := W ++ relWords with hall
    set L : ℕ := (allWords.map List.length).foldr max 0 with hL
    set B : ℕ := 3 * L + 3 with hB
    have hBpos : (0 : ℝ) < (B : ℝ) := by rw [hB]; positivity
    set m : ℝ := min (1 / 2) (1 / ((k : ℝ) + 1)) with hm
    have hmpos : 0 < m := by
      rw [hm]; refine lt_min (by norm_num) ?_; positivity
    set ε : ℝ := m / (B : ℝ) with hεdef
    have hεpos : 0 < ε := div_pos hmpos hBpos
    have hBε : (B : ℝ) * ε = m := by rw [hεdef]; field_simp
    set bnd : ℕ := (allWords.map letterBound).foldr max 0 with hbnd
    set sufs : List (List (ℕ × Bool)) := allWords.flatMap List.tails with hsufs
    set gens : List (List (ℕ × Bool)) :=
      (List.range bnd).flatMap fun i => [[(i, true)], [(i, false)]] with hgens
    set F : Finset (Carrier c) :=
      ((([] : List (ℕ × Bool)) :: (sufs ++ gens)).map (evalCode c)).toFinset
      with hF
    have hmemF : ∀ u ∈ ([] : List (ℕ × Bool)) :: (sufs ++ gens),
        evalCode c u ∈ F := by
      intro u hu
      rw [hF, List.mem_toFinset, List.mem_map]
      exact ⟨u, hu, rfl⟩
    have h1F : (1 : Carrier c) ∈ F := by
      have h := hmemF [] List.mem_cons_self
      exact h
    have hgenF : ∀ i, i < bnd → ∀ s : Bool, evalCode c [(i, s)] ∈ F := by
      intro i hi s
      refine hmemF _ (List.mem_cons_of_mem _ (List.mem_append_right _ ?_))
      rw [hgens, List.mem_flatMap]
      exact ⟨i, List.mem_range.2 hi, by cases s <;> simp⟩
    have hsufF : ∀ u ∈ allWords, ∀ t ∈ u.tails, evalCode c t ∈ F := by
      intro u hu t ht
      refine hmemF _ (List.mem_cons_of_mem _ (List.mem_append_left _ ?_))
      rw [hsufs, List.mem_flatMap]
      exact ⟨u, hu, ht⟩
    have hletF : ∀ u ∈ allWords, ∀ p ∈ u, p.1 < bnd := by
      intro u hu p hp
      have hb : letterBound u ≤ bnd := by
        rw [hbnd]; exact MFMicrostate.le_foldr_max letterBound allWords u hu
      exact lt_of_lt_of_le (lt_letterBound hp) hb
    obtain ⟨SM⟩ := hSofic F ε hεpos
    have hone := soficMap_one_le SM h1F
    refine ⟨modelMicrostate c SM bnd, ?_, ?_⟩
    · intro j hj
      have hrall : rawRelator c j ∈ allWords := by
        rw [hall]
        refine List.mem_append_right _ ?_
        rw [hrelW, List.mem_map]
        exact ⟨j, List.mem_range.2 (Nat.lt_succ_of_le hj), rfl⟩
      have htriv : evalCode c (rawRelator c j) = 1 :=
        (evalCode_eq_one_iff c (rawRelator c j)).2
          (Subgroup.subset_normalClosure (relatorAt_mem_relatorSet c j))
      have hgap := approxWordN SM bnd hεpos.le h1F hgenF (rawRelator c j)
        (hletF _ hrall) (hsufF _ hrall)
      rw [htriv] at hgap
      have htri := hammingDistance_triangle SM.carrier
        (evalRaw (truncGen c SM bnd) (rawRelator c j)) (SM.map 1) 1
      rw [hammingDistance_comm SM.carrier
        (evalRaw (truncGen c SM bnd) (rawRelator c j)) (SM.map 1)] at htri
      have hlen : (rawRelator c j).length ≤ L := by
        rw [hL]
        exact MFMicrostate.le_foldr_max List.length allWords _ hrall
      have hb : 3 * ((rawRelator c j).length : ℝ) + 2 ≤ (B : ℝ) := by
        have hLle : ((rawRelator c j).length : ℝ) ≤ (L : ℝ) := by
          exact_mod_cast hlen
        rw [hB]; push_cast; linarith
      have hcoef : ε + (3 * ((rawRelator c j).length : ℝ) + 1) * ε
          ≤ (B : ℝ) * ε := by
        calc ε + (3 * ((rawRelator c j).length : ℝ) + 1) * ε
            = (3 * ((rawRelator c j).length : ℝ) + 2) * ε := by ring
          _ ≤ (B : ℝ) * ε := mul_le_mul_of_nonneg_right hb hεpos.le
      have hfinal : (B : ℝ) * ε ≤ 1 / ((k : ℝ) + 1) := by
        rw [hBε, hm]; exact min_le_right _ _
      have hval : (modelMicrostate c SM bnd).hlen (relatorAt c j)
          = hammingDistance SM.carrier
              (evalRaw (truncGen c SM bnd) (rawRelator c j)) 1 :=
        (modelMicrostate c SM bnd).len_def (rawRelator c j)
      rw [hval]
      linarith
    · intro w hw
      have hwall : w ∈ allWords := by
        rw [hall]; exact List.mem_append_left _ hw
      have hne : evalCode c w ≠ 1 := fun hcon => hvoid ⟨w, hw, hcon⟩
      have hwF : evalCode c w ∈ F :=
        hsufF w hwall w (MFMicrostate.self_mem_tails w)
      have hgap := approxWordN SM bnd hεpos.le h1F hgenF w (hletF w hwall)
        (hsufF w hwall)
      have hsep : (1 : ℝ) - ε
          ≤ hammingDistance SM.carrier (SM.map (evalCode c w)) (SM.map 1) :=
        SM.separated (evalCode c w) hwF 1 h1F hne
      have htri1 := hammingDistance_triangle SM.carrier
        (SM.map (evalCode c w)) (evalRaw (truncGen c SM bnd) w) (SM.map 1)
      have htri2 := hammingDistance_triangle SM.carrier
        (evalRaw (truncGen c SM bnd) w) 1 (SM.map 1)
      have honesymm : hammingDistance SM.carrier 1 (SM.map 1) ≤ ε := by
        rw [hammingDistance_comm]; exact hone
      have hlen : w.length ≤ L := by
        rw [hL]; exact MFMicrostate.le_foldr_max List.length allWords w hwall
      have hb : 3 * (w.length : ℝ) + 3 ≤ (B : ℝ) := by
        have hLle : (w.length : ℝ) ≤ (L : ℝ) := by exact_mod_cast hlen
        rw [hB]; push_cast; linarith
      have hcoef : (3 * (w.length : ℝ) + 1) * ε + ε ≤ (B : ℝ) * ε - ε := by
        have hstep : (3 * (w.length : ℝ) + 3) * ε ≤ (B : ℝ) * ε :=
          mul_le_mul_of_nonneg_right hb hεpos.le
        nlinarith [hεpos.le]
      have hhalf : (B : ℝ) * ε ≤ 1 / 2 := by
        rw [hBε, hm]; exact min_le_left _ _
      rw [modelMicrostate_len]
      linarith
  · -- Backward: read a fixed-separation model off microstates, then amplify.
    intro h
    refine isSofic_of_isSoficWeak (δ := 1 / 2) (by norm_num) ?_
    intro F ε hε
    set wd : Carrier c → List (ℕ × Bool) :=
      Function.surjInv (evalCode_surjective c) with hwd
    have hwdspec : ∀ g : Carrier c, evalCode c (wd g) = g := fun g =>
      Function.surjInv_eq (evalCode_surjective c) g
    set pairs : Finset (Carrier c × Carrier c) :=
      (F ×ˢ F).filter fun q => q.1 ≠ q.2 with hpairs
    set W : List (List (ℕ × Bool)) :=
      pairs.toList.map fun q => invRaw (wd q.1) ++ wd q.2 with hW
    set mulWords : List (List (ℕ × Bool)) :=
      (F ×ˢ F).toList.map fun q =>
        invRaw (wd q.1 ++ wd q.2) ++ wd (q.1 * q.2) with hmul
    have hmultriv : ∀ u ∈ mulWords, evalCode c u = 1 := by
      intro u hu
      rw [hmul, List.mem_map] at hu
      obtain ⟨q, _hq, rfl⟩ := hu
      rw [evalCode_append, evalCode_invRaw, evalCode_append, hwdspec, hwdspec,
        hwdspec, inv_mul_cancel]
    obtain ⟨N, A, hNA⟩ := exists_area_bound_list c mulWords hmultriv
    obtain ⟨k, hk⟩ := exists_nat_gt ((A : ℝ) / ε)
    have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hAk : (A : ℝ) * (1 / ((k : ℝ) + 1)) ≤ ε := by
      have h1 : (A : ℝ) / ε < (k : ℝ) + 1 := by linarith
      have h2 : (A : ℝ) < ε * ((k : ℝ) + 1) := by
        have := (div_lt_iff₀ hε).1 h1
        linarith
      rw [mul_one_div]
      exact (div_le_iff₀ hkpos).2 (by linarith)
    rcases h W N k with hvoid | ⟨M, hrel, hsep⟩
    · exfalso
      obtain ⟨w, hw, hwtriv⟩ := hvoid
      rw [hW, List.mem_map] at hw
      obtain ⟨q, hq, rfl⟩ := hw
      rw [Finset.mem_toList, hpairs, Finset.mem_filter] at hq
      have hwt : evalCode c (invRaw (wd q.1) ++ wd q.2) = 1 := hwtriv
      rw [evalCode_append, evalCode_invRaw, hwdspec, hwdspec,
        inv_mul_eq_one] at hwt
      exact hq.2 hwt
    refine ⟨{
      carrier := M.carrier
      nonempty := M.nonempty
      map := fun g => evalRaw M.gen (wd g)
      multiplicative := ?_
      separated := ?_ }⟩
    · intro g hg h' hh'
      have hmemword :
          (invRaw (wd g ++ wd h') ++ wd (g * h')) ∈ mulWords := by
        rw [hmul, List.mem_map]
        refine ⟨(g, h'), ?_, rfl⟩
        rw [Finset.mem_toList, Finset.mem_product]
        exact ⟨hg, hh'⟩
      have hval : M.len (invRaw (wd g ++ wd h') ++ wd (g * h'))
          = hammingDistance M.carrier (evalRaw M.gen (wd (g * h')))
              (evalRaw M.gen (wd g) * evalRaw M.gen (wd h')) := by
        rw [M.len_def, evalRaw_append, evalRaw_invRaw, evalRaw_append,
          ← SoficMicrostateNormalForm.hammingDistance_eq_displacement]
      have hbound := hNA M (1 / ((k : ℝ) + 1)) (by positivity) hrel _ hmemword
      rw [hval] at hbound
      exact hbound.trans hAk
    · intro g hg h' hh' hne
      have hmemword : (invRaw (wd h') ++ wd g) ∈ W := by
        rw [hW, List.mem_map]
        refine ⟨(h', g), ?_, rfl⟩
        rw [Finset.mem_toList, hpairs, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hh', hg⟩, Ne.symm hne⟩
      have hval : M.len (invRaw (wd h') ++ wd g)
          = hammingDistance M.carrier (evalRaw M.gen (wd g))
              (evalRaw M.gen (wd h')) := by
        rw [M.len_def, evalRaw_append, evalRaw_invRaw,
          ← SoficMicrostateNormalForm.hammingDistance_eq_displacement]
      have hbound := hsep _ hmemword
      rw [hval] at hbound
      exact hbound

/-! ## Certificates

Everything numerical below --- table composition, the identity table, moved
points, the two cleared-denominator comparisons --- is
`Computability.SoficRecognitionPi02`'s, which never mentions a presentation
code.  What is new is the *validating* lookup: an entry that is out of range,
or whose two tables fail to be mutually inverse, is silently replaced by the
identity pair, so that every raw certificate names an honest microstate whose
generators are eventually the identity. -/

/-- The raw table pair a certificate stores at a letter. -/
def certEntry (cert : PermCert) (i : ℕ) : List ℕ × List ℕ :=
  cert.2.getD i ([], [])

/-- Well-formedness of one stored entry, as a Boolean test. -/
def certOkN (cert : PermCert) (i : ℕ) : Bool :=
  (decide (i < cert.2.length) &&
      decide (compTable cert.1 (certEntry cert i).1 (certEntry cert i).2
        = idTable cert.1)) &&
    decide (compTable cert.1 (certEntry cert i).2 (certEntry cert i).1
      = idTable cert.1)

/-- **The validating lookup.**  A stored entry is used only if it is a genuine
mutually inverse pair; otherwise the identity pair is used. -/
def certGenN (cert : PermCert) (i : ℕ) : List ℕ × List ℕ :=
  bif certOkN cert i then certEntry cert i else (idTable cert.1, idTable cert.1)

theorem compTable_idTable_self (m : ℕ) :
    compTable m (idTable m) (idTable m) = idTable m := by
  have h : ∀ x, x < m + 1 → act m (idTable m) (act m (idTable m) x) = x := by
    intro x hx
    rw [act_idTable m x hx, act_idTable m x hx]
  exact (map_range_eq_range_iff (m + 1)
    (fun x => act m (idTable m) (act m (idTable m) x))).2 h

theorem inverseTables_idTable (m : ℕ) :
    InverseTables m (idTable m) (idTable m) :=
  ⟨compTable_idTable_self m, compTable_idTable_self m⟩

theorem certGenN_eq_entry (cert : PermCert) {i : ℕ} (h : certOkN cert i = true) :
    certGenN cert i = certEntry cert i := by
  show (bif certOkN cert i then certEntry cert i
    else (idTable cert.1, idTable cert.1)) = _
  rw [h]
  rfl

theorem certGenN_eq_id (cert : PermCert) {i : ℕ} (h : certOkN cert i = false) :
    certGenN cert i = (idTable cert.1, idTable cert.1) := by
  show (bif certOkN cert i then certEntry cert i
    else (idTable cert.1, idTable cert.1)) = _
  rw [h]
  rfl

theorem certOkN_eq_true (cert : PermCert) {i : ℕ} (hi : i < cert.2.length)
    (h : InverseTables cert.1 (certEntry cert i).1 (certEntry cert i).2) :
    certOkN cert i = true := by
  simp only [certOkN, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hi, h.1⟩, h.2⟩

theorem certOkN_eq_false (cert : PermCert) {i : ℕ} (hi : cert.2.length ≤ i) :
    certOkN cert i = false := by
  have hlt : decide (i < cert.2.length) = false :=
    decide_eq_false (Nat.not_lt.2 hi)
  simp [certOkN, hlt]

theorem certGenN_of_le (cert : PermCert) {i : ℕ} (hi : cert.2.length ≤ i) :
    certGenN cert i = (idTable cert.1, idTable cert.1) :=
  certGenN_eq_id cert (certOkN_eq_false cert hi)

theorem inverseTables_certGenN (cert : PermCert) (i : ℕ) :
    InverseTables cert.1 (certGenN cert i).1 (certGenN cert i).2 := by
  cases h : certOkN cert i with
  | false =>
      rw [certGenN_eq_id cert h]
      exact inverseTables_idTable cert.1
  | true =>
      rw [certGenN_eq_entry cert h]
      simp only [certOkN, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1.2, h.2⟩

/-- The permutation a certificate names at a letter. -/
def certGenPermN (cert : PermCert) (i : ℕ) : Equiv.Perm (natModel cert.1) :=
  toPerm cert.1 (certGenN cert i).1 (certGenN cert i).2
    (inverseTables_certGenN cert i)

theorem certGenPermN_val (cert : PermCert) (i : ℕ) (x : Fin (cert.1 + 1)) :
    ((certGenPermN cert i) x).val = act cert.1 (certGenN cert i).1 x.val := rfl

theorem certGenPermN_inv_val (cert : PermCert) (i : ℕ) (x : Fin (cert.1 + 1)) :
    (((certGenPermN cert i)⁻¹) x).val
      = act cert.1 (certGenN cert i).2 x.val := rfl

theorem certGenPermN_eq_one (cert : PermCert) {i : ℕ}
    (hi : cert.2.length ≤ i) : certGenPermN cert i = 1 := by
  refine Equiv.ext fun x => Fin.val_injective ?_
  show act cert.1 (certGenN cert i).1 x.val = x.val
  rw [certGenN_of_le cert hi]
  exact act_idTable cert.1 x.val x.isLt

/-- The microstate a certificate names. -/
def certMicrostate (cert : PermCert) : NatMicrostate where
  carrier := natModel cert.1
  nonempty := by rw [card_natModel]; exact Nat.succ_pos _
  bound := cert.2.length
  gen := certGenPermN cert
  gen_eq_one := fun _ hi => certGenPermN_eq_one cert hi

/-- The table of one signed letter. -/
def letterTableN (cert : PermCert) (p : ℕ × Bool) : List ℕ :=
  bif p.2 then (certGenN cert p.1).1 else (certGenN cert p.1).2

/-- The table of a raw word. -/
def wordTableN (cert : PermCert) (w : List (ℕ × Bool)) : List ℕ :=
  w.foldr (fun p acc => compTable cert.1 (letterTableN cert p) acc)
    (idTable cert.1)

@[simp] theorem wordTableN_nil (cert : PermCert) :
    wordTableN cert [] = idTable cert.1 := rfl

@[simp] theorem wordTableN_cons (cert : PermCert) (p : ℕ × Bool)
    (w : List (ℕ × Bool)) :
    wordTableN cert (p :: w)
      = compTable cert.1 (letterTableN cert p) (wordTableN cert w) := rfl

theorem act_letterTableN (cert : PermCert) (p : ℕ × Bool)
    (x : Fin (cert.1 + 1)) :
    act cert.1 (letterTableN cert p) x.val
      = (((if p.2 then certGenPermN cert p.1
            else (certGenPermN cert p.1)⁻¹)) x).val := by
  obtain ⟨i, s⟩ := p
  cases s
  · rfl
  · rfl

theorem act_wordTableN (cert : PermCert) :
    ∀ (w : List (ℕ × Bool)) (x : Fin (cert.1 + 1)),
      act cert.1 (wordTableN cert w) x.val
        = ((evalRaw (certGenPermN cert) w) x).val
  | [], x => by
      rw [wordTableN_nil]
      have h : evalRaw (certGenPermN cert) ([] : List (ℕ × Bool)) = 1 := rfl
      rw [h]
      exact act_idTable cert.1 x.val x.isLt
  | p :: w, x => by
      obtain ⟨i, s⟩ := p
      rw [wordTableN_cons, act_compTable cert.1 _ _ x.isLt,
        act_wordTableN cert w x, evalRaw_cons' _ (i, s) w,
        Equiv.Perm.mul_apply, evalRaw_letter]
      exact act_letterTableN cert (i, s) _

/-- **The certificate computes the displacement exactly.** -/
theorem len_certMicrostate (cert : PermCert) (w : List (ℕ × Bool)) :
    (certMicrostate cert).len w
      = (movedCount cert.1 (wordTableN cert w) : ℝ) / ((cert.1 : ℝ) + 1) := by
  rw [(certMicrostate cert).len_def]
  exact hammingDistance_eq_movedCount cert.1
    (evalRaw (certGenPermN cert) w) (wordTableN cert w)
    fun i => (act_wordTableN cert w i).symm

/-! ## The certificate read off a microstate -/

/-- The certificate assembled from a family of permutations of `{0, …, m}`
that is the identity past a bound. -/
def certOfN (m b : ℕ) (g : ℕ → Equiv.Perm (natModel m)) : PermCert :=
  (m, (List.range b).map fun i => (tabOf m (g i), tabOf m (g i)⁻¹))

theorem certOfN_length (m b : ℕ) (g : ℕ → Equiv.Perm (natModel m)) :
    (certOfN m b g).2.length = b := by
  rw [certOfN]
  simp

theorem certEntry_certOfN (m b : ℕ) (g : ℕ → Equiv.Perm (natModel m)) {i : ℕ}
    (hi : i < b) :
    certEntry (certOfN m b g) i = (tabOf m (g i), tabOf m (g i)⁻¹) := by
  rw [certEntry, certOfN]
  exact getD_map_range b _ _ hi

theorem certGenPermN_certOfN (m b : ℕ) (g : ℕ → Equiv.Perm (natModel m))
    (hg : ∀ i, b ≤ i → g i = 1) (i : ℕ) :
    certGenPermN (certOfN m b g) i = g i := by
  by_cases hi : i < b
  · have hentry := certEntry_certOfN m b g hi
    have hok : certOkN (certOfN m b g) i = true := by
      refine certOkN_eq_true (certOfN m b g) ?_ ?_
      · rw [certOfN_length]; exact hi
      · rw [hentry]; exact inverseTables_tabOf m (g i)
    refine Equiv.ext fun x => Fin.val_injective ?_
    show act (certOfN m b g).1 (certGenN (certOfN m b g) i).1 x.val = (g i x).val
    rw [certGenN_eq_entry _ hok, hentry]
    exact act_tabOf m (g i) x
  · have hle : b ≤ i := Nat.not_lt.1 hi
    rw [certGenPermN_eq_one _ (by rw [certOfN_length]; exact hle), hg i hle]
    rfl

/-- Displacement is invariant under transporting a microstate along a
bijection of models.  Stated with the target model as a variable, so that no
projection of a certificate has to be unfolded inside a type. -/
theorem len_eq_of_permCongr (M : NatMicrostate) {Y : FiniteModel}
    (e : M.carrier ≃ Y) (g : ℕ → Equiv.Perm Y)
    (hg : ∀ i, g i = permCongrHom e (M.gen i)) (w : List (ℕ × Bool)) :
    hammingDistance Y (evalRaw g w) 1 = M.len w := by
  rw [M.len_def]
  have hfun : g = fun i => permCongrHom e (M.gen i) := funext hg
  have hcong : evalRaw g w = permCongrHom e (evalRaw M.gen w) := by
    rw [hfun]
    exact (map_evalRaw (permCongrHom e) M.gen w).symm
  rw [hcong, show (1 : Equiv.Perm Y) = permCongrHom e 1 from
    (map_one (permCongrHom e)).symm, hammingDistance_permCongrHom]

/-- The certificate's microstate, with its carrier and generators named. -/
theorem len_certMicrostate' (cert : PermCert) (w : List (ℕ × Bool)) :
    (certMicrostate cert).len w
      = hammingDistance (natModel cert.1)
          (evalRaw (certGenPermN cert) w) 1 :=
  (certMicrostate cert).len_def w

/-- **Every microstate is named by a certificate.**  Transport the microstate
to `{0, …, m}` along a cardinality equivalence, and read the tables off. -/
theorem exists_cert_len (M : NatMicrostate) :
    ∃ cert : PermCert, ∀ w : List (ℕ × Bool),
      (certMicrostate cert).len w = M.len w := by
  classical
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Fintype.card M.carrier = m + 1 := by
    have hpos := M.nonempty
    exact ⟨Fintype.card M.carrier - 1, by omega⟩
  have e : M.carrier ≃ Fin (m + 1) := Fintype.equivFinOfCardEq hm
  have hgone : ∀ i, M.bound ≤ i → permCongrHom e (M.gen i) = 1 := by
    intro i hi
    rw [M.gen_eq_one i hi, map_one]
  refine ⟨certOfN m M.bound fun i => permCongrHom e (M.gen i), fun w => ?_⟩
  refine Eq.trans (len_certMicrostate' _ w) ?_
  exact len_eq_of_permCongr M e _
    (certGenPermN_certOfN m M.bound _ hgone) w

/-! ## The microstate disjunct is a certificate search -/

/-- The relator clause, as a Boolean test. -/
def relatorOkN (c : PresentationCode) (cert : PermCert) (k j : ℕ) : Bool :=
  decide (movedCount cert.1 (wordTableN cert (rawRelator c j)) * (k + 1)
    ≤ cert.1 + 1)

/-- The separation clause, as a Boolean test. -/
def wordOkN (cert : PermCert) (w : List (ℕ × Bool)) : Bool :=
  decide (cert.1 + 1 ≤ 2 * movedCount cert.1 (wordTableN cert w))

/-- The checker input: a code together with a challenge `(W, N, k)`. -/
abbrev CheckInputN : Type := PresentationCode × (List (List (ℕ × Bool)) × ℕ × ℕ)

/-- **The certificate checker.**  Every clause is a comparison of naturals, so
this is a total Boolean function of raw data. -/
def passesCheckN (x : CheckInputN) (cert : PermCert) : Bool :=
  decide ((List.range (x.2.2.1 + 1)).map (relatorOkN x.1 cert x.2.2.2)
      = (List.range (x.2.2.1 + 1)).map fun _ => true) &&
    decide (x.2.1.map (wordOkN cert) = x.2.1.map fun _ => true)

theorem passesCheckN_eq_true_iff (x : CheckInputN) (cert : PermCert) :
    passesCheckN x cert = true ↔
      ((∀ j, j ≤ x.2.2.1 →
          movedCount cert.1 (wordTableN cert (rawRelator x.1 j))
            * (x.2.2.2 + 1) ≤ cert.1 + 1) ∧
        ∀ w ∈ x.2.1,
          cert.1 + 1 ≤ 2 * movedCount cert.1 (wordTableN cert w)) := by
  rw [passesCheckN, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff,
    map_eq_map_iff, map_eq_map_iff]
  constructor
  · rintro ⟨hr, hw⟩
    refine ⟨fun j hj => ?_, fun w hwmem => ?_⟩
    · have h := hr j (List.mem_range.2 (Nat.lt_succ_of_le hj))
      rwa [relatorOkN, decide_eq_true_iff] at h
    · have h := hw w hwmem
      rwa [wordOkN, decide_eq_true_iff] at h
  · rintro ⟨hr, hw⟩
    refine ⟨fun j hj => ?_, fun w hwmem => ?_⟩
    · rw [relatorOkN, decide_eq_true_iff]
      exact hr j (Nat.lt_succ_iff.1 (List.mem_range.1 hj))
    · rw [wordOkN, decide_eq_true_iff]
      exact hw w hwmem

/-- **The microstate disjunct is a certificate search.** -/
theorem passesN_iff_exists_check (c : PresentationCode)
    (W : List (List (ℕ × Bool))) (N k : ℕ) :
    (∃ M : NatMicrostate, PassesN c W N k M)
      ↔ ∃ cert : PermCert, passesCheckN (c, W, N, k) cert = true := by
  constructor
  · rintro ⟨M, hrel, hsep⟩
    obtain ⟨cert, hlen⟩ := exists_cert_len M
    refine ⟨cert, (passesCheckN_eq_true_iff (c, W, N, k) cert).2 ⟨?_, ?_⟩⟩
    · intro j hj
      have h := hrel j hj
      have hval : M.hlen (relatorAt c j) = M.len (rawRelator c j) := rfl
      rw [hval, ← hlen, len_certMicrostate] at h
      exact div_le_div_iff_nat.1 h
    · intro w hw
      have h := hsep w hw
      rw [← hlen, len_certMicrostate] at h
      exact half_le_div_iff_nat.1 h
  · rintro ⟨cert, hcheck⟩
    obtain ⟨hrel, hsep⟩ := (passesCheckN_eq_true_iff (c, W, N, k) cert).1 hcheck
    refine ⟨certMicrostate cert, fun j hj => ?_, fun w hw => ?_⟩
    · have hval : (certMicrostate cert).hlen (relatorAt c j)
          = (certMicrostate cert).len (rawRelator c j) := rfl
      rw [hval, len_certMicrostate]
      exact div_le_div_iff_nat.2 (hrel j hj)
    · rw [len_certMicrostate]
      exact half_le_div_iff_nat.2 (hsep w hw)

/-! ## The checker is primitive recursive -/

section Effective

variable {α : Type} [Primcodable α]

theorem primrec_certEntry {fcert : α → PermCert} {fi : α → ℕ}
    (hcert : Primrec fcert) (hi : Primrec fi) :
    Primrec fun a => certEntry (fcert a) (fi a) :=
  ((Primrec.list_getD (([], []) : List ℕ × List ℕ)).comp
    (Primrec.snd.comp hcert) hi).of_eq fun _ => rfl

theorem primrec_certOkN {fcert : α → PermCert} {fi : α → ℕ}
    (hcert : Primrec fcert) (hi : Primrec fi) :
    Primrec fun a => certOkN (fcert a) (fi a) := by
  have hm : Primrec fun a : α => (fcert a).1 := Primrec.fst.comp hcert
  have he := primrec_certEntry hcert hi
  have hid : Primrec fun a : α => idTable (fcert a).1 := primrec_idTable hm
  have hlt : Primrec fun a : α => decide (fi a < (fcert a).2.length) :=
    (Primrec.nat_lt.comp hi
      (Primrec.list_length.comp (Primrec.snd.comp hcert))).decide
  have h1 : Primrec fun a : α =>
      decide (compTable (fcert a).1 (certEntry (fcert a) (fi a)).1
        (certEntry (fcert a) (fi a)).2 = idTable (fcert a).1) :=
    (Primrec.eq.comp
      (primrec_compTable hm (Primrec.fst.comp he) (Primrec.snd.comp he))
      hid).decide
  have h2 : Primrec fun a : α =>
      decide (compTable (fcert a).1 (certEntry (fcert a) (fi a)).2
        (certEntry (fcert a) (fi a)).1 = idTable (fcert a).1) :=
    (Primrec.eq.comp
      (primrec_compTable hm (Primrec.snd.comp he) (Primrec.fst.comp he))
      hid).decide
  exact (Primrec.and.comp (Primrec.and.comp hlt h1) h2).of_eq fun _ => rfl

theorem primrec_certGenN {fcert : α → PermCert} {fi : α → ℕ}
    (hcert : Primrec fcert) (hi : Primrec fi) :
    Primrec fun a => certGenN (fcert a) (fi a) := by
  have hm : Primrec fun a : α => (fcert a).1 := Primrec.fst.comp hcert
  have hid : Primrec fun a : α => idTable (fcert a).1 := primrec_idTable hm
  exact (Primrec.cond (primrec_certOkN hcert hi) (primrec_certEntry hcert hi)
    (Primrec.pair hid hid)).of_eq fun _ => rfl

theorem primrec_letterTableN {fcert : α → PermCert} {fp : α → ℕ × Bool}
    (hcert : Primrec fcert) (hp : Primrec fp) :
    Primrec fun a => letterTableN (fcert a) (fp a) :=
  (Primrec.cond (Primrec.snd.comp hp)
    (Primrec.fst.comp (primrec_certGenN hcert (Primrec.fst.comp hp)))
    (Primrec.snd.comp
      (primrec_certGenN hcert (Primrec.fst.comp hp)))).of_eq fun _ => rfl

theorem primrec_wordTableN {fcert : α → PermCert}
    {fw : α → List (ℕ × Bool)} (hcert : Primrec fcert) (hw : Primrec fw) :
    Primrec fun a => wordTableN (fcert a) (fw a) := by
  have hstep : Primrec₂ fun (a : α) (z : (ℕ × Bool) × List ℕ) =>
      compTable (fcert a).1 (letterTableN (fcert a) z.1) z.2 :=
    (primrec_compTable (Primrec.fst.comp (hcert.comp Primrec.fst))
      (primrec_letterTableN (hcert.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_foldr hw
    (primrec_idTable (Primrec.fst.comp hcert)) hstep).of_eq fun _ => rfl

theorem primrec_relatorOkN {fc : α → PresentationCode} {fcert : α → PermCert}
    {fk fj : α → ℕ} (hc : Primrec fc) (hcert : Primrec fcert)
    (hk : Primrec fk) (hj : Primrec fj) :
    Primrec fun a => relatorOkN (fc a) (fcert a) (fk a) (fj a) := by
  have hrel : Primrec fun a : α => rawRelator (fc a) (fj a) :=
    primrec_rawRelator.comp hc hj
  have hcount : Primrec fun a : α =>
      movedCount (fcert a).1 (wordTableN (fcert a) (rawRelator (fc a) (fj a))) :=
    primrec_movedCount (Primrec.fst.comp hcert) (primrec_wordTableN hcert hrel)
  have hleft : Primrec fun a : α =>
      movedCount (fcert a).1 (wordTableN (fcert a) (rawRelator (fc a) (fj a)))
        * (fk a + 1) :=
    Primrec.nat_mul.comp hcount (Primrec.succ.comp hk)
  have hright : Primrec fun a : α => (fcert a).1 + 1 :=
    Primrec.succ.comp (Primrec.fst.comp hcert)
  exact (Primrec.nat_le.comp hleft hright).decide.of_eq fun _ => rfl

theorem primrec_wordOkN {fcert : α → PermCert} {fw : α → List (ℕ × Bool)}
    (hcert : Primrec fcert) (hw : Primrec fw) :
    Primrec fun a => wordOkN (fcert a) (fw a) := by
  have hcount : Primrec fun a : α =>
      movedCount (fcert a).1 (wordTableN (fcert a) (fw a)) :=
    primrec_movedCount (Primrec.fst.comp hcert) (primrec_wordTableN hcert hw)
  have hright : Primrec fun a : α =>
      2 * movedCount (fcert a).1 (wordTableN (fcert a) (fw a)) :=
    Primrec.nat_mul.comp (Primrec.const 2) hcount
  have hleft : Primrec fun a : α => (fcert a).1 + 1 :=
    Primrec.succ.comp (Primrec.fst.comp hcert)
  exact (Primrec.nat_le.comp hleft hright).decide.of_eq fun _ => rfl

end Effective

theorem primrec_passesCheckN : Primrec₂ passesCheckN := by
  have hc : Primrec fun z : CheckInputN × PermCert => z.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hW : Primrec fun z : CheckInputN × PermCert => z.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hN : Primrec fun z : CheckInputN × PermCert => z.1.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hk : Primrec fun z : CheckInputN × PermCert => z.1.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hcert : Primrec fun z : CheckInputN × PermCert => z.2 := Primrec.snd
  have hrange : Primrec fun z : CheckInputN × PermCert =>
      List.range (z.1.2.2.1 + 1) :=
    Primrec.list_range.comp (Primrec.succ.comp hN)
  have hrelList : Primrec fun z : CheckInputN × PermCert =>
      (List.range (z.1.2.2.1 + 1)).map (relatorOkN z.1.1 z.2 z.1.2.2.2) :=
    Primrec.list_map hrange
      (primrec_relatorOkN (hc.comp Primrec.fst) (hcert.comp Primrec.fst)
        (hk.comp Primrec.fst) Primrec.snd).to₂
  have hwordList : Primrec fun z : CheckInputN × PermCert =>
      z.1.2.1.map (wordOkN z.2) :=
    Primrec.list_map hW
      (primrec_wordOkN (hcert.comp Primrec.fst) Primrec.snd).to₂
  have htrueRange : Primrec fun z : CheckInputN × PermCert =>
      (List.range (z.1.2.2.1 + 1)).map fun _ : ℕ => true :=
    Primrec.list_map hrange (Primrec.const true).to₂
  have htrueWord : Primrec fun z : CheckInputN × PermCert =>
      z.1.2.1.map fun _ : List (ℕ × Bool) => true :=
    Primrec.list_map hW (Primrec.const true).to₂
  exact (Primrec.and.comp (Primrec.eq.comp hrelList htrueRange).decide
    (Primrec.eq.comp hwordList htrueWord).decide).of_eq fun _ => rfl

/-! ## Answering a challenge is recursively enumerable -/

/-- The search space for one challenge: a raw word together with a
word-problem certificate for the void disjunct, paired with a permutation
certificate for the microstate disjunct. -/
abbrev AnswerDataN : Type := (List (ℕ × Bool) × WordCertificate) × PermCert

/-- The matrix of the answer search. -/
def answerCheckN (x : CheckInputN) (b : AnswerDataN) : Bool :=
  (decide (b.1.1 ∈ x.2.1) && wordCheck (x.1, b.1.1) b.1.2) || passesCheckN x b.2

theorem exists_voidN_iff (c : PresentationCode) (W : List (List (ℕ × Bool))) :
    (∃ y : List (ℕ × Bool) × WordCertificate,
        (decide (y.1 ∈ W) && wordCheck (c, y.1) y.2) = true)
      ↔ ∃ w ∈ W, EnumWordProblem c w := by
  constructor
  · rintro ⟨⟨w, p⟩, hb⟩
    rw [Bool.and_eq_true, decide_eq_true_iff] at hb
    exact ⟨w, hb.1, (wordCheck_complete c w).2 ⟨p, hb.2⟩⟩
  · rintro ⟨w, hw, htriv⟩
    obtain ⟨p, hp⟩ := (wordCheck_complete c w).1 htriv
    exact ⟨(w, p), by rw [Bool.and_eq_true, decide_eq_true_iff]; exact ⟨hw, hp⟩⟩

theorem answerCheckN_iff (x : CheckInputN) :
    (∃ b : AnswerDataN, answerCheckN x b = true)
      ↔ AnswersN x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  constructor
  · rintro ⟨⟨⟨w, p⟩, cert⟩, hb⟩
    rw [answerCheckN, Bool.or_eq_true] at hb
    rcases hb with h | h
    · exact Or.inl ((exists_voidN_iff x.1 x.2.1).1 ⟨(w, p), h⟩)
    · refine Or.inr ((passesN_iff_exists_check x.1 x.2.1 x.2.2.1 x.2.2.2).2
        ⟨cert, ?_⟩)
      exact h
  · intro hAns
    rcases hAns with hvoid | hM
    · obtain ⟨⟨w, p⟩, h⟩ := (exists_voidN_iff x.1 x.2.1).2 hvoid
      exact ⟨((w, p), default), by
        rw [answerCheckN, Bool.or_eq_true]; exact Or.inl h⟩
    · obtain ⟨cert, h⟩ :=
        (passesN_iff_exists_check x.1 x.2.1 x.2.2.1 x.2.2.2).1 hM
      exact ⟨((default, default), cert), by
        rw [answerCheckN, Bool.or_eq_true]; exact Or.inr h⟩

theorem primrec_answerCheckN : Primrec₂ answerCheckN := by
  have hmem : PrimrecPred fun z : CheckInputN × AnswerDataN =>
      z.2.1.1 ∈ z.1.2.1 := by
    have h : PrimrecRel fun (L : List (List (ℕ × Bool)))
        (u : List (ℕ × Bool)) => ∃ a ∈ L, a = u :=
      PrimrecRel.exists_mem_list Primrec.eq
    refine (h.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))).of_eq fun z => ?_
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hz
      exact ⟨z.2.1.1, hz, rfl⟩
  have hsearch : Primrec fun z : CheckInputN × AnswerDataN =>
      wordCheck (z.1.1, z.2.1.1) z.2.1.2 :=
    primrec_wordCheck.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
  have hpass : Primrec fun z : CheckInputN × AnswerDataN =>
      passesCheckN z.1 z.2.2 :=
    primrec_passesCheckN.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  exact (Primrec.or.comp (Primrec.and.comp hmem.decide hsearch) hpass).of_eq
    fun _ => rfl

/-- **Answering one challenge is recursively enumerable.** -/
theorem rePred_answersN :
    REPred fun x : PresentationCode × (List (List (ℕ × Bool)) × ℕ × ℕ) =>
      AnswersN x.1 x.2.1 x.2.2.1 x.2.2.2 :=
  (WordProblemRE.rePred_exists_eq_true primrec_answerCheckN.to_comp).of_eq
    answerCheckN_iff

/-! ## The arithmetical bounds -/

/-- The challenge named by a scale index.  Surjectivity onto all challenges is
what makes `∀ n` equivalent to `∀ W N k`. -/
def decodeChallengeN (n : ℕ) : List (List (ℕ × Bool)) × ℕ × ℕ :=
  (Encodable.decode (α := List (List (ℕ × Bool)) × ℕ × ℕ) n).getD ([], 0, 0)

theorem primrec_decodeChallengeN : Primrec decodeChallengeN :=
  (Primrec.option_getD.comp Primrec.decode
    (Primrec.const (([], 0, 0) : List (List (ℕ × Bool)) × ℕ × ℕ))).of_eq
    fun _ => rfl

theorem decodeChallengeN_surjective (q : List (List (ℕ × Bool)) × ℕ × ℕ) :
    decodeChallengeN (Encodable.encode q) = q := by
  simp [decodeChallengeN]

-- Sealing the decoder keeps the arithmetical bookkeeping cheap: `Encodable`
-- decoding at a product type runs through `Nat.unpair`, whose well-founded
-- recursion the kernel will happily try to evaluate on an open term.  Nothing
-- below needs to look inside it, only `decodeChallengeN_surjective`.
attribute [irreducible] decodeChallengeN

/-- **Recognising soficity from a recursively enumerated presentation code is
`Π⁰₂`.** -/
theorem pi02_isSofic_enum :
    Pi02 fun c : PresentationCode => IsSofic (Carrier c) := by
  refine ⟨fun z : PresentationCode × ℕ =>
    AnswersN z.1 (decodeChallengeN z.2).1 (decodeChallengeN z.2).2.1
      (decodeChallengeN z.2).2.2, ?_, ?_⟩
  · have hmap : Computable fun z : PresentationCode × ℕ =>
        (z.1, decodeChallengeN z.2) :=
      (Primrec.pair Primrec.fst
        (primrec_decodeChallengeN.comp Primrec.snd)).to_comp
    exact rePred_answersN.comp hmap
  · intro c
    refine Iff.trans (isSofic_iff_forall_answersN c) ?_
    constructor
    · intro h n
      exact h (decodeChallengeN n).1 (decodeChallengeN n).2.1
        (decodeChallengeN n).2.2
    · intro h W N k
      have hn : AnswersN c (decodeChallengeN (Encodable.encode (W, N, k))).1
          (decodeChallengeN (Encodable.encode (W, N, k))).2.1
          (decodeChallengeN (Encodable.encode (W, N, k))).2.2 :=
        h (Encodable.encode (W, N, k))
      rw [decodeChallengeN_surjective (W, N, k)] at hn
      exact hn

/-- **Recognising non-soficity from a recursively enumerated presentation code
is `Σ⁰₂`.** -/
theorem sigma02_not_isSofic_enum :
    Sigma02 fun c : PresentationCode => ¬ IsSofic (Carrier c) :=
  (sigma02_compl_iff _).2 pi02_isSofic_enum

/-! ## The exact classification

The upper bound above and the hardness of
`Computability.SoficRecognitionSecondLevel` are statements about the *same*
domain --- standard recursively enumerated presentation codes --- so they
pair.  Both carry no hypothesis: hardness routes through
`Endpoint.MainResults.exists_finitelyPresented_nonsofic_group`, which is an
unconditional theorem of this repository, and the upper bound is proved above
from the definition of soficity alone.

This is, to this development's knowledge, the first exact arithmetical
classification of a group approximation property to be checked by a proof
assistant's kernel. -/

/-- **Soficity of a recursively enumerated presentation is `Π⁰₂`-complete.**
No hypothesis, no construction datum. -/
theorem sofic_enum_pi02Complete :
    Pi02Complete fun c : EnumeratedPresentationCodes.PresentationCode =>
      IsSofic (EnumeratedPresentationCodes.Carrier c) :=
  ⟨pi02_isSofic_enum, SoficRecognitionSecondLevel.soficCode_pi02Hard⟩

/-- **Non-soficity of a recursively enumerated presentation is
`Σ⁰₂`-complete.** -/
theorem nonsofic_enum_sigma02Complete :
    Sigma02Complete fun c : EnumeratedPresentationCodes.PresentationCode =>
      ¬ IsSofic (EnumeratedPresentationCodes.Carrier c) :=
  pi02Complete_compl sofic_enum_pi02Complete

/-! ## The closed form -/

/-- **The exact arithmetical classification of soficity on enumerated
presentations**, as a closed proposition. -/
def SoficEnumeratedExactClassification : Prop :=
  Pi02Complete (fun c : EnumeratedPresentationCodes.PresentationCode =>
      IsSofic (EnumeratedPresentationCodes.Carrier c)) ∧
    Sigma02Complete (fun c : EnumeratedPresentationCodes.PresentationCode =>
      ¬ IsSofic (EnumeratedPresentationCodes.Carrier c))

/-- **The classification holds.** -/
theorem soficEnumeratedExactClassification :
    SoficEnumeratedExactClassification :=
  ⟨sofic_enum_pi02Complete, nonsofic_enum_sigma02Complete⟩

end SoficEnumeratedPi02
end GroupApproximation
