import GroupApproximation.Computability.SoficEnumeratedPi02
import GroupApproximation.Computability.SoficRecognitionSecondLevel
import GroupApproximation.Sofic.LEFSofic

/-!
# Local embeddability of a recursively enumerated presentation is `Π⁰₂`-complete

`Computability.SoficEnumeratedPi02` classifies **soficity** on standard
recursively enumerated presentation codes: `Π⁰₂`-complete, both halves
unconditional.  This file carries out the same classification for **LEF**,
local embeddability into finite groups, on the same domain.

The two proofs share their whole effective layer --- permutation tables on
`{0, …, m}`, the validating certificate lookup `certGenN`, the word table
`wordTableN`, `movedCount`, the enumerated word-problem checker `wordCheck`
--- because none of that mentions soficity.  What changes is that **an LEF
challenge is exact**.

## What "exact" removes

A sofic challenge carries a tolerance `k` and asks for a microstate that
displaces the relator prefix by at most `1/(k+1)` and the listed words by at
least `1/2`; the backward direction then has to trade the multiplicative
defect against an area count, which is why `SoficEnumeratedPi02` needs
`AreaBounded` --- a *pair* `(N, A)` of a prefix length and an area --- and an
amplification step at the end.

An LEF challenge asks for a microstate in which the relators at addresses
`0, …, N` act as the **identity** and every listed word acts **nontrivially**.
Three consequences:

* **No tolerance.**  A challenge is a pair `(W, N)`, not a triple `(W, N, k)`.
* **No area count.**  `PrefixKilled` carries a prefix length alone: a
  microstate killing a long enough relator prefix kills every fixed element of
  the normal closure outright, so the directed-union subgroup argument
  (`prefixKilledSubgroup`) replaces the area calculus verbatim but with the
  numerical half deleted.
* **No amplification.**  The microstate *is* the local embedding: `f g` is the
  value of a chosen word for `g`, the trivial words force exact
  multiplicativity, and the separation words force exact injectivity.  There
  is no `isSofic_of_isSoficWeak` step.

## The two model conventions

`IsLEF` asks for a map into `Equiv.Perm (Fin n)` with `n` unconstrained,
while a `NatMicrostate` must act on a **nonempty** finite model.  Going from
LEF to a microstate we therefore pad the model by one point --- `optionPerm`
extends a permutation of `α` to `Option α` fixing `none`, injectively and
multiplicatively --- and going back we transport the microstate's model to
`Fin (Fintype.card _)` along `permCongrHom`, which is where the `n` of `IsLEF`
comes from.

## What is proved

* `isLEF_iff_forall_answersLEF` --- the oracle-free `∀∃` normal form for LEF
  of an enumerated code.
* `passesLEF_iff_exists_check` --- the microstate disjunct is a certificate
  search with a primitive recursive matrix.
* `rePred_answersLEF` --- one challenge being answered is recursively
  enumerable.
* `pi02_isLEF_enum` --- the upper bound.
* `lefCode_pi02Hard` --- hardness, from the generic second-level Rice
  statement, with the nonsofic seed of `SoficRecognitionSecondLevel` (nonsofic
  groups are not LEF, by `isSofic_of_isLEF`).
* `lef_enum_pi02Complete` / `nonlef_enum_sigma02Complete` --- the exact
  classification.

## Research nodes

* `research/lef-recognition-has-a-pi2-upper-bound.md` --- the upper bound,
  whose displayed normal form the enumerated `AnswersLEF` below is.
* `research/mf-recognition-two-generator-recursive-is-pi2-complete.md` --- the
  completeness table whose LEF row this file closes on enumerated codes.
* `research/second-level-rice-theorem-for-local-approximation-properties.md`
  --- the general second-level Rice statement supplying hardness.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace LEFEnumeratedPi02

open ArithmeticalHierarchy
open Higman
open EnumeratedPresentationCodes
open SoficRecognitionPi02
open SoficEnumeratedPi02

/-! ## Padding a permutation model by one point

`IsLEF` may hand back `n = 0`, whose model has no points, while a
`NatMicrostate` needs a nonempty one.  Extending along `Option` costs nothing
and is injective, which is all the two clauses of a challenge need. -/

/-- Extend a permutation of `α` to `Option α`, fixing `none`. -/
def optionPerm {α : Type} (σ : Equiv.Perm α) : Equiv.Perm (Option α) where
  toFun := Option.map σ
  invFun := Option.map σ.symm
  left_inv := fun x => by cases x <;> simp
  right_inv := fun x => by cases x <;> simp

@[simp] theorem optionPerm_some {α : Type} (σ : Equiv.Perm α) (a : α) :
    optionPerm σ (some a) = some (σ a) := rfl

@[simp] theorem optionPerm_none {α : Type} (σ : Equiv.Perm α) :
    optionPerm σ none = none := rfl

/-- The padding is a monoid homomorphism. -/
def optionPermHom (α : Type) : Equiv.Perm α →* Equiv.Perm (Option α) where
  toFun := optionPerm
  map_one' := by
    refine Equiv.ext fun x => ?_
    cases x <;> simp
  map_mul' σ τ := by
    refine Equiv.ext fun x => ?_
    cases x <;> simp [Equiv.Perm.mul_apply]

@[simp] theorem optionPermHom_apply {α : Type} (σ : Equiv.Perm α) :
    optionPermHom α σ = optionPerm σ := rfl

theorem optionPermHom_injective (α : Type) :
    Function.Injective (optionPermHom α) := by
  intro σ τ h
  refine Equiv.ext fun a => ?_
  have h' := Equiv.Perm.congr_fun h (some a)
  rw [optionPermHom_apply, optionPermHom_apply, optionPerm_some,
    optionPerm_some] at h'
  exact Option.some_injective _ h'

theorem optionPerm_eq_one_iff {α : Type} (σ : Equiv.Perm α) :
    optionPerm σ = 1 ↔ σ = 1 := by
  constructor
  · intro h
    refine optionPermHom_injective α ?_
    have h1 : (optionPermHom α) σ = optionPerm σ := rfl
    have h2 : (optionPermHom α) (1 : Equiv.Perm α) = 1 := map_one _
    rw [h1, h2, h]
  · rintro rfl
    exact map_one (optionPermHom α)

/-- Word evaluation commutes with the padding. -/
theorem evalRaw_optionPerm {α : Type} (x : ℕ → Equiv.Perm α) (w : RawWord) :
    evalRaw (fun i => optionPerm (x i)) w = optionPerm (evalRaw x w) := by
  have h := map_evalRaw (optionPermHom α) x w
  simp only [optionPermHom_apply] at h
  exact h.symm

/-- Transport of permutations along a bijection is injective. -/
theorem permCongrHom_injective {X Y : Type} (e : X ≃ Y) :
    Function.Injective (permCongrHom e) := by
  intro p q h
  refine Equiv.ext fun x => ?_
  have h' := Equiv.Perm.congr_fun h (e x)
  rw [permCongrHom_apply, permCongrHom_apply, e.symm_apply_apply] at h'
  exact e.injective h'

/-! ## Exact triviality in a microstate -/

/-- **Zero Hamming distance is equality**, on a nonempty model. -/
theorem hammingDistance_eq_zero_iff {Y : FiniteModel} (hY : 0 < Fintype.card Y)
    (p q : Equiv.Perm Y) : hammingDistance Y p q = 0 ↔ p = q := by
  classical
  constructor
  · intro h
    rw [hammingDistance, div_eq_zero_iff] at h
    rcases h with h | h
    · have hcard : (hammingDisagreement p q).card = 0 := by exact_mod_cast h
      have hempty : hammingDisagreement p q = ∅ := Finset.card_eq_zero.1 hcard
      refine Equiv.ext fun x => ?_
      by_contra hx
      have hmem : x ∈ hammingDisagreement p q :=
        (mem_hammingDisagreement p q x).2 hx
      rw [hempty] at hmem
      simp at hmem
    · exfalso
      have hz : Fintype.card Y = 0 := by exact_mod_cast h
      omega
  · rintro rfl
    exact hammingDistance_self Y p

/-- A microstate displaces a word by zero exactly when it kills it. -/
theorem len_eq_zero_iff (M : NatMicrostate) (w : RawWord) :
    M.len w = 0 ↔ evalRaw M.gen w = 1 := by
  rw [M.len_def]
  exact hammingDistance_eq_zero_iff M.nonempty _ _

/-- The free-group reading of the same statement, at an enumerated relator. -/
theorem hom_relatorAt (M : NatMicrostate) (c : PresentationCode) (j : ℕ) :
    M.hom (relatorAt c j) = evalRaw M.gen (rawRelator c j) :=
  M.hom_freeEval (rawRelator c j)

/-! ## The prefix that already kills a trivial word

The exact analogue of `SoficEnumeratedPi02.AreaBounded`, with the area count
deleted: a relator prefix suffices outright, because a microstate satisfying
the relators exactly satisfies every consequence of them exactly. -/

/-- **Killed by a relator prefix.**  Some prefix length `N` works: every
microstate sending the enumerated relators at addresses `0, …, N` to the
identity sends `x` to the identity. -/
def PrefixKilled (c : PresentationCode) (x : FreeGroup ℕ) : Prop :=
  ∃ N : ℕ, ∀ M : NatMicrostate,
    (∀ j, j ≤ N → M.hom (relatorAt c j) = 1) → M.hom x = 1

/-- The elements killed by a prefix form a subgroup. -/
def prefixKilledSubgroup (c : PresentationCode) : Subgroup (FreeGroup ℕ) where
  carrier := {x | PrefixKilled c x}
  one_mem' := ⟨0, fun M _ => map_one M.hom⟩
  mul_mem' := by
    rintro x y ⟨Nx, hx⟩ ⟨Ny, hy⟩
    refine ⟨max Nx Ny, fun M hrel => ?_⟩
    rw [map_mul, hx M fun j hj => hrel j (hj.trans (le_max_left _ _)),
      hy M fun j hj => hrel j (hj.trans (le_max_right _ _)), one_mul]
  inv_mem' := by
    rintro x ⟨N, hx⟩
    refine ⟨N, fun M hrel => ?_⟩
    rw [map_inv, hx M hrel, inv_one]

/-- Being killed is conjugation invariant, so the subgroup is normal. -/
instance prefixKilledSubgroup_normal (c : PresentationCode) :
    (prefixKilledSubgroup c).Normal where
  conj_mem := by
    rintro x ⟨N, hx⟩ g
    refine ⟨N, fun M hrel => ?_⟩
    rw [map_mul, map_mul, map_inv, hx M hrel, mul_one, mul_inv_cancel]

theorem mem_prefixKilledSubgroup_iff {c : PresentationCode} {x : FreeGroup ℕ} :
    x ∈ prefixKilledSubgroup c ↔ PrefixKilled c x := Iff.rfl

theorem subset_prefixKilledSubgroup (c : PresentationCode) :
    relatorSet c ⊆ (prefixKilledSubgroup c : Set (FreeGroup ℕ)) := by
  rintro r ⟨j, rfl⟩
  exact ⟨j, fun M hrel => hrel j le_rfl⟩

/-- **Exact relators force exact triviality.**  Every element of the normal
closure of the enumerated relator set carries a prefix length that kills it in
every microstate. -/
theorem exists_prefix_kill (c : PresentationCode) {x : FreeGroup ℕ}
    (hx : x ∈ Subgroup.normalClosure (relatorSet c)) : PrefixKilled c x :=
  mem_prefixKilledSubgroup_iff.1
    (Subgroup.normalClosure_le_normal (N := prefixKilledSubgroup c)
      (subset_prefixKilledSubgroup c) hx)

/-- **One prefix for a whole finite list of trivial words.** -/
theorem exists_prefix_kill_list (c : PresentationCode) (L : List RawWord)
    (hL : ∀ u ∈ L, evalCode c u = 1) :
    ∃ N : ℕ, ∀ M : NatMicrostate,
      (∀ j, j ≤ N → evalRaw M.gen (rawRelator c j) = 1) →
        ∀ u ∈ L, evalRaw M.gen u = 1 := by
  induction L with
  | nil => exact ⟨0, by simp⟩
  | cons a t ih =>
      obtain ⟨Nt, hNt⟩ := ih fun u hu => hL u (List.mem_cons_of_mem _ hu)
      obtain ⟨Na, hNa⟩ := exists_prefix_kill c
        ((evalCode_eq_one_iff c a).1 (hL a List.mem_cons_self))
      refine ⟨max Na Nt, fun M hrel u hu => ?_⟩
      rcases List.mem_cons.1 hu with rfl | hu'
      · have hb := hNa M fun j hj =>
          (hom_relatorAt M c j).trans (hrel j (hj.trans (le_max_left _ _)))
        rwa [M.hom_freeEval] at hb
      · exact hNt M (fun j hj => hrel j (hj.trans (le_max_right _ _))) u hu'

/-! ## Challenges and answers -/

/-- The conditions an exact challenge asks a microstate for: the enumerated
relators at the first `N + 1` addresses act as the identity, and every listed
word acts nontrivially. -/
def PassesLEF (c : PresentationCode) (W : List RawWord) (N : ℕ)
    (M : NatMicrostate) : Prop :=
  (∀ j, j ≤ N → evalRaw M.gen (rawRelator c j) = 1) ∧
    (∀ w ∈ W, evalRaw M.gen w ≠ 1)

/-- **One challenge, answered.**  Either the challenge is void because one of
its words is trivial in the coded group, or a microstate meets it exactly. -/
def AnswersLEF (c : PresentationCode) (W : List RawWord) (N : ℕ) : Prop :=
  (∃ w ∈ W, EnumWordProblem c w) ∨ ∃ M : NatMicrostate, PassesLEF c W N M

/-! ## Reading a microstate off a local embedding -/

/-- The generator family a local embedding provides, truncated at a bound. -/
noncomputable def lefGen (c : PresentationCode) {n : ℕ}
    (f : Carrier c → Equiv.Perm (Fin n)) (b i : ℕ) : Equiv.Perm (Fin n) :=
  if i < b then f (evalCode c [(i, true)]) else 1

theorem lefGen_of_lt (c : PresentationCode) {n : ℕ}
    (f : Carrier c → Equiv.Perm (Fin n)) {b i : ℕ} (hi : i < b) :
    lefGen c f b i = f (PresentedGroup.of i) := by
  rw [lefGen, if_pos hi, evalCode_letter_pos]

theorem lefGen_of_le (c : PresentationCode) {n : ℕ}
    (f : Carrier c → Equiv.Perm (Fin n)) {b i : ℕ} (hi : b ≤ i) :
    lefGen c f b i = 1 := by
  rw [lefGen, if_neg (Nat.not_lt.2 hi)]

/-- **The word induction, exactly.**  On a word whose letters are below the
bound and all of whose suffixes are evaluated inside the test set, the
truncated generators reproduce the local embedding on the nose. -/
theorem evalRaw_lefGen (c : PresentationCode) {n : ℕ} {F : Finset (Carrier c)}
    (f : Carrier c → Equiv.Perm (Fin n)) (hmul : LocalMultiplicativeOn F f)
    (b : ℕ) (hgenF : ∀ i, i < b → ∀ s : Bool, evalCode c [(i, s)] ∈ F) :
    ∀ u : RawWord, (∀ p ∈ u, p.1 < b) → (∀ t ∈ u.tails, evalCode c t ∈ F) →
      evalRaw (lefGen c f b) u = f (evalCode c u)
  | [], _, _ => by
      have h0 : evalCode c ([] : RawWord) = 1 := rfl
      have h1 : evalRaw (lefGen c f b) ([] : RawWord) = 1 := rfl
      rw [h0, h1, hmul.map_one]
  | p :: t, hlet, hsuf => by
      have htail : ∀ s ∈ t.tails, evalCode c s ∈ F := by
        intro s hs
        exact hsuf s (by rw [List.tails_cons]; exact List.mem_cons_of_mem _ hs)
      have hlett : ∀ q ∈ t, q.1 < b := fun q hq =>
        hlet q (List.mem_cons_of_mem _ hq)
      have ih := evalRaw_lefGen c f hmul b hgenF t hlett htail
      have hpb : p.1 < b := hlet p List.mem_cons_self
      have hmemp : evalCode c [p] ∈ F := hgenF p.1 hpb p.2
      have hmemt : evalCode c t ∈ F := hsuf t (by
        rw [List.tails_cons]
        exact List.mem_cons_of_mem _ (MFMicrostate.self_mem_tails t))
      have hletter : evalRaw (lefGen c f b) [p] = f (evalCode c [p]) := by
        obtain ⟨i, s⟩ := p
        have hib : i < b := hpb
        cases s with
        | true =>
            rw [evalRaw_letter_pos, evalCode_letter_pos, lefGen_of_lt c f hib]
        | false =>
            have hpos : (PresentedGroup.of i : Carrier c) ∈ F := by
              have h := hgenF i hib true
              rwa [evalCode_letter_pos] at h
            have hneg : (PresentedGroup.of i : Carrier c)⁻¹ ∈ F := by
              have h := hgenF i hib false
              rwa [evalCode_letter_neg] at h
            rw [evalRaw_letter_neg, evalCode_letter_neg,
              hmul.map_inv_of_mem hpos hneg, lefGen_of_lt c f hib]
      have hev : evalCode c (p :: t) = evalCode c [p] * evalCode c t :=
        evalRaw_cons' _ p t
      have hgv : evalRaw (lefGen c f b) (p :: t)
          = evalRaw (lefGen c f b) [p] * evalRaw (lefGen c f b) t :=
        evalRaw_cons' _ p t
      rw [hgv, hev, hmul.map_mul _ hmemp _ hmemt, hletter, ih]

/-! ## The equivalence -/

/-- **LEF of an enumerated coded group is exactly the assertion that every
exact challenge is answered.**

The right-hand side mentions the coded group only through `EnumWordProblem`,
a recursively enumerable predicate; the microstate disjunct mentions it not at
all. -/
theorem isLEF_iff_forall_answersLEF (c : PresentationCode) :
    IsLEF (Carrier c) ↔ ∀ W N, AnswersLEF c W N := by
  classical
  constructor
  · -- Forward: a local embedding of a large enough ball *is* a microstate.
    intro hLEF W N
    by_cases hvoid : ∃ w ∈ W, EnumWordProblem c w
    · exact Or.inl hvoid
    refine Or.inr ?_
    set relWords : List RawWord :=
      (List.range (N + 1)).map (rawRelator c) with hrelW
    set allWords : List RawWord := W ++ relWords with hall
    set bnd : ℕ := (allWords.map letterBound).foldr max 0 with hbnd
    set sufs : List RawWord := allWords.flatMap List.tails with hsufs
    set gens : List RawWord :=
      (List.range bnd).flatMap fun i => [[(i, true)], [(i, false)]] with hgens
    set F : Finset (Carrier c) :=
      ((([] : RawWord) :: (sufs ++ gens)).map (evalCode c)).toFinset with hF
    have hmemF : ∀ u ∈ ([] : RawWord) :: (sufs ++ gens), evalCode c u ∈ F := by
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
    obtain ⟨n, f, hinj, hmul⟩ := hLEF F
    have hword : ∀ u ∈ allWords, evalRaw (lefGen c f bnd) u = f (evalCode c u) :=
      fun u hu => evalRaw_lefGen c f hmul bnd hgenF u (hletF u hu) (hsufF u hu)
    refine ⟨{ carrier := ⟨Option (Fin n), inferInstance, inferInstance⟩
              nonempty := by
                show 0 < Fintype.card (Option (Fin n))
                rw [Fintype.card_option]
                omega
              bound := bnd
              gen := fun i => optionPerm (lefGen c f bnd i)
              gen_eq_one := fun i hi => by
                show optionPerm (lefGen c f bnd i) = 1
                rw [lefGen_of_le c f hi]
                exact map_one (optionPermHom (Fin n)) }, ?_, ?_⟩
    · intro j hj
      have hrall : rawRelator c j ∈ allWords := by
        rw [hall]
        refine List.mem_append_right _ ?_
        rw [hrelW, List.mem_map]
        exact ⟨j, List.mem_range.2 (Nat.lt_succ_of_le hj), rfl⟩
      have htriv : evalCode c (rawRelator c j) = 1 :=
        (evalCode_eq_one_iff c (rawRelator c j)).2
          (Subgroup.subset_normalClosure (relatorAt_mem_relatorSet c j))
      have hw := hword _ hrall
      rw [htriv, hmul.map_one] at hw
      show evalRaw (fun i => optionPerm (lefGen c f bnd i)) (rawRelator c j) = 1
      rw [evalRaw_optionPerm (lefGen c f bnd) (rawRelator c j), hw]
      exact map_one (optionPermHom (Fin n))
    · intro w hw
      have hwall : w ∈ allWords := by
        rw [hall]; exact List.mem_append_left _ hw
      have hne : evalCode c w ≠ 1 := fun hcon => hvoid ⟨w, hw, hcon⟩
      have hwF : evalCode c w ∈ F :=
        hsufF w hwall w (MFMicrostate.self_mem_tails w)
      have hfne : f (evalCode c w) ≠ 1 := by
        intro hcon
        refine hne (hinj (Finset.mem_coe.2 hwF) (Finset.mem_coe.2 h1F) ?_)
        rw [hcon, hmul.map_one]
      have hev := hword w hwall
      show evalRaw (fun i => optionPerm (lefGen c f bnd i)) w ≠ 1
      rw [evalRaw_optionPerm (lefGen c f bnd) w, hev]
      intro hcon
      exact hfne ((optionPerm_eq_one_iff _).1 hcon)
  · -- Backward: a microstate meeting the challenge *is* a local embedding.
    intro h s
    set wd : Carrier c → RawWord :=
      Function.surjInv (evalCode_surjective c) with hwd
    have hwdspec : ∀ g : Carrier c, evalCode c (wd g) = g := fun g =>
      Function.surjInv_eq (evalCode_surjective c) g
    set pairs : Finset (Carrier c × Carrier c) :=
      (s ×ˢ s).filter fun q => q.1 ≠ q.2 with hpairs
    set W : List RawWord :=
      pairs.toList.map fun q => invRaw (wd q.1) ++ wd q.2 with hW
    set trivWords : List RawWord :=
      wd 1 :: (s ×ˢ s).toList.map fun q =>
        invRaw (wd q.1 ++ wd q.2) ++ wd (q.1 * q.2) with hTW
    have htrivial : ∀ u ∈ trivWords, evalCode c u = 1 := by
      intro u hu
      rw [hTW] at hu
      rcases List.mem_cons.1 hu with rfl | hu'
      · rw [hwdspec]
      · rw [List.mem_map] at hu'
        obtain ⟨q, _hq, rfl⟩ := hu'
        rw [evalCode_append, evalCode_invRaw, evalCode_append, hwdspec, hwdspec,
          hwdspec, inv_mul_cancel]
    obtain ⟨N, hN⟩ := exists_prefix_kill_list c trivWords htrivial
    rcases h W N with hvoid | ⟨M, hrel, hsep⟩
    · exfalso
      obtain ⟨w, hwmem, hwtriv⟩ := hvoid
      rw [hW, List.mem_map] at hwmem
      obtain ⟨q, hq, rfl⟩ := hwmem
      rw [Finset.mem_toList, hpairs, Finset.mem_filter] at hq
      have hwt : evalCode c (invRaw (wd q.1) ++ wd q.2) = 1 := hwtriv
      rw [evalCode_append, evalCode_invRaw, hwdspec, hwdspec,
        inv_mul_eq_one] at hwt
      exact hq.2 hwt
    have htrivEval : ∀ u ∈ trivWords, evalRaw M.gen u = 1 := hN M hrel
    refine ⟨Fintype.card M.carrier,
      fun g => permCongrHom (Fintype.equivFin M.carrier) (evalRaw M.gen (wd g)),
      ?_, ?_, ?_⟩
    · intro x hx y hy hxy
      by_contra hne
      have hmemW : (invRaw (wd y) ++ wd x) ∈ W := by
        rw [hW, List.mem_map]
        refine ⟨(y, x), ?_, rfl⟩
        rw [Finset.mem_toList, hpairs, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨Finset.mem_coe.1 hy, Finset.mem_coe.1 hx⟩,
          fun hcon => hne hcon.symm⟩
      refine hsep _ hmemW ?_
      have heq : evalRaw M.gen (wd x) = evalRaw M.gen (wd y) :=
        permCongrHom_injective _ hxy
      rw [evalRaw_append, evalRaw_invRaw, heq, inv_mul_cancel]
    · show permCongrHom (Fintype.equivFin M.carrier) (evalRaw M.gen (wd 1)) = 1
      rw [htrivEval (wd 1) (by rw [hTW]; exact List.mem_cons_self)]
      exact map_one _
    · intro x hx y hy
      have hmemT : (invRaw (wd x ++ wd y) ++ wd (x * y)) ∈ trivWords := by
        rw [hTW]
        refine List.mem_cons_of_mem _ ?_
        rw [List.mem_map]
        refine ⟨(x, y), ?_, rfl⟩
        rw [Finset.mem_toList, Finset.mem_product]
        exact ⟨hx, hy⟩
      have hz := htrivEval _ hmemT
      rw [evalRaw_append, evalRaw_invRaw, evalRaw_append, inv_mul_eq_one] at hz
      show permCongrHom (Fintype.equivFin M.carrier) (evalRaw M.gen (wd (x * y)))
        = permCongrHom (Fintype.equivFin M.carrier) (evalRaw M.gen (wd x))
          * permCongrHom (Fintype.equivFin M.carrier) (evalRaw M.gen (wd y))
      rw [← hz, map_mul]

/-! ## The microstate disjunct is a certificate search

Every piece of effective data below --- `PermCert`, the validating lookup
`certGenN`, the word table `wordTableN`, `movedCount` --- is
`SoficEnumeratedPi02`'s, unchanged.  Only the two comparisons change: instead
of cleared-denominator inequalities against `1/(k+1)` and `1/2`, an exact
challenge asks for `movedCount = 0` and `0 < movedCount`. -/

/-- A certificate kills a word exactly when its table moves no point. -/
theorem movedCount_eq_zero_iff (cert : PermCert) (w : RawWord) :
    movedCount cert.1 (wordTableN cert w) = 0
      ↔ evalRaw (certMicrostate cert).gen w = 1 := by
  rw [← len_eq_zero_iff, SoficEnumeratedPi02.len_certMicrostate]
  have hpos : (0 : ℝ) < (cert.1 : ℝ) + 1 := by positivity
  rw [div_eq_zero_iff]
  constructor
  · intro h
    exact Or.inl (by exact_mod_cast h)
  · rintro (h | h)
    · exact_mod_cast h
    · exact absurd h hpos.ne'

/-- The relator clause, as a Boolean test. -/
def relatorOkLEF (c : PresentationCode) (cert : PermCert) (j : ℕ) : Bool :=
  decide (movedCount cert.1 (wordTableN cert (rawRelator c j)) = 0)

/-- The separation clause, as a Boolean test. -/
def wordOkLEF (cert : PermCert) (w : RawWord) : Bool :=
  decide (0 < movedCount cert.1 (wordTableN cert w))

/-- The checker input: a code together with an exact challenge `(W, N)`. -/
abbrev CheckInputLEF : Type := PresentationCode × (List RawWord × ℕ)

/-- **The certificate checker.**  Every clause is a comparison of naturals, so
this is a total Boolean function of raw data. -/
def passesCheckLEF (x : CheckInputLEF) (cert : PermCert) : Bool :=
  decide ((List.range (x.2.2 + 1)).map (relatorOkLEF x.1 cert)
      = (List.range (x.2.2 + 1)).map fun _ => true) &&
    decide (x.2.1.map (wordOkLEF cert) = x.2.1.map fun _ => true)

theorem passesCheckLEF_eq_true_iff (x : CheckInputLEF) (cert : PermCert) :
    passesCheckLEF x cert = true ↔
      ((∀ j, j ≤ x.2.2 →
          movedCount cert.1 (wordTableN cert (rawRelator x.1 j)) = 0) ∧
        ∀ w ∈ x.2.1, 0 < movedCount cert.1 (wordTableN cert w)) := by
  rw [passesCheckLEF, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff,
    map_eq_map_iff, map_eq_map_iff]
  constructor
  · rintro ⟨hr, hw⟩
    refine ⟨fun j hj => ?_, fun w hwmem => ?_⟩
    · have h := hr j (List.mem_range.2 (Nat.lt_succ_of_le hj))
      rwa [relatorOkLEF, decide_eq_true_iff] at h
    · have h := hw w hwmem
      rwa [wordOkLEF, decide_eq_true_iff] at h
  · rintro ⟨hr, hw⟩
    refine ⟨fun j hj => ?_, fun w hwmem => ?_⟩
    · rw [relatorOkLEF, decide_eq_true_iff]
      exact hr j (Nat.lt_succ_iff.1 (List.mem_range.1 hj))
    · rw [wordOkLEF, decide_eq_true_iff]
      exact hw w hwmem

/-- **The microstate disjunct is a certificate search.** -/
theorem passesLEF_iff_exists_check (c : PresentationCode) (W : List RawWord)
    (N : ℕ) :
    (∃ M : NatMicrostate, PassesLEF c W N M)
      ↔ ∃ cert : PermCert, passesCheckLEF (c, W, N) cert = true := by
  constructor
  · rintro ⟨M, hrel, hsep⟩
    obtain ⟨cert, hlen⟩ := exists_cert_len M
    refine ⟨cert, (passesCheckLEF_eq_true_iff (c, W, N) cert).2 ⟨?_, ?_⟩⟩
    · intro j hj
      refine (movedCount_eq_zero_iff cert (rawRelator c j)).2 ?_
      refine (len_eq_zero_iff _ _).1 ?_
      rw [hlen]
      exact (len_eq_zero_iff M (rawRelator c j)).2 (hrel j hj)
    · intro w hw
      rcases Nat.eq_zero_or_pos (movedCount cert.1 (wordTableN cert w))
        with h0 | hpos
      · exfalso
        have h1 := (movedCount_eq_zero_iff cert w).1 h0
        have h2 := (len_eq_zero_iff _ w).2 h1
        rw [hlen] at h2
        exact hsep w hw ((len_eq_zero_iff M w).1 h2)
      · exact hpos
  · rintro ⟨cert, hcheck⟩
    obtain ⟨hrel, hsep⟩ := (passesCheckLEF_eq_true_iff (c, W, N) cert).1 hcheck
    refine ⟨certMicrostate cert, fun j hj => ?_, fun w hw => ?_⟩
    · exact (movedCount_eq_zero_iff cert (rawRelator c j)).1 (hrel j hj)
    · intro hcon
      have hz := (movedCount_eq_zero_iff cert w).2 hcon
      have hp := hsep w hw
      omega

/-! ## The checker is primitive recursive -/

section Effective

variable {α : Type} [Primcodable α]

theorem primrec_relatorOkLEF {fc : α → PresentationCode}
    {fcert : α → PermCert} {fj : α → ℕ} (hc : Primrec fc)
    (hcert : Primrec fcert) (hj : Primrec fj) :
    Primrec fun a => relatorOkLEF (fc a) (fcert a) (fj a) := by
  have hrel : Primrec fun a : α => rawRelator (fc a) (fj a) :=
    primrec_rawRelator.comp hc hj
  have hcount : Primrec fun a : α =>
      movedCount (fcert a).1 (wordTableN (fcert a) (rawRelator (fc a) (fj a))) :=
    primrec_movedCount (Primrec.fst.comp hcert) (primrec_wordTableN hcert hrel)
  exact (Primrec.eq.comp hcount (Primrec.const 0)).decide.of_eq fun _ => rfl

theorem primrec_wordOkLEF {fcert : α → PermCert} {fw : α → RawWord}
    (hcert : Primrec fcert) (hw : Primrec fw) :
    Primrec fun a => wordOkLEF (fcert a) (fw a) := by
  have hcount : Primrec fun a : α =>
      movedCount (fcert a).1 (wordTableN (fcert a) (fw a)) :=
    primrec_movedCount (Primrec.fst.comp hcert) (primrec_wordTableN hcert hw)
  exact (Primrec.nat_lt.comp (Primrec.const 0) hcount).decide.of_eq fun _ => rfl

end Effective

theorem primrec_passesCheckLEF : Primrec₂ passesCheckLEF := by
  have hc : Primrec fun z : CheckInputLEF × PermCert => z.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hW : Primrec fun z : CheckInputLEF × PermCert => z.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hN : Primrec fun z : CheckInputLEF × PermCert => z.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hcert : Primrec fun z : CheckInputLEF × PermCert => z.2 := Primrec.snd
  have hrange : Primrec fun z : CheckInputLEF × PermCert =>
      List.range (z.1.2.2 + 1) :=
    Primrec.list_range.comp (Primrec.succ.comp hN)
  have hrelList : Primrec fun z : CheckInputLEF × PermCert =>
      (List.range (z.1.2.2 + 1)).map (relatorOkLEF z.1.1 z.2) :=
    Primrec.list_map hrange
      (primrec_relatorOkLEF (hc.comp Primrec.fst) (hcert.comp Primrec.fst)
        Primrec.snd).to₂
  have hwordList : Primrec fun z : CheckInputLEF × PermCert =>
      z.1.2.1.map (wordOkLEF z.2) :=
    Primrec.list_map hW
      (primrec_wordOkLEF (hcert.comp Primrec.fst) Primrec.snd).to₂
  have htrueRange : Primrec fun z : CheckInputLEF × PermCert =>
      (List.range (z.1.2.2 + 1)).map fun _ : ℕ => true :=
    Primrec.list_map hrange (Primrec.const true).to₂
  have htrueWord : Primrec fun z : CheckInputLEF × PermCert =>
      z.1.2.1.map fun _ : RawWord => true :=
    Primrec.list_map hW (Primrec.const true).to₂
  exact (Primrec.and.comp (Primrec.eq.comp hrelList htrueRange).decide
    (Primrec.eq.comp hwordList htrueWord).decide).of_eq fun _ => rfl

/-! ## Answering a challenge is recursively enumerable -/

/-- The search space for one exact challenge: a raw word together with a
word-problem certificate for the void disjunct, paired with a permutation
certificate for the microstate disjunct. -/
abbrev AnswerDataLEF : Type := (RawWord × WordCertificate) × PermCert

/-- The matrix of the answer search. -/
def answerCheckLEF (x : CheckInputLEF) (b : AnswerDataLEF) : Bool :=
  (decide (b.1.1 ∈ x.2.1) && wordCheck (x.1, b.1.1) b.1.2) || passesCheckLEF x b.2

theorem answerCheckLEF_iff (x : CheckInputLEF) :
    (∃ b : AnswerDataLEF, answerCheckLEF x b = true)
      ↔ AnswersLEF x.1 x.2.1 x.2.2 := by
  constructor
  · rintro ⟨⟨⟨w, p⟩, cert⟩, hb⟩
    rw [answerCheckLEF, Bool.or_eq_true] at hb
    rcases hb with h | h
    · exact Or.inl ((exists_voidN_iff x.1 x.2.1).1 ⟨(w, p), h⟩)
    · exact Or.inr ((passesLEF_iff_exists_check x.1 x.2.1 x.2.2).2 ⟨cert, h⟩)
  · intro hAns
    rcases hAns with hvoid | hM
    · obtain ⟨⟨w, p⟩, h⟩ := (exists_voidN_iff x.1 x.2.1).2 hvoid
      exact ⟨((w, p), default), by
        rw [answerCheckLEF, Bool.or_eq_true]; exact Or.inl h⟩
    · obtain ⟨cert, h⟩ := (passesLEF_iff_exists_check x.1 x.2.1 x.2.2).1 hM
      exact ⟨((default, default), cert), by
        rw [answerCheckLEF, Bool.or_eq_true]; exact Or.inr h⟩

theorem primrec_answerCheckLEF : Primrec₂ answerCheckLEF := by
  have hmem : PrimrecPred fun z : CheckInputLEF × AnswerDataLEF =>
      z.2.1.1 ∈ z.1.2.1 := by
    have h : PrimrecRel fun (L : List RawWord) (u : RawWord) =>
        ∃ a ∈ L, a = u :=
      PrimrecRel.exists_mem_list Primrec.eq
    refine (h.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))).of_eq fun z => ?_
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hz
      exact ⟨z.2.1.1, hz, rfl⟩
  have hsearch : Primrec fun z : CheckInputLEF × AnswerDataLEF =>
      wordCheck (z.1.1, z.2.1.1) z.2.1.2 :=
    primrec_wordCheck.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
  have hpass : Primrec fun z : CheckInputLEF × AnswerDataLEF =>
      passesCheckLEF z.1 z.2.2 :=
    primrec_passesCheckLEF.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  exact (Primrec.or.comp (Primrec.and.comp hmem.decide hsearch) hpass).of_eq
    fun _ => rfl

/-- **Answering one exact challenge is recursively enumerable.** -/
theorem rePred_answersLEF :
    REPred fun x : PresentationCode × (List RawWord × ℕ) =>
      AnswersLEF x.1 x.2.1 x.2.2 :=
  (WordProblemRE.rePred_exists_eq_true primrec_answerCheckLEF.to_comp).of_eq
    answerCheckLEF_iff

/-! ## The arithmetical bounds -/

/-- The exact challenge named by a scale index. -/
def decodeChallengeLEF (n : ℕ) : List RawWord × ℕ :=
  (Encodable.decode (α := List RawWord × ℕ) n).getD ([], 0)

theorem primrec_decodeChallengeLEF : Primrec decodeChallengeLEF :=
  (Primrec.option_getD.comp Primrec.decode
    (Primrec.const (([], 0) : List RawWord × ℕ))).of_eq fun _ => rfl

theorem decodeChallengeLEF_surjective (q : List RawWord × ℕ) :
    decodeChallengeLEF (Encodable.encode q) = q := by
  simp [decodeChallengeLEF]

-- As in `SoficEnumeratedPi02`: sealing the decoder keeps the arithmetical
-- bookkeeping cheap, since `Encodable` decoding at a product type runs through
-- `Nat.unpair`, whose well-founded recursion the kernel would try to evaluate
-- on an open term.  Only `decodeChallengeLEF_surjective` is needed below.
attribute [irreducible] decodeChallengeLEF

/-- **Recognising local embeddability into finite groups from a recursively
enumerated presentation code is `Π⁰₂`.** -/
theorem pi02_isLEF_enum :
    Pi02 fun c : PresentationCode => IsLEF (Carrier c) := by
  refine ⟨fun z : PresentationCode × ℕ =>
    AnswersLEF z.1 (decodeChallengeLEF z.2).1 (decodeChallengeLEF z.2).2,
    ?_, ?_⟩
  · have hmap : Computable fun z : PresentationCode × ℕ =>
        (z.1, decodeChallengeLEF z.2) :=
      (Primrec.pair Primrec.fst
        (primrec_decodeChallengeLEF.comp Primrec.snd)).to_comp
    exact rePred_answersLEF.comp hmap
  · intro c
    refine Iff.trans (isLEF_iff_forall_answersLEF c) ?_
    constructor
    · intro h n
      exact h (decodeChallengeLEF n).1 (decodeChallengeLEF n).2
    · intro h W N
      have hn : AnswersLEF c (decodeChallengeLEF (Encodable.encode (W, N))).1
          (decodeChallengeLEF (Encodable.encode (W, N))).2 :=
        h (Encodable.encode (W, N))
      rw [decodeChallengeLEF_surjective (W, N)] at hn
      exact hn

/-- **Recognising failure of LEF from a recursively enumerated presentation
code is `Σ⁰₂`.** -/
theorem sigma02_not_isLEF_enum :
    Sigma02 fun c : PresentationCode => ¬ IsLEF (Carrier c) :=
  (sigma02_compl_iff _).2 pi02_isLEF_enum

/-! ## Hardness

The generic second-level Rice statement of `SoficRecognitionSecondLevel`
applies verbatim: LEF is hereditary along injective homomorphisms, holds at
the trivial group, and fails at the nonsofic finite presentation code Theorem
C of this repository supplies --- a nonsofic group is not LEF, since LEF
groups are sofic. -/

/-- LEF read as a property of groups in `Type`. -/
abbrev LEFProperty : (H : Type) → [Group H] → Prop := fun H _ ↦ IsLEF H

/-- The trivial group is LEF, being finite. -/
theorem isLEF_punit : IsLEF (PUnit : Type) :=
  isLEF_of_finite PUnit

/-- A non-LEF finite presentation **code**, with no hypotheses: the nonsofic
seed of `SoficRecognitionSecondLevel` is not LEF, because LEF implies sofic. -/
theorem exists_nonlef_presentationCode :
    ∃ seed : PresentationCodes.PresentationCode,
      ¬ IsLEF (PresentationCodes.Carrier seed) := by
  obtain ⟨seed, hseed⟩ :=
    SoficRecognitionSecondLevel.exists_nonsofic_presentationCode
  exact ⟨seed, fun hlef => hseed (isSofic_of_isLEF hlef)⟩

/-- **Recognising LEF from a recursively enumerated presentation is
`Π⁰₂`-hard.**  Unconditional: heredity is `isLEF_of_injective`, the positive
branch is `isLEF_punit`, and the forbidden seed comes from
`exists_finitelyPresented_nonsofic_group`. -/
theorem lefCode_pi02Hard :
    Pi02Hard (fun q : EnumeratedPresentationCodes.PresentationCode ↦
      IsLEF (EnumeratedPresentationCodes.Carrier q)) := by
  obtain ⟨seed, hseed⟩ := exists_nonlef_presentationCode
  exact SoficRecognitionSecondLevel.pi02Hard_of_hereditary LEFProperty
    (fun f hf hK ↦ isLEF_of_injective f hf hK) isLEF_punit seed hseed

/-- **Recognising failure of LEF from a recursively enumerated presentation is
`Σ⁰₂`-hard.** -/
theorem nonlefCode_sigma02Hard :
    Sigma02Hard (fun q : EnumeratedPresentationCodes.PresentationCode ↦
      ¬ IsLEF (EnumeratedPresentationCodes.Carrier q)) :=
  pi02Hard_compl lefCode_pi02Hard

/-! ## The exact classification

Upper bound and hardness are statements about the *same* domain --- standard
recursively enumerated presentation codes --- so they pair, and both carry no
hypothesis.  This is the second group approximation property to receive an
exact arithmetical classification inside this development, after soficity. -/

/-- **Local embeddability into finite groups of a recursively enumerated
presentation is `Π⁰₂`-complete.**  No hypothesis, no construction datum. -/
theorem lef_enum_pi02Complete :
    Pi02Complete fun c : EnumeratedPresentationCodes.PresentationCode =>
      IsLEF (EnumeratedPresentationCodes.Carrier c) :=
  ⟨pi02_isLEF_enum, lefCode_pi02Hard⟩

/-- **Failure of LEF for a recursively enumerated presentation is
`Σ⁰₂`-complete.** -/
theorem nonlef_enum_sigma02Complete :
    Sigma02Complete fun c : EnumeratedPresentationCodes.PresentationCode =>
      ¬ IsLEF (EnumeratedPresentationCodes.Carrier c) :=
  pi02Complete_compl lef_enum_pi02Complete

/-! ## The closed form -/

/-- **The exact arithmetical classification of LEF on enumerated
presentations**, as a closed proposition. -/
def LEFEnumeratedExactClassification : Prop :=
  Pi02Complete (fun c : EnumeratedPresentationCodes.PresentationCode =>
      IsLEF (EnumeratedPresentationCodes.Carrier c)) ∧
    Sigma02Complete (fun c : EnumeratedPresentationCodes.PresentationCode =>
      ¬ IsLEF (EnumeratedPresentationCodes.Carrier c))

/-- **The classification holds.** -/
theorem lefEnumeratedExactClassification : LEFEnumeratedExactClassification :=
  ⟨lef_enum_pi02Complete, nonlef_enum_sigma02Complete⟩

end LEFEnumeratedPi02
end GroupApproximation
