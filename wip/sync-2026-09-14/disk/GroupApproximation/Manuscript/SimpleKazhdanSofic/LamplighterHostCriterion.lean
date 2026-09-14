import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterHostTables

/-!
# The word problem of `G_Δ`: vanishing of coefficients

`simple_kazhdan_sofic_group.tex` at 8b36733d7, section "LEF groups", l.451–454:

> After collecting equal $\xi$ and equal coordinates, the word is trivial if and only if every
> coefficient of its difference from $I_3$ vanishes at every assignment of its finitely many
> variables, as $\Omega$ is the full shift.

* `entryEval_eq_zero_iff`: an entry vanishes exactly when, for every unit that occurs, the
  coefficients of the monomials with that unit sum to zero at every point (`R_Δ = ⊕_ξ LC(Ω, F_2) u_ξ`).
* `factorFn_apply`: `e_U ∘ ξ⁻¹` is `x ↦ x(δ) + c(δ)` for `ξ = (x ↦ δx + c)`, and
  `wordValue_lampGen_eq_iff`: two words in the letters of `Λ` are equal exactly when their `Δ`-letters
  are equal and their lamps agree at the lamp positions that occur.
* The decision `wordTrivial E w`, from a test `E` of equality of `Δ`-words. The points `x ∈ Ω` are
  replaced by the assignments of bits to the coordinates `x(δ)` that occur, consistent with `E`; as
  `Ω` is the full shift, every consistent assignment is the restriction of a point.
* `wordTrivial_eq_true_iff`: when `E` is correct on the `Δ`-words of `w`, the decision says whether
  `w` is trivial.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace Lamplighter
namespace Host

open Multiplicative

variable {ι : Type*} {Δ : Type} [Group Δ] (t : ι → Δ)

/-! ## Coefficients -/

/-- The coefficient `∏_{p ∈ F} e_U ∘ ξ_p⁻¹` of a monomial `(F, w)`. -/
noncomputable def monoFn (m : Mono ι) : LocallyConstant (LampSpace Δ) (ZMod 2) :=
  (m.1.map (factorFn t)).prod

theorem monoFn_apply (m : Mono ι) (x : LampSpace Δ) :
    monoFn t m x = (m.1.map fun p => factorFn t p x).prod := by
  obtain ⟨F, w⟩ := m
  show (F.map (factorFn t)).prod x = (F.map fun p => factorFn t p x).prod
  induction F with
  | nil => rfl
  | cons p F ih =>
    rw [List.map_cons, List.prod_cons, LocallyConstant.mul_apply, ih, List.map_cons,
      List.prod_cons]

open Classical in
/-- The coefficient of `u_η` in an entry, at a point `x`. -/
theorem coeff_entryEval_apply (e : Entry ι) (η : LampAffine Δ) (x : LampSpace Δ) :
    (ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2)).symm
        (SkewMonoidAlgebra.coeff (entryEval t e) η) x =
      (e.map fun m => if wordValue (lampGen t) m.2 = η then monoFn t m x else 0).sum := by
  induction e with
  | nil => rfl
  | cons m e ih =>
    rw [entryEval_cons, SkewMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add,
      LocallyConstant.add_apply, ih, List.map_cons, List.sum_cons, monoEval,
      ← ClopenGroupCrossedProduct.single_eq_coeff_mul_unit, SkewMonoidAlgebra.coeff_single,
      Finsupp.single_apply]
    split_ifs <;> rfl

open Classical in
/-- **Collecting equal units** (tex l.451–454): an entry vanishes exactly when, for every unit
that occurs, the coefficients of the monomials with that unit sum to zero at every point. -/
theorem entryEval_eq_zero_iff (e : Entry ι) :
    entryEval t e = 0 ↔ ∀ m0 ∈ e, ∀ x : LampSpace Δ,
      (e.map fun m => if wordValue (lampGen t) m.2 = wordValue (lampGen t) m0.2 then
        monoFn t m x else 0).sum = 0 := by
  constructor
  · intro h m0 _ x
    rw [← coeff_entryEval_apply, h]
    rfl
  · intro h
    refine SkewMonoidAlgebra.ext fun η => ?_
    refine (ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2)).symm.injective
      (LocallyConstant.ext fun x => ?_)
    rw [coeff_entryEval_apply]
    show _ = (0 : ZMod 2)
    by_cases hη : ∃ m0 ∈ e, wordValue (lampGen t) m0.2 = η
    · obtain ⟨m0, hm0, rfl⟩ := hη
      exact h m0 hm0 x
    · refine List.sum_eq_zero fun y hy => ?_
      obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hy
      exact if_neg fun he => hη ⟨m, hm, he⟩

/-- **The factors** (tex l.450): `e_U ∘ ξ_p⁻¹` is `x ↦ x(δ) + c(δ)`, for `ξ_p = (x ↦ δx + c)`. -/
theorem factorFn_apply (p : List (Option ι × Bool)) (x : LampSpace Δ) :
    factorFn t p x =
      x (wordValue t (deltaWord p)) + lampSum t p (wordValue t (deltaWord p)) := by
  have hv := wordValue_lampGen t p
  set ξ := wordValue (lampGen t) p with hξ
  set γ := wordValue t (deltaWord p) with hγ
  have hl : ξ.left = ofAdd (lampSum t p) := by
    rw [hv]
    simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.left_inr,
      SemidirectProduct.right_inl, map_one, MulAut.one_apply, mul_one]
  have hr : ξ.right = γ := by
    rw [hv, SemidirectProduct.mul_right, SemidirectProduct.right_inl, SemidirectProduct.right_inr,
      one_mul]
  have hy : x γ = factorFn t p x + lampSum t p γ := by
    conv_lhs => rw [← smul_inv_smul ξ x]
    rw [smul_apply, hr, inv_mul_cancel, hl, toAdd_ofAdd]
    rfl
  have key : ∀ a b c : ZMod 2, a = b + c → b = a + c := by decide
  exact key _ _ _ hy

/-- **Equality in `Λ`** (tex l.444–447): two words in the letters of `Λ` are equal exactly when
their `Δ`-letters are equal and their lamps agree at every lamp position that occurs. -/
theorem wordValue_lampGen_eq_iff [DecidableEq Δ] (u u' : List (Option ι × Bool)) :
    wordValue (lampGen t) u = wordValue (lampGen t) u' ↔
      wordValue t (deltaWord u) = wordValue t (deltaWord u') ∧
        ∀ q ∈ lampPrefixes u ++ lampPrefixes u',
          lampSum t u (wordValue t q) = lampSum t u' (wordValue t q) := by
  rw [wordValue_lampGen, wordValue_lampGen]
  constructor
  · intro h
    have hr := congrArg SemidirectProduct.right h
    have hl := congrArg SemidirectProduct.left h
    simp only [SemidirectProduct.mul_right, SemidirectProduct.right_inl,
      SemidirectProduct.right_inr, one_mul] at hr
    simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.left_inr,
      SemidirectProduct.right_inl, map_one, MulAut.one_apply, mul_one] at hl
    refine ⟨hr, fun q _ => ?_⟩
    rw [ofAdd.injective hl]
  · rintro ⟨hr, hc⟩
    have hF : lampSum t u = lampSum t u' := by
      refine Finsupp.ext fun a => ?_
      by_cases ha : ∃ q ∈ lampPrefixes u ++ lampPrefixes u', wordValue t q = a
      · obtain ⟨q, hq, rfl⟩ := ha
        exact hc q hq
      · have h1 : ((lampPrefixes u).filter fun q => wordValue t q = a) = [] :=
          List.filter_eq_nil_iff.2 fun q hq => by
            simpa using fun he => ha ⟨q, List.mem_append.2 (Or.inl hq), he⟩
        have h2 : ((lampPrefixes u').filter fun q => wordValue t q = a) = [] :=
          List.filter_eq_nil_iff.2 fun q hq => by
            simpa using fun he => ha ⟨q, List.mem_append.2 (Or.inr hq), he⟩
        rw [lampSum_apply, lampSum_apply, h1, h2]
    rw [hr, hF]

/-! ## Bits and lists -/

/-- `false ↦ 0` and `true ↦ 1`. -/
def bitZ (b : Bool) : ZMod 2 :=
  if b then 1 else 0

theorem bitZ_xor (a b : Bool) : bitZ (xor a b) = bitZ a + bitZ b := by
  cases a <;> cases b <;> decide

theorem bitZ_and (a b : Bool) : bitZ (a && b) = bitZ a * bitZ b := by
  cases a <;> cases b <;> decide

theorem bitZ_decide (z : ZMod 2) : bitZ (decide (z = 1)) = z := by
  revert z
  decide

theorem bitZ_inj {a b : Bool} : bitZ a = bitZ b ↔ a = b := by
  cases a <;> cases b <;> decide

theorem bitZ_eq_zero {b : Bool} : bitZ b = 0 ↔ b = false := by
  cases b <;> decide

theorem getD_mem {α : Type*} {l : List α} {i : ℕ} {d : α} (h : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

theorem getD_map_of_lt {α β : Type*} {l : List α} {i : ℕ} (h : i < l.length) (f : α → β) (d : α)
    (d' : β) : (l.map f).getD i d' = f (l.getD i d) := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_map_findIdx {α β : Type*} [DecidableEq α] {l : List α} {y : α} (h : y ∈ l)
    (f : α → β) (d : β) : (l.map f).getD (l.findIdx fun z => decide (z = y)) d = f y := by
  have hlt : l.findIdx (fun z => decide (z = y)) < l.length :=
    List.findIdx_lt_length_of_exists ⟨y, h, by simp⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt]
  exact congrArg f (of_decide_eq_true (List.findIdx_getElem (w := hlt)))

/-! ## The decision -/

/-- The indices of `Fin 3`. -/
def fin3 : List (Fin 3) :=
  [0, 1, 2]

theorem mem_fin3 (i : Fin 3) : i ∈ fin3 := by
  fin_cases i <;> simp [fin3]

/-- The `Δ`-words of an entry that the decision compares. -/
def entryWords (e : Entry ι) : List (List (ι × Bool)) :=
  e.flatMap fun m => deltaWord m.2 :: (lampPrefixes m.2 ++
    m.1.flatMap fun p => deltaWord p :: lampPrefixes p)

/-- The `Δ`-words of a word that the decision compares. -/
def wordWords (w : List (Gen ι × Bool)) : List (List (ι × Bool)) :=
  fin3.flatMap fun i => fin3.flatMap fun j => entryWords (diffEntry (wordMat w) i j)

/-- All lists of `n` bits. -/
def allBits : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allBits n).flatMap fun l => [false :: l, true :: l]

theorem mem_allBits {n : ℕ} {a : List Bool} : a ∈ allBits n ↔ a.length = n := by
  induction n generalizing a with
  | zero => simp [allBits, List.length_eq_zero_iff]
  | succ n ih =>
    cases a with
    | nil => simp [allBits]
    | cons b l =>
      simp only [allBits, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false,
        List.length_cons, Nat.add_right_cancel_iff, ← ih]
      constructor
      · rintro ⟨l', hl', h | h⟩
        · rw [List.cons.injEq] at h
          rw [h.2]
          exact hl'
        · rw [List.cons.injEq] at h
          rw [h.2]
          exact hl'
      · intro hl
        refine ⟨l, hl, ?_⟩
        cases b
        · exact Or.inl rfl
        · exact Or.inr rfl

section Decision

variable [DecidableEq ι] (E : List (ι × Bool) → List (ι × Bool) → Bool)

/-- The parity of the number of words in a list that `E` declares equal to `q`. -/
def parity (q : List (ι × Bool)) : List (List (ι × Bool)) → Bool
  | [] => false
  | q' :: L => xor (E q' q) (parity q L)

/-- `E`'s test of equality of two words in the letters of `Λ`: the `Δ`-letters agree, and the
lamps agree at every lamp position that occurs. -/
def sameUnit (u u' : List (Option ι × Bool)) : Bool :=
  E (deltaWord u) (deltaWord u') &&
    (lampPrefixes u ++ lampPrefixes u').all fun q =>
      parity E q (lampPrefixes u) == parity E q (lampPrefixes u')

/-- The coordinates `δ` of the factors of an entry, as `Δ`-words. -/
def points (e : Entry ι) : List (List (ι × Bool)) :=
  e.flatMap fun m => m.1.map deltaWord

/-- The bit of a coordinate `γ` in an assignment `a` along `P`. -/
def bitAt (P : List (List (ι × Bool))) (a : List Bool) (γ : List (ι × Bool)) : Bool :=
  a.getD (P.findIdx fun γ' => decide (γ' = γ)) false

/-- The value `∏_{p ∈ F} (x(δ_p) + c_p(δ_p))` of a coefficient at an assignment. -/
def monoBit (P : List (List (ι × Bool))) (a : List Bool) :
    List (List (Option ι × Bool)) → Bool
  | [] => true
  | p :: F => xor (bitAt P a (deltaWord p)) (parity E (deltaWord p) (lampPrefixes p)) &&
      monoBit P a F

/-- An assignment along `P` is consistent when coordinates that `E` declares equal get equal
bits. -/
def consistent (P : List (List (ι × Bool))) (a : List Bool) : Bool :=
  (List.range P.length).all fun i => (List.range P.length).all fun j =>
    !E (P.getD i []) (P.getD j []) || a.getD i false == a.getD j false

/-- The sum, at an assignment, of the coefficients of the monomials with the unit of `m0`. -/
def classSum (P : List (List (ι × Bool))) (a : List Bool) (m0 : Mono ι) : Entry ι → Bool
  | [] => false
  | m :: e => xor (sameUnit E m.2 m0.2 && monoBit E P a m.1) (classSum P a m0 e)

/-- **The decision for an entry**: at every consistent assignment, the coefficients with each
unit sum to zero. -/
def entryZero (e : Entry ι) : Bool :=
  e.all fun m0 => (allBits (points e).length).all fun a =>
    !consistent E (points e) a || !classSum E (points e) a m0 e

/-- **The decision for a word**: every entry of its difference from `I_3` vanishes. -/
def wordTrivial (w : List (Gen ι × Bool)) : Bool :=
  fin3.all fun i => fin3.all fun j => entryZero E (diffEntry (wordMat w) i j)

theorem consistent_eq_true (P : List (List (ι × Bool))) (a : List Bool) :
    consistent E P a = true ↔ ∀ i < P.length, ∀ j < P.length,
      E (P.getD i []) (P.getD j []) = true → a.getD i false = a.getD j false := by
  unfold consistent
  simp only [List.all_eq_true, List.mem_range]
  refine ⟨fun h i hi j hj hij => ?_, fun h i hi j hj => ?_⟩
  · have h1 := h i hi j hj
    rw [hij] at h1
    simpa using h1
  · cases hij : E (P.getD i []) (P.getD j [])
    · rfl
    · simpa using h i hi j hj hij

variable [DecidableEq Δ]

theorem bitZ_parity (q : List (ι × Bool)) (L : List (List (ι × Bool)))
    (hE : ∀ q' ∈ L, E q' q = decide (wordValue t q' = wordValue t q)) :
    bitZ (parity E q L) =
      ((L.filter fun q' => wordValue t q' = wordValue t q).length : ZMod 2) := by
  induction L with
  | nil => rfl
  | cons q' L ih =>
    show bitZ (xor (E q' q) (parity E q L)) = _
    rw [bitZ_xor, ih fun y hy => hE y (List.mem_cons_of_mem _ hy), hE q' List.mem_cons_self]
    by_cases h : wordValue t q' = wordValue t q
    · rw [decide_eq_true h, List.filter_cons_of_pos (by simpa using h), List.length_cons,
        Nat.cast_succ]
      exact add_comm _ _
    · rw [decide_eq_false h, List.filter_cons_of_neg (by simpa using h)]
      exact zero_add _

open Classical in
theorem sameUnit_eq (u u' : List (Option ι × Bool))
    (hE : ∀ a ∈ deltaWord u :: deltaWord u' :: (lampPrefixes u ++ lampPrefixes u'),
      ∀ b ∈ deltaWord u :: deltaWord u' :: (lampPrefixes u ++ lampPrefixes u'),
        E a b = decide (wordValue t a = wordValue t b)) :
    sameUnit E u u' = decide (wordValue (lampGen t) u = wordValue (lampGen t) u') := by
  have key : ∀ q ∈ lampPrefixes u ++ lampPrefixes u',
      ((parity E q (lampPrefixes u) == parity E q (lampPrefixes u')) = true ↔
        lampSum t u (wordValue t q) = lampSum t u' (wordValue t q)) := by
    intro q hq
    have hqm : q ∈ deltaWord u :: deltaWord u' :: (lampPrefixes u ++ lampPrefixes u') :=
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)
    rw [beq_iff_eq, ← bitZ_inj, lampSum_apply, lampSum_apply,
      bitZ_parity t E q _ fun q' hq' => hE q' (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_append.2 (Or.inl hq')))) q hqm,
      bitZ_parity t E q _ fun q' hq' => hE q' (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_append.2 (Or.inr hq')))) q hqm]
  rw [Bool.eq_iff_iff, decide_eq_true_iff, wordValue_lampGen_eq_iff, sameUnit, Bool.and_eq_true,
    List.all_eq_true, hE (deltaWord u) (by simp) (deltaWord u') (by simp), decide_eq_true_iff]
  exact and_congr Iff.rfl
    ⟨fun h q hq => (key q hq).1 (h q hq), fun h q hq => (key q hq).2 (h q hq)⟩

theorem bitZ_monoBit (P : List (List (ι × Bool))) (a : List Bool) (x : LampSpace Δ)
    (F : List (List (Option ι × Bool)))
    (hbit : ∀ p ∈ F, bitZ (bitAt P a (deltaWord p)) = x (wordValue t (deltaWord p)))
    (hE : ∀ p ∈ F, ∀ q' ∈ lampPrefixes p,
      E q' (deltaWord p) = decide (wordValue t q' = wordValue t (deltaWord p))) :
    bitZ (monoBit E P a F) = (F.map fun p => factorFn t p x).prod := by
  induction F with
  | nil => rfl
  | cons p F ih =>
    show bitZ (xor (bitAt P a (deltaWord p)) (parity E (deltaWord p) (lampPrefixes p)) &&
      monoBit E P a F) = _
    rw [bitZ_and, bitZ_xor, hbit p List.mem_cons_self,
      bitZ_parity t E _ _ (hE p List.mem_cons_self), ← lampSum_apply, ← factorFn_apply,
      ih (fun p' hp' => hbit p' (List.mem_cons_of_mem _ hp'))
        (fun p' hp' => hE p' (List.mem_cons_of_mem _ hp')), List.map_cons, List.prod_cons]

open Classical in
theorem bitZ_classSum (P : List (List (ι × Bool))) (a : List Bool) (m0 : Mono ι)
    (x : LampSpace Δ) (e : Entry ι)
    (hsame : ∀ m ∈ e, sameUnit E m.2 m0.2 =
      decide (wordValue (lampGen t) m.2 = wordValue (lampGen t) m0.2))
    (hmono : ∀ m ∈ e, bitZ (monoBit E P a m.1) = monoFn t m x) :
    bitZ (classSum E P a m0 e) =
      (e.map fun m => if wordValue (lampGen t) m.2 = wordValue (lampGen t) m0.2 then
        monoFn t m x else 0).sum := by
  induction e with
  | nil => rfl
  | cons m e ih =>
    show bitZ (xor (sameUnit E m.2 m0.2 && monoBit E P a m.1) (classSum E P a m0 e)) = _
    rw [bitZ_xor, bitZ_and, hsame m List.mem_cons_self, hmono m List.mem_cons_self,
      ih (fun m' hm' => hsame m' (List.mem_cons_of_mem _ hm'))
        (fun m' hm' => hmono m' (List.mem_cons_of_mem _ hm')), List.map_cons, List.sum_cons]
    by_cases h : wordValue (lampGen t) m.2 = wordValue (lampGen t) m0.2
    · rw [decide_eq_true h, if_pos h]
      exact congrArg (· + _) (one_mul _)
    · rw [decide_eq_false h, if_neg h]
      exact congrArg (· + _) (zero_mul _)

open Classical in
/-- **The decision for an entry is correct** (tex l.451–454), when `E` is correct on the `Δ`-words
of the entry. Every consistent assignment is the restriction of a point, as `Ω` is the full shift. -/
theorem entryZero_eq_true_iff (e : Entry ι)
    (hE : ∀ u ∈ entryWords e, ∀ v ∈ entryWords e,
      E u v = decide (wordValue t u = wordValue t v)) :
    entryZero E e = true ↔ entryEval t e = 0 := by
  have hdw : ∀ m ∈ e, deltaWord m.2 ∈ entryWords e := fun m hm =>
    List.mem_flatMap.2 ⟨m, hm, List.mem_cons_self⟩
  have hlp : ∀ m ∈ e, ∀ q ∈ lampPrefixes m.2, q ∈ entryWords e := fun m hm q hq =>
    List.mem_flatMap.2 ⟨m, hm, List.mem_cons_of_mem _ (List.mem_append.2 (Or.inl hq))⟩
  have hfdw : ∀ m ∈ e, ∀ p ∈ m.1, deltaWord p ∈ entryWords e := fun m hm p hp =>
    List.mem_flatMap.2 ⟨m, hm, List.mem_cons_of_mem _ (List.mem_append.2 (Or.inr
      (List.mem_flatMap.2 ⟨p, hp, List.mem_cons_self⟩)))⟩
  have hflp : ∀ m ∈ e, ∀ p ∈ m.1, ∀ q ∈ lampPrefixes p, q ∈ entryWords e :=
    fun m hm p hp q hq => List.mem_flatMap.2 ⟨m, hm, List.mem_cons_of_mem _ (List.mem_append.2
      (Or.inr (List.mem_flatMap.2 ⟨p, hp, List.mem_cons_of_mem _ hq⟩)))⟩
  have hpts : ∀ γ ∈ points e, γ ∈ entryWords e := by
    intro γ hγ
    obtain ⟨m, hm, hγm⟩ := List.mem_flatMap.1 hγ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hγm
    exact hfdw m hm p hp
  have hsame : ∀ m0 ∈ e, ∀ m ∈ e, sameUnit E m.2 m0.2 =
      decide (wordValue (lampGen t) m.2 = wordValue (lampGen t) m0.2) := by
    intro m0 hm0 m hm
    have hsub : ∀ y ∈ deltaWord m.2 :: deltaWord m0.2 :: (lampPrefixes m.2 ++ lampPrefixes m0.2),
        y ∈ entryWords e := by
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hdw m hm
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hdw m0 hm0
      rcases List.mem_append.1 hy with hy | hy
      · exact hlp m hm y hy
      · exact hlp m0 hm0 y hy
    exact sameUnit_eq t E m.2 m0.2 fun y hy z hz => hE y (hsub y hy) z (hsub z hz)
  have hmono : ∀ (a : List Bool) (x : LampSpace Δ),
      (∀ γ ∈ points e, bitZ (bitAt (points e) a γ) = x (wordValue t γ)) →
        ∀ m ∈ e, bitZ (monoBit E (points e) a m.1) = monoFn t m x := by
    intro a x hbit m hm
    rw [monoFn_apply]
    exact bitZ_monoBit t E _ a x m.1
      (fun p hp => hbit _ (List.mem_flatMap.2 ⟨m, hm, List.mem_map.2 ⟨p, hp, rfl⟩⟩))
      (fun p hp q hq => hE q (hflp m hm p hp q hq) _ (hfdw m hm p hp))
  rw [entryEval_eq_zero_iff]
  constructor
  · intro h m0 hm0 x
    have ha : ((points e).map fun γ => decide (x (wordValue t γ) = 1)) ∈
        allBits (points e).length :=
      mem_allBits.2 (List.length_map _)
    have hcons : consistent E (points e)
        ((points e).map fun γ => decide (x (wordValue t γ) = 1)) = true := by
      rw [consistent_eq_true]
      intro i hi j hj hij
      rw [hE _ (hpts _ (getD_mem hi)) _ (hpts _ (getD_mem hj))] at hij
      rw [getD_map_of_lt hi _ [] false, getD_map_of_lt hj _ [] false]
      show decide (x (wordValue t ((points e).getD i [])) = 1) =
        decide (x (wordValue t ((points e).getD j [])) = 1)
      rw [of_decide_eq_true hij]
    have hbit : ∀ γ ∈ points e, bitZ (bitAt (points e)
        ((points e).map fun γ => decide (x (wordValue t γ) = 1)) γ) = x (wordValue t γ) := by
      intro γ hγ
      rw [bitAt, getD_map_findIdx hγ, bitZ_decide]
    have h1 : classSum E (points e) ((points e).map fun γ => decide (x (wordValue t γ) = 1))
        m0 e = false := by
      simpa [hcons] using List.all_eq_true.1 (List.all_eq_true.1 h m0 hm0) _ ha
    rw [← bitZ_classSum t E (points e) _ m0 x e (hsame m0 hm0) (hmono _ x hbit), h1]
    rfl
  · intro h
    refine List.all_eq_true.2 fun m0 hm0 => List.all_eq_true.2 fun a _ => ?_
    by_cases hcons : consistent E (points e) a = true
    · let x : LampSpace Δ := fun h' =>
        bitZ (a.getD ((points e).findIdx fun γ => decide (wordValue t γ = h')) false)
      have hbit : ∀ γ ∈ points e, bitZ (bitAt (points e) a γ) = x (wordValue t γ) := by
        intro γ hγ
        have hi : (points e).findIdx (fun γ' => decide (wordValue t γ' = wordValue t γ)) <
            (points e).length := List.findIdx_lt_length_of_exists ⟨γ, hγ, by simp⟩
        have hj : (points e).findIdx (fun γ' => decide (γ' = γ)) < (points e).length :=
          List.findIdx_lt_length_of_exists ⟨γ, hγ, by simp⟩
        have hpi := of_decide_eq_true (List.findIdx_getElem (w := hi))
        have hpj := of_decide_eq_true (List.findIdx_getElem (w := hj))
        have hcz := (consistent_eq_true E (points e) a).1 hcons _ hi _ hj (by
          rw [hE _ (hpts _ (getD_mem hi)) _ (hpts _ (getD_mem hj)), List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
          simp [hpj, hpi])
        exact congrArg bitZ hcz.symm
      have h2 := h m0 hm0 x
      rw [← bitZ_classSum t E (points e) a m0 x e (hsame m0 hm0) (hmono a x hbit),
        bitZ_eq_zero] at h2
      simp [hcons, h2]
    · simp [Bool.eq_false_iff.2 hcons]

/-- **The decision for a word is correct** (tex l.451–455), when `E` is correct on the `Δ`-words
of the word. -/
theorem wordTrivial_eq_true_iff (w : List (Gen ι × Bool))
    (hE : ∀ u ∈ wordWords w, ∀ v ∈ wordWords w,
      E u v = decide (wordValue t u = wordValue t v)) :
    wordTrivial E w = true ↔ wordValue (gens t) w = 1 := by
  have hsub : ∀ i j, ∀ u ∈ entryWords (diffEntry (wordMat w) i j), u ∈ wordWords w :=
    fun i j u hu => List.mem_flatMap.2 ⟨i, mem_fin3 i, List.mem_flatMap.2 ⟨j, mem_fin3 j, hu⟩⟩
  have hentry : ∀ i j, entryZero E (diffEntry (wordMat w) i j) = true ↔
      entryEval t (diffEntry (wordMat w) i j) = 0 := fun i j =>
    entryZero_eq_true_iff t E _ fun u hu v hv => hE u (hsub i j u hu) v (hsub i j v hv)
  rw [wordValue_gens_eq_one_iff, matEval_eq_one_iff, wordTrivial, List.all_eq_true]
  constructor
  · intro h i j
    exact (hentry i j).1 (List.all_eq_true.1 (h i (mem_fin3 i)) j (mem_fin3 j))
  · intro h i _
    exact List.all_eq_true.2 fun j _ => (hentry i j).2 (h i j)

end Decision

end Host
end Lamplighter
end SimpleKazhdanSofic
end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.Lamplighter.Host.entryEval_eq_zero_iff
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Lamplighter.Host.factorFn_apply
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Lamplighter.Host.entryZero_eq_true_iff
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Lamplighter.Host.wordTrivial_eq_true_iff
