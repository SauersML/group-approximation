import GroupApproximation.Manuscript.SimpleKazhdanSofic.SturmianQueries
import GroupApproximation.Computability.OracleTruthTable
import GroupApproximation.Meta.AxiomGuard

/-!
# The slope and the language of a Sturmian subshift compute each other

`simple_kazhdan_sofic_group.tex` (origin tip 696c4b602), proof of `cor:wp`, second paragraph:

> ... and `α` computes `L(X_α)`. Such a word has `⌊θ + mα⌋` ones, within `1` of `mα`, so `L(X_α)`
> computes `α`.

Both reductions are truth tables in `OracleTruthTable.turingReducible_of_truthTable`, over the cut
oracle `slopeOracle α n = [a < bα]` for `n = Nat.pair a b`.
* `L(X_α)` computes `α`: for `b ≥ 1`, `a < bα` exactly when every word of length `b` of `X_α` has
  at least `a` ones (`natCast_lt_mul_iff_allWords`), so the queries are all words of length `b`.
* `α` computes `L(X_α)`: `v` is a word exactly when `s_k - s_l - 1 < (k - l)α` for all `k, l ≤ |v|`
  (`mem_language_sturmian_iff_pairs`). The query for `l < k` is `s_k - s_l - 1 < (k - l)α`. For
  `k < l` it is `s_l - s_k + 1 < (l - k)α`, whose negation is the needed strict inequality because
  `α` is irrational.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open Encodable SturmianQueries

/-- **Proof of `cor:wp`, second paragraph: "`α` computes `L(X_α)`".** -/
def PrintedSlopeComputesSturmianLanguage : Prop :=
  ∀ α : ℝ, Irrational α → 0 < α → α < 1 →
    TuringReducible (languageOracle (sturmianSubshift α)) (slopeOracle α)

/-- **Proof of `cor:wp`, second paragraph: "`L(X_α)` computes `α`".** -/
def PrintedSturmianLanguageComputesSlope : Prop :=
  ∀ α : ℝ, Irrational α → 0 < α → α < 1 →
    TuringReducible (slopeOracle α) (languageOracle (sturmianSubshift α))

namespace SturmianComputability

variable (α : ℝ)

/-- The values of the slope oracle. -/
noncomputable def slopeValue (n : ℕ) : ℕ :=
  (slopeOracle α n).get trivial

/-- The values of the language oracle of `X_α`. -/
noncomputable def languageValue (n : ℕ) : ℕ :=
  (languageOracle (sturmianSubshift α) n).get trivial

theorem slopeValue_pair_eq_one_iff (x y : ℕ) :
    slopeValue α (Nat.pair x y) = 1 ↔ (x : ℝ) < (y : ℝ) * α := by
  unfold slopeValue slopeOracle
  simp only [Part.get_some, Nat.unpair_pair]
  by_cases h : (x : ℝ) < (y : ℝ) * α
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]
    exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' h⟩

theorem slopeValue_pair_eq_zero_iff (x y : ℕ) :
    slopeValue α (Nat.pair x y) = 0 ↔ ¬ (x : ℝ) < (y : ℝ) * α := by
  unfold slopeValue slopeOracle
  simp only [Part.get_some, Nat.unpair_pair]
  by_cases h : (x : ℝ) < (y : ℝ) * α
  · rw [if_pos h]
    exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h h'⟩
  · rw [if_neg h]
    exact ⟨fun _ => h, fun _ => rfl⟩

open Classical in
theorem languageValue_encode (w : List Bool) :
    languageValue α (encode w) = if w ∈ language (sturmianSubshift α) then 1 else 0 := by
  unfold languageValue languageOracle
  simp only [Part.get_some]
  by_cases h : w ∈ language (sturmianSubshift α)
  · rw [if_pos ⟨w, Encodable.encodek w, h⟩, if_pos h]
  · rw [if_neg h, if_neg]
    rintro ⟨v, hv, hv'⟩
    exact h (Option.some.inj ((Encodable.encodek w).symm.trans hv) ▸ hv')

theorem natCast_ne_mul (hα : Irrational α) {c d : ℕ} (hd : 0 < d) : (c : ℝ) ≠ (d : ℝ) * α := by
  intro h
  apply hα
  refine ⟨(c : ℚ) / d, ?_⟩
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast, h]
  exact mul_div_cancel_left₀ α hd'

section LanguageComputesSlope

/-- The answer `m` for the word `w` says that `w ∉ L(X_α)`, or `w` has at least `a` ones. -/
def wordOk (a b : ℕ) (w : List Bool) (m : ℕ) : Bool :=
  decide (m = 0) || decide (a ≤ prefixOnes w b)

theorem wordOk_iff (a b : ℕ) (w : List Bool) :
    wordOk a b w (languageValue α (encode w)) = true ↔
      (w ∈ language (sturmianSubshift α) → a ≤ prefixOnes w b) := by
  rw [languageValue_encode]
  by_cases h : w ∈ language (sturmianSubshift α)
  · rw [if_pos h]
    simp [wordOk, h]
  · rw [if_neg h]
    simp [wordOk, h]

theorem foldl_wordOk (a b : ℕ) :
    ((allWords b).foldl (fun s w => (s.1 && wordOk a b w (s.2.head?.getD 0), s.2.tail))
        (true, ((allWords b).map encode).map (languageValue α))).1 = true ↔
      ∀ w ∈ allWords b, w ∈ language (sturmianSubshift α) → a ≤ prefixOnes w b := by
  have h := foldl_answers (wordOk a b) (languageValue α ∘ encode) (allWords b) true []
  rw [List.append_nil] at h
  rw [List.map_map, h]
  rw [Bool.true_and, List.all_eq_true]
  exact forall₂_congr fun w _ => wordOk_iff α a b w

theorem turingReducible_slope_language (hα : Irrational α) (hα0 : 0 < α) (hα1 : α < 1) :
    TuringReducible (slopeOracle α) (languageOracle (sturmianSubshift α)) := by
  refine OracleTruthTable.turingReducible_of_truthTable (gt := languageValue α) (fun _ => rfl)
    (Q := fun n => (allWords (Nat.unpair n).2).map encode)
    (D := fun n ans => if (Nat.unpair n).2 = 0 then 0 else
      cond ((allWords (Nat.unpair n).2).foldl
        (fun s w => (s.1 && wordOk (Nat.unpair n).1 (Nat.unpair n).2 w (s.2.head?.getD 0),
          s.2.tail)) (true, ans)).1 1 0) ?_ ?_ fun n => ?_
  · exact Primrec.list_map (primrec_allWords.comp (Primrec.snd.comp Primrec.unpair))
      (Primrec.encode.comp Primrec.snd)
  · have hb : Primrec fun p : ℕ × List ℕ => (Nat.unpair p.1).2 :=
      Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)
    have ha : Primrec fun p : ℕ × List ℕ => (Nat.unpair p.1).1 :=
      Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)
    have hans : Primrec fun q : (ℕ × List ℕ) × ((Bool × List ℕ) × List Bool) =>
        q.2.1.2.head?.getD 0 :=
      Primrec.option_getD.comp (Primrec.list_head?.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))) (Primrec.const 0)
    have hok : Primrec fun q : (ℕ × List ℕ) × ((Bool × List ℕ) × List Bool) =>
        wordOk (Nat.unpair q.1.1).1 (Nat.unpair q.1.1).2 q.2.2 (q.2.1.2.head?.getD 0) :=
      Primrec.or.comp (PrimrecPred.decide (Primrec.eq.comp hans (Primrec.const 0)))
        (PrimrecPred.decide (Primrec.nat_le.comp (ha.comp Primrec.fst)
          (primrec_prefixOnes.comp (Primrec.snd.comp Primrec.snd) (hb.comp Primrec.fst))))
    have hstep : Primrec₂ fun (p : ℕ × List ℕ) (q : (Bool × List ℕ) × List Bool) =>
        (q.1.1 && wordOk (Nat.unpair p.1).1 (Nat.unpair p.1).2 q.2 (q.1.2.head?.getD 0),
          q.1.2.tail) :=
      Primrec.pair (Primrec.and.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)) hok)
        (Primrec.list_tail.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
    exact Primrec.ite (Primrec.eq.comp hb (Primrec.const 0)) (Primrec.const 0)
      (Primrec.cond (Primrec.fst.comp (Primrec.list_foldl (primrec_allWords.comp hb)
        (Primrec.pair (Primrec.const true) Primrec.snd) hstep)) (Primrec.const 1)
        (Primrec.const 0))
  · unfold slopeOracle
    congr 1
    generalize (Nat.unpair n).1 = a
    generalize (Nat.unpair n).2 = b
    by_cases hb : b = 0
    · subst hb
      have h0 : ¬ ((a : ℝ) < 0) := not_lt.2 (Nat.cast_nonneg a)
      simp [h0]
    · have key := (foldl_wordOk α a b).trans
        (natCast_lt_mul_iff_allWords α hα hα0 hα1 a (Nat.pos_of_ne_zero hb)).symm
      rw [if_neg hb]
      by_cases h : (a : ℝ) < (b : ℝ) * α
      · simp only [if_pos h, key.2 h, cond_true]
      · simp only [if_neg h, Bool.eq_false_iff.2 fun ht => h (key.1 ht), cond_false]

end LanguageComputesSlope

section SlopeComputesLanguage

/-- The query for the pair `(k, l)`, as a code `Nat.pair a b` of `a < bα`: `s_k - s_l - 1 < (k - l)α`
when `l < k`, and `s_l - s_k + 1 < (l - k)α` otherwise. -/
def queryCode (v : List Bool) (p : ℕ × ℕ) : ℕ :=
  if p.2 < p.1 then Nat.pair (prefixOnes v p.1 - prefixOnes v p.2 - 1) (p.1 - p.2)
  else Nat.pair (prefixOnes v p.2 - prefixOnes v p.1 + 1) (p.2 - p.1)

/-- The decision for the pair `(k, l)` from the answer `m` to its query. -/
def pairOk (p : ℕ × ℕ) (m : ℕ) : Bool :=
  if p.2 < p.1 then decide (m = 1) else if p.1 = p.2 then true else decide (m = 0)

theorem pairOk_iff (hα : Irrational α) (hα0 : 0 < α) (v : List Bool) (p : ℕ × ℕ) :
    pairOk p (slopeValue α (queryCode v p)) = true ↔
      (prefixOnes v p.1 : ℝ) - prefixOnes v p.2 - 1 < ((p.1 : ℝ) - p.2) * α := by
  obtain ⟨k, l⟩ := p
  dsimp only [pairOk, queryCode]
  rcases lt_trichotomy l k with hlk | rfl | hkl
  · rw [if_pos hlk, if_pos hlk, decide_eq_true_iff, slopeValue_pair_eq_one_iff,
      Nat.cast_sub hlk.le]
    have hmono := prefixOnes_mono v hlk.le
    have hpos : (0 : ℝ) < ((k : ℝ) - l) * α :=
      mul_pos (sub_pos.2 (by exact_mod_cast hlk)) hα0
    rcases Nat.eq_or_lt_of_le hmono with heq | hlt
    · rw [heq, Nat.sub_self, Nat.zero_sub, Nat.cast_zero]
      exact ⟨fun _ => by linarith, fun _ => hpos⟩
    · rw [Nat.cast_sub (by omega : 1 ≤ prefixOnes v k - prefixOnes v l), Nat.cast_sub hmono,
        Nat.cast_one]
  · rw [if_neg (lt_irrefl _), if_pos rfl]
    simp
  · rw [if_neg (not_lt.2 hkl.le), if_neg (not_lt.2 hkl.le), if_neg hkl.ne, decide_eq_true_iff,
      slopeValue_pair_eq_zero_iff]
    have hmono := prefixOnes_mono v hkl.le
    have hne := natCast_ne_mul α hα (c := prefixOnes v l - prefixOnes v k + 1) (d := l - k)
      (by omega)
    rw [Nat.cast_add, Nat.cast_sub hmono, Nat.cast_sub hkl.le, Nat.cast_one] at hne
    rw [Nat.cast_add, Nat.cast_sub hmono, Nat.cast_sub hkl.le, Nat.cast_one]
    have hneg : ((l : ℝ) - k) * α = -(((k : ℝ) - l) * α) := by ring
    constructor
    · intro h
      have h' := lt_of_le_of_ne (not_lt.1 h) hne.symm
      linarith
    · intro h
      exact not_lt.2 (by linarith)

theorem foldl_pairOk (v : List Bool) :
    ((pairsUpTo v.length).foldl (fun s p => (s.1 && pairOk p (s.2.head?.getD 0), s.2.tail))
        (true, ((pairsUpTo v.length).map (queryCode v)).map (slopeValue α))).1 = true ↔
      ∀ p ∈ pairsUpTo v.length, pairOk p (slopeValue α (queryCode v p)) = true := by
  have h := foldl_answers pairOk (slopeValue α ∘ queryCode v) (pairsUpTo v.length) true []
  rw [List.append_nil] at h
  rw [List.map_map, h]
  rw [Bool.true_and, List.all_eq_true]
  exact Iff.rfl

theorem all_pairOk_iff (hα : Irrational α) (hα0 : 0 < α) (hα1 : α < 1) (v : List Bool) :
    (∀ p ∈ pairsUpTo v.length, pairOk p (slopeValue α (queryCode v p)) = true) ↔
      v ∈ language (sturmianSubshift α) := by
  rw [mem_language_sturmian_iff_pairs α hα0 hα1 v]
  constructor
  · intro h k l hk hl
    exact (pairOk_iff α hα hα0 v (k, l)).1 (h (k, l) (mem_pairsUpTo.2 ⟨hk, hl⟩))
  · intro h p hp
    exact (pairOk_iff α hα hα0 v p).2 (h p.1 p.2 (mem_pairsUpTo.1 hp).1 (mem_pairsUpTo.1 hp).2)

theorem primrec₂_queryCode : Primrec₂ queryCode := by
  have s₁ : Primrec fun x : List Bool × (ℕ × ℕ) => prefixOnes x.1 x.2.1 :=
    primrec_prefixOnes.comp Primrec.fst (Primrec.fst.comp Primrec.snd)
  have s₂ : Primrec fun x : List Bool × (ℕ × ℕ) => prefixOnes x.1 x.2.2 :=
    primrec_prefixOnes.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  have k₁ : Primrec fun x : List Bool × (ℕ × ℕ) => x.2.1 := Primrec.fst.comp Primrec.snd
  have l₁ : Primrec fun x : List Bool × (ℕ × ℕ) => x.2.2 := Primrec.snd.comp Primrec.snd
  exact Primrec.ite (Primrec.nat_lt.comp l₁ k₁)
    (Primrec₂.natPair.comp (Primrec.nat_sub.comp (Primrec.nat_sub.comp s₁ s₂) (Primrec.const 1))
      (Primrec.nat_sub.comp k₁ l₁))
    (Primrec₂.natPair.comp (Primrec.nat_add.comp (Primrec.nat_sub.comp s₂ s₁) (Primrec.const 1))
      (Primrec.nat_sub.comp l₁ k₁))

theorem primrec₂_pairOk : Primrec₂ pairOk := by
  have k₁ : Primrec fun x : (ℕ × ℕ) × ℕ => x.1.1 := Primrec.fst.comp Primrec.fst
  have l₁ : Primrec fun x : (ℕ × ℕ) × ℕ => x.1.2 := Primrec.snd.comp Primrec.fst
  exact Primrec.ite (Primrec.nat_lt.comp l₁ k₁)
    (PrimrecPred.decide (Primrec.eq.comp Primrec.snd (Primrec.const 1)))
    (Primrec.ite (Primrec.eq.comp k₁ l₁) (Primrec.const true)
      (PrimrecPred.decide (Primrec.eq.comp Primrec.snd (Primrec.const 0))))

theorem turingReducible_language_slope (hα : Irrational α) (hα0 : 0 < α) (hα1 : α < 1) :
    TuringReducible (languageOracle (sturmianSubshift α)) (slopeOracle α) := by
  have hv : Primrec fun n => (decode (α := List Bool) n).getD [] :=
    Primrec.option_getD.comp Primrec.decode (Primrec.const [])
  refine OracleTruthTable.turingReducible_of_truthTable (gt := slopeValue α) (fun _ => rfl)
    (Q := fun n => (pairsUpTo ((decode (α := List Bool) n).getD []).length).map
      (queryCode ((decode (α := List Bool) n).getD [])))
    (D := fun n ans => cond (decode (α := List Bool) n).isSome
      (cond ((pairsUpTo ((decode (α := List Bool) n).getD []).length).foldl
        (fun s p => (s.1 && pairOk p (s.2.head?.getD 0), s.2.tail)) (true, ans)).1 1 0) 0)
    ?_ ?_ fun n => ?_
  · exact Primrec.list_map (primrec_pairsUpTo.comp (Primrec.list_length.comp hv))
      (primrec₂_queryCode.comp (hv.comp Primrec.fst) Primrec.snd)
  · have hstep : Primrec₂ fun (_ : ℕ × List ℕ) (q : (Bool × List ℕ) × (ℕ × ℕ)) =>
        (q.1.1 && pairOk q.2 (q.1.2.head?.getD 0), q.1.2.tail) :=
      Primrec.pair (Primrec.and.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (primrec₂_pairOk.comp (Primrec.snd.comp Primrec.snd)
          (Primrec.option_getD.comp (Primrec.list_head?.comp
            (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))) (Primrec.const 0))))
        (Primrec.list_tail.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
    exact Primrec.cond (Primrec.option_isSome.comp (Primrec.decode.comp Primrec.fst))
      (Primrec.cond (Primrec.fst.comp (Primrec.list_foldl
        (primrec_pairsUpTo.comp (Primrec.list_length.comp (hv.comp Primrec.fst)))
        (Primrec.pair (Primrec.const true) Primrec.snd) hstep)) (Primrec.const 1)
        (Primrec.const 0)) (Primrec.const 0)
  · cases hd : (decode n : Option (List Bool)) with
    | none =>
      simp only [Option.isSome_none, cond_false]
      show Part.some _ = Part.some 0
      rw [if_neg fun ⟨v, hv', _⟩ => Option.some_ne_none v (hv'.symm.trans hd)]
    | some v =>
      simp only [Option.isSome_some, Option.getD_some, cond_true]
      by_cases hmem : v ∈ language (sturmianSubshift α)
      · rw [(foldl_pairOk α v).2 ((all_pairOk_iff α hα hα0 hα1 v).2 hmem), cond_true]
        show Part.some _ = Part.some 1
        rw [if_pos ⟨v, hd, hmem⟩]
      · rw [Bool.eq_false_iff.2 fun ht =>
          hmem ((all_pairOk_iff α hα hα0 hα1 v).1 ((foldl_pairOk α v).1 ht)), cond_false]
        show Part.some _ = Part.some 0
        rw [if_neg fun ⟨v', hv', hv''⟩ => by
          obtain rfl := Option.some.inj (hd.symm.trans hv')
          exact hmem hv'']

end SlopeComputesLanguage

/-- **Proof of `cor:wp`, second paragraph: "`L(X_α)` computes `α`".** -/
theorem printedSturmianLanguageComputesSlope : PrintedSturmianLanguageComputesSlope :=
  fun α hα hα0 hα1 => turingReducible_slope_language α hα hα0 hα1

/-- **Proof of `cor:wp`, second paragraph: "`α` computes `L(X_α)`".** -/
theorem printedSlopeComputesSturmianLanguage : PrintedSlopeComputesSturmianLanguage :=
  fun α hα hα0 hα1 => turingReducible_language_slope α hα hα0 hα1

#audit_closed_axioms printedSturmianLanguageComputesSlope
#audit_closed_axioms printedSlopeComputesSturmianLanguage

end SturmianComputability

end SimpleKazhdanSofic
end GroupApproximation
