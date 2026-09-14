import GroupApproximation.GroupTheory.LevelShiftDeltaWords
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFSolvableWordProblem
import Mathlib.Computability.Partrec
import Mathlib.Computability.Primrec.List

/-!
# The second choice of `Δ` has solvable word problem

`simple_kazhdan_sofic_group.tex` at origin/main 8b36733d7, section "LEF groups", tex l.440–444:

> From a word in the β^{±1} and h_γ^{±1} one computes the exponent sum ℓ of β, the levels where f changes, namely the
> exponent sums of β before the letters h_γ^{±1}, and the values of f there as words in E. It is trivial if and only if
> ℓ = 0 and these values are trivial, so Δ has solvable word problem.

For generators `s : ι → Γ` with a computable word problem, the generators `levelGen s : Option ι → Perm (Γ × ℤ)` of `Δ`
have a computable word problem.

* The criterion is `gValue_eq_one_iff_tags` (`GroupTheory/LevelShiftDeltaWords`).
* `primrec_shiftPair`, `primrec_hLetters` and `primrec_valueWordAt`: the exponent sum, the tagged letters and the value
  words are primitive recursive. The comparison of tags is done on natural-number pairs.
* `allOk`: the answers of the oracle of `Γ` on the finitely many value words, computed by `Nat.rec` over the list of codes
  (`computable_allOk`).
* `wordProblemOracle_levelGen_eq` and `hasSolvableWordProblem_closure_levelGen`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace LevelShiftDeltaWordProblem

open LevelShiftDelta Encodable

section Words

variable {Γ : Type*} [Group Γ] {ι : Type*} (s : ι → Γ)

theorem wordValue_levelGen (w : List (Option ι × Bool)) : wordValue (levelGen s) w = gValue s w := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    obtain ⟨o, b⟩ := x
    simp only [wordValue, gValue, ih]

theorem wordValue_eq_lValue (u : List (ι × Bool)) : wordValue s u = lValue s u := by
  induction u with
  | nil => rfl
  | cons x u ih =>
    obtain ⟨i, b⟩ := x
    simp only [wordValue, lValue, ih]

end Words

section Primrec

variable {ι : Type*} [Primcodable ι]

/-- One letter of the exponent sum of `β`. -/
def shiftStep (x : Option ι × Bool) (acc : ℕ × ℕ) : ℕ × ℕ :=
  Option.casesOn x.1 (cond x.2 (acc.1 + 1, acc.2) (acc.1, acc.2 + 1)) fun _ => acc

omit [Primcodable ι] in
theorem shiftPair_eq_foldr (w : List (Option ι × Bool)) : shiftPair w = w.foldr shiftStep (0, 0) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    obtain ⟨o, b⟩ := x
    cases o <;> cases b <;> simp [shiftPair, shiftStep, ih]

theorem primrec_shiftStep : Primrec₂ (shiftStep (ι := ι)) := by
  have h1 : Primrec fun a : (Option ι × Bool) × (ℕ × ℕ) => a.1.1 := Primrec.fst.comp Primrec.fst
  have hf : Primrec fun a : (Option ι × Bool) × (ℕ × ℕ) =>
      cond a.1.2 (a.2.1 + 1, a.2.2) (a.2.1, a.2.2 + 1) :=
    Primrec.cond (Primrec.snd.comp Primrec.fst)
      (Primrec.pair (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd))
      (Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.succ.comp (Primrec.snd.comp Primrec.snd)))
  have hg : Primrec₂ fun (a : (Option ι × Bool) × (ℕ × ℕ)) (_ : ι) => a.2 :=
    (Primrec.snd.comp Primrec.fst).to₂
  exact (Primrec.option_casesOn h1 hf hg).of_eq fun a => rfl

theorem primrec_shiftPair : Primrec (shiftPair : List (Option ι × Bool) → ℕ × ℕ) :=
  (Primrec.list_foldr Primrec.id (Primrec.const ((0, 0) : ℕ × ℕ))
    (primrec_shiftStep.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
    fun w => (shiftPair_eq_foldr w).symm

/-- One letter of the tagged letters `h_γ^{±1}`. -/
def lettersStep (x : Option ι × Bool) (acc : List ((ℕ × ℕ) × (ι × Bool))) :
    List ((ℕ × ℕ) × (ι × Bool)) :=
  Option.casesOn x.1
    (cond x.2 (acc.map fun p => ((p.1.1 + 1, p.1.2), p.2)) (acc.map fun p => ((p.1.1, p.1.2 + 1), p.2)))
    fun i => ((0, 0), (i, x.2)) :: acc

omit [Primcodable ι] in
theorem hLetters_eq_foldr (w : List (Option ι × Bool)) : hLetters w = w.foldr lettersStep [] := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    obtain ⟨o, b⟩ := x
    cases o <;> cases b <;> simp [hLetters, lettersStep, ih]

theorem primrec_lettersStep : Primrec₂ (lettersStep (ι := ι)) := by
  have h1 : Primrec fun a : (Option ι × Bool) × List ((ℕ × ℕ) × (ι × Bool)) => a.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hup : Primrec₂ fun (_ : (Option ι × Bool) × List ((ℕ × ℕ) × (ι × Bool)))
      (p : (ℕ × ℕ) × (ι × Bool)) => ((p.1.1 + 1, p.1.2), p.2) :=
    (Primrec.pair (Primrec.pair (Primrec.succ.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))) (Primrec.snd.comp Primrec.snd)).to₂
  have hdown : Primrec₂ fun (_ : (Option ι × Bool) × List ((ℕ × ℕ) × (ι × Bool)))
      (p : (ℕ × ℕ) × (ι × Bool)) => ((p.1.1, p.1.2 + 1), p.2) :=
    (Primrec.pair (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.succ.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))) (Primrec.snd.comp Primrec.snd)).to₂
  have hf : Primrec fun a : (Option ι × Bool) × List ((ℕ × ℕ) × (ι × Bool)) =>
      cond a.1.2 (a.2.map fun p => ((p.1.1 + 1, p.1.2), p.2)) (a.2.map fun p => ((p.1.1, p.1.2 + 1), p.2)) :=
    Primrec.cond (Primrec.snd.comp Primrec.fst) (Primrec.list_map Primrec.snd hup)
      (Primrec.list_map Primrec.snd hdown)
  have hg : Primrec₂ fun (a : (Option ι × Bool) × List ((ℕ × ℕ) × (ι × Bool))) (i : ι) =>
      ((0, 0), (i, a.1.2)) :: a.2 :=
    (Primrec.list_cons.comp
      (Primrec.pair (Primrec.const ((0, 0) : ℕ × ℕ))
        (Primrec.pair Primrec.snd (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
      (Primrec.snd.comp Primrec.fst)).to₂
  exact (Primrec.option_casesOn h1 hf hg).of_eq fun a => rfl

theorem primrec_hLetters : Primrec (hLetters : List (Option ι × Bool) → List ((ℕ × ℕ) × (ι × Bool))) :=
  (Primrec.list_foldr Primrec.id (Primrec.const ([] : List ((ℕ × ℕ) × (ι × Bool))))
    (primrec_lettersStep.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
    fun w => (hLetters_eq_foldr w).symm

/-- The value word at the tag of `p`, with the comparison of tags on natural numbers. -/
def valueWordAt (w : List (Option ι × Bool)) (p : (ℕ × ℕ) × (ι × Bool)) : List (ι × Bool) :=
  (hLetters w).filterMap fun q => if q.1.1 + p.1.2 ≤ p.1.1 + q.1.2 then some q.2 else none

omit [Primcodable ι] in
theorem valueWordAt_eq (w : List (Option ι × Bool)) (p : (ℕ × ℕ) × (ι × Bool)) :
    valueWordAt w p = valueWord w (tagLevel p.1) := by
  unfold valueWordAt valueWord
  refine List.filterMap_congr fun q _ => ?_
  have hiff : q.1.1 + p.1.2 ≤ p.1.1 + q.1.2 ↔ tagLevel q.1 ≤ tagLevel p.1 := by
    simp only [tagLevel]
    omega
  by_cases h : q.1.1 + p.1.2 ≤ p.1.1 + q.1.2
  · rw [if_pos h, if_pos (hiff.1 h)]
  · rw [if_neg h, if_neg fun h' => h (hiff.2 h')]

theorem primrec_valueWordAt : Primrec₂ (valueWordAt (ι := ι)) := by
  have hc : PrimrecPred fun z : (List (Option ι × Bool) × ((ℕ × ℕ) × (ι × Bool))) × ((ℕ × ℕ) × (ι × Bool)) =>
      z.2.1.1 + z.1.2.1.2 ≤ z.1.2.1.1 + z.2.1.2 :=
    Primrec.nat_le.comp
      (Primrec.nat_add.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))
      (Primrec.nat_add.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
  have hg : Primrec₂ fun (a : List (Option ι × Bool) × ((ℕ × ℕ) × (ι × Bool)))
      (q : (ℕ × ℕ) × (ι × Bool)) => if q.1.1 + a.2.1.2 ≤ a.2.1.1 + q.1.2 then some q.2 else none :=
    (Primrec.ite hc (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const none)).to₂
  exact (Primrec.listFilterMap (primrec_hLetters.comp Primrec.fst) hg).of_eq fun a => rfl

/-- The codes of the value words at the tags. -/
def codes (w : List (Option ι × Bool)) : List ℕ :=
  (hLetters w).map fun p => encode (valueWordAt w p)

theorem primrec_codes : Primrec (codes (ι := ι)) :=
  Primrec.list_map primrec_hLetters (Primrec.encode.comp primrec_valueWordAt)

end Primrec

section Query

/-- The oracle answers on a list of codes, combined by `Nat.rec` over the positions. -/
def allOk (o : ℕ → ℕ) (L : List ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k acc => acc && decide (o (L.getD k 0) = 1)) L.length

theorem allOk_rec (o : ℕ → ℕ) (L : List ℕ) : ∀ n : ℕ,
    Nat.rec (motive := fun _ => Bool) true (fun k acc => acc && decide (o (L.getD k 0) = 1)) n = true ↔
      ∀ k < n, o (L.getD k 0) = 1
  | 0 => by simp
  | n + 1 => by
    have hstep : Nat.rec (motive := fun _ => Bool) true (fun k acc => acc && decide (o (L.getD k 0) = 1)) (n + 1) =
        (Nat.rec (motive := fun _ => Bool) true (fun k acc => acc && decide (o (L.getD k 0) = 1)) n &&
          decide (o (L.getD n 0) = 1)) := rfl
    rw [hstep, Bool.and_eq_true, decide_eq_true_eq, allOk_rec o L n]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      by_cases hkn : k < n
      · exact h1 k hkn
      · have hk' : k = n := by omega
        rw [hk']
        exact h2
    · intro h
      exact ⟨fun k hk => h k (by omega), h n (by omega)⟩

theorem allOk_iff (o : ℕ → ℕ) (L : List ℕ) : allOk o L = true ↔ ∀ c ∈ L, o c = 1 := by
  rw [allOk, allOk_rec]
  constructor
  · intro h c hc
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
    have h' := h k hk
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some] at h'
  · intro h k hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    exact h _ (List.getElem_mem hk)

theorem computable_allOk {o : ℕ → ℕ} (ho : Computable o) : Computable (allOk o) := by
  have hq : Computable fun q : List ℕ × (ℕ × Bool) => o (q.1.getD q.2.1 0) :=
    ho.comp ((Primrec.list_getD 0).to_comp.comp Computable.fst (Computable.fst.comp Computable.snd))
  have hd : Computable fun q : List ℕ × (ℕ × Bool) => decide (o (q.1.getD q.2.1 0) = 1) :=
    (PrimrecPred.decide (Primrec.eq.comp Primrec.id (Primrec.const 1))).to_comp.comp hq
  have hstep : Computable₂ fun (L : List ℕ) (p : ℕ × Bool) => p.2 && decide (o (L.getD p.1 0) = 1) :=
    (Primrec.and.to_comp.comp (Computable.snd.comp Computable.snd) hd).to₂
  exact (Computable.nat_rec Computable.list_length (Computable.const true) hstep).of_eq fun L => rfl

variable {ι : Type*} [Primcodable ι]

/-- **The decision** (tex l.440–444): `ℓ = 0` and the oracle of `Γ` answers `1` on every value word at a tag. -/
def decideWord (o : ℕ → ℕ) (w : List (Option ι × Bool)) : Bool :=
  decide ((shiftPair w).1 = (shiftPair w).2) && allOk o (codes w)

theorem computable_decideWord {o : ℕ → ℕ} (ho : Computable o) : Computable (decideWord (ι := ι) o) :=
  (Primrec.and.to_comp.comp
    (PrimrecPred.decide (Primrec.eq.comp (Primrec.fst.comp primrec_shiftPair)
      (Primrec.snd.comp primrec_shiftPair))).to_comp
    ((computable_allOk ho).comp primrec_codes.to_comp)).of_eq fun _ => rfl

variable (ι)

/-- The decision on codes of words. -/
def decideCode (o : ℕ → ℕ) (n : ℕ) : ℕ :=
  cond (Option.casesOn (decode n : Option (List (Option ι × Bool))) false (decideWord o)) 1 0

theorem computable_decideCode {o : ℕ → ℕ} (ho : Computable o) : Computable (decideCode ι o) :=
  (Computable.cond
    (Computable.option_casesOn Computable.decode (Computable.const false)
      ((computable_decideWord ho).comp Computable.snd).to₂)
    (Computable.const 1) (Computable.const 0)).of_eq fun _ => rfl

end Query

section Correctness

variable {Γ : Type*} [Group Γ] {ι : Type*} [Primcodable ι] (s : ι → Γ)

/-- The answers of the word problem of `Γ`. -/
noncomputable def oracleAnswer (n : ℕ) : ℕ :=
  (wordProblemOracle s n).get (by simp [wordProblemOracle])

theorem computable_oracleAnswer (h : Partrec (wordProblemOracle s)) : Computable (oracleAnswer s) :=
  h.of_eq_tot fun _ => Part.get_mem _

theorem oracleAnswer_encode (u : List (ι × Bool)) :
    oracleAnswer s (encode u) = 1 ↔ wordValue s u = 1 := by
  unfold oracleAnswer wordProblemOracle
  simp only [Part.get_some]
  split_ifs with hex
  · obtain ⟨w, hw, hv⟩ := hex
    rw [encodek, Option.some_inj] at hw
    subst hw
    simp [hv]
  · simp only [false_iff]
    intro hv
    exact hex ⟨u, encodek u, hv⟩

/-- **The word problem of `Δ` is decided by `decideCode` from the answers of the word problem of `Γ`**
(tex l.440–444). -/
theorem wordProblemOracle_levelGen_eq :
    wordProblemOracle (levelGen s) = fun n => Part.some (decideCode ι (oracleAnswer s) n) := by
  funext n
  unfold wordProblemOracle decideCode
  congr 1
  cases hd : (decode n : Option (List (Option ι × Bool))) with
  | none =>
    rw [if_neg (by rintro ⟨w, hw, -⟩; cases hw)]
    rfl
  | some w =>
    have key : wordValue (levelGen s) w = 1 ↔ decideWord (oracleAnswer s) w = true := by
      rw [wordValue_levelGen, gValue_eq_one_iff_tags, decideWord, Bool.and_eq_true, decide_eq_true_eq,
        allOk_iff, codes, List.forall_mem_map]
      refine and_congr_right' (forall₂_congr fun p _ => ?_)
      rw [oracleAnswer_encode, valueWordAt_eq, wordValue_eq_lValue]
    by_cases hw : wordValue (levelGen s) w = 1
    · rw [if_pos ⟨w, rfl, hw⟩]
      simp [key.1 hw]
    · rw [if_neg (by rintro ⟨w', hw', hv⟩; cases Option.some_injective _ hw'; exact hw hv)]
      simp [Bool.eq_false_iff.2 fun h => hw (key.2 h)]

end Correctness

/-- **`Δ` has solvable word problem** (tex l.444): for finitely many generators of `Γ` with computable word problem, the
generators `β` and `h_γ` of `Δ = ⟨β, h_γ⟩` have computable word problem. -/
theorem hasSolvableWordProblem_closure_levelGen {Γ : Type} [Group Γ] {ι : Type} [Primcodable ι] [Finite ι]
    (s : ι → Γ) (hs : Partrec (wordProblemOracle s)) :
    HasSolvableWordProblem ↥(Subgroup.closure (Set.range (levelGen s))) := by
  let H := Subgroup.closure (Set.range (levelGen s))
  let t : Option ι → H := fun o => ⟨levelGen s o, Subgroup.subset_closure ⟨o, rfl⟩⟩
  refine ⟨Option ι, inferInstance, inferInstance, t, ?_, ?_⟩
  · have hpre : Set.range t = ((↑) : H → Equiv.Perm (Γ × ℤ)) ⁻¹' Set.range (levelGen s) := by
      ext x
      constructor
      · rintro ⟨o, rfl⟩
        exact ⟨o, rfl⟩
      · rintro ⟨o, ho⟩
        exact ⟨o, Subtype.ext ho⟩
    rw [hpre]
    exact Subgroup.closure_closure_coe_preimage
  · have hcomp : (H.subtype ∘ t) = levelGen s := funext fun _ => rfl
    rw [← wordProblemOracle_comp_injective t H.subtype Subtype.val_injective, hcomp,
      wordProblemOracle_levelGen_eq]
    exact (computable_decideCode ι (computable_oracleAnswer s hs)).partrec

end LevelShiftDeltaWordProblem
end SimpleKazhdanSofic
end GroupApproximation
