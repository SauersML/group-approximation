import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterHostCriterion
import GroupApproximation.Computability.OracleTruthTable

/-!
# The word problem of `G_Δ` is solvable

`simple_kazhdan_sofic_group.tex` at 8b36733d7, section "LEF groups", l.455:

> So $G_\Delta$ has solvable word problem.

For generators `t : ι → Δ` with computable word problem, the generators `gens t` of `G_Δ` have a
word problem Turing reducible to that of `t`, by a truth-table reduction
(`OracleTruthTable.turingReducible_of_truthTable`).

* The queries on a word `w`: the words `u⁻¹v` for all `Δ`-words `u, v` that the decision compares
  (`queryWords`).
* The decision: `wordTrivial` with the test of equality `ansE` read off the answers.
  `ansE_answers`: on the answers of the word problem of `Δ` it is correct on those words, so
  `wordTrivial_eq_true_iff` applies (`wordProblemOracle_gens`).
* The primitive recursive layer: every function of letters is primitive recursive, as `ι` is finite.
* `printedLamplighterHostSolvableWordProblem`: `G_Δ` has solvable word problem when `Δ` has.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace Lamplighter
namespace Host

open Encodable

variable {ι : Type} [Primcodable ι] [DecidableEq ι]

/-! ## The truth table -/

/-- The queries: the words `u⁻¹v`, for all `Δ`-words `u, v` that the decision compares. -/
def queryWords (w : List (Gen ι × Bool)) : List (List (ι × Bool)) :=
  (wordWords w).flatMap fun u => (wordWords w).map fun v => wordInv u ++ v

/-- The codes of the queries. -/
def queryCodes (w : List (Gen ι × Bool)) : List ℕ :=
  (queryWords w).map encode

/-- The test of equality of `Δ`-words read off the answers `ans` to the queries. -/
def ansE (w : List (Gen ι × Bool)) (ans : List ℕ) (u v : List (ι × Bool)) : Bool :=
  decide (ans.getD ((queryCodes w).findIdx fun k => decide (k = encode (wordInv u ++ v))) 0 = 1)

/-- The queries on an input code. -/
def hostQueries (n : ℕ) : List ℕ :=
  ((decode n : Option (List (Gen ι × Bool))).map queryCodes).getD []

/-- The decision on an input code, from the answers. -/
def hostDecide (n : ℕ) (ans : List ℕ) : ℕ :=
  ((decode n : Option (List (Gen ι × Bool))).map fun w =>
    bif wordTrivial (ansE w ans) w then 1 else 0).getD 0

variable {Δ : Type} [Group Δ]

open Classical in
/-- The total answers of the word problem of `Δ` in the generators `t`. -/
noncomputable def answer (t : ι → Δ) (q : ℕ) : ℕ :=
  if ∃ v : List (ι × Bool), decode q = some v ∧ wordValue t v = 1 then 1 else 0

open Classical in
theorem answer_encode (t : ι → Δ) (v : List (ι × Bool)) :
    answer t (encode v) = if wordValue t v = 1 then 1 else 0 := by
  unfold answer
  by_cases h : wordValue t v = 1
  · rw [if_pos ⟨v, encodek v, h⟩, if_pos h]
  · rw [if_neg ?_, if_neg h]
    rintro ⟨w, hw, hw'⟩
    exact h (Option.some.inj ((encodek v).symm.trans hw) ▸ hw')

/-- **The answers decide equality** on the `Δ`-words of `w`. -/
theorem ansE_answers [DecidableEq Δ] (t : ι → Δ) (w : List (Gen ι × Bool))
    {u v : List (ι × Bool)} (hu : u ∈ wordWords w) (hv : v ∈ wordWords w) :
    ansE w ((queryCodes w).map (answer t)) u v = decide (wordValue t u = wordValue t v) := by
  have hmem : encode (wordInv u ++ v) ∈ queryCodes w :=
    List.mem_map.2 ⟨wordInv u ++ v, List.mem_flatMap.2 ⟨u, hu, List.mem_map.2 ⟨v, hv, rfl⟩⟩, rfl⟩
  rw [ansE, getD_map_findIdx hmem, answer_encode]
  simp only [wordValue_append, wordValue_wordInv, inv_mul_eq_one]
  by_cases h : wordValue t u = wordValue t v <;> simp [h]

/-- **The oracle of `G_Δ` from the answers of `Δ`**: on every input, the word problem of `gens t`
is the decision applied to the answers of `t` to the queries. -/
theorem wordProblemOracle_gens [DecidableEq Δ] (t : ι → Δ) (n : ℕ) :
    wordProblemOracle (gens t) n =
      Part.some (hostDecide n ((hostQueries (ι := ι) n).map (answer t))) := by
  cases hd : (decode n : Option (List (Gen ι × Bool))) with
  | none =>
    simp [wordProblemOracle, hostDecide, hd]
  | some w =>
    have hq : (hostQueries (ι := ι) n).map (answer t) = (queryCodes w).map (answer t) := by
      simp [hostQueries, hd]
    have htriv := wordTrivial_eq_true_iff t (ansE w ((queryCodes w).map (answer t))) w
      fun u hu v hv => ansE_answers t w hu hv
    rw [hq]
    by_cases h : wordValue (gens t) w = 1
    · have ht := htriv.2 h
      simp [wordProblemOracle, hostDecide, hd, h, ht]
    · have ht := Bool.eq_false_iff.2 (mt htriv.1 h)
      simp [wordProblemOracle, hostDecide, hd, h, ht]

/-! ## Primitive recursion -/

section Primrec

variable [Finite ι]

theorem all_eq_foldr {α : Type*} (l : List α) (p : α → Bool) :
    l.all p = l.foldr (fun y b => p y && b) true := by
  induction l with
  | nil => rfl
  | cons y l ih => rw [List.all_cons, ih, List.foldr_cons]

theorem primrec_xor : Primrec₂ (xor : Bool → Bool → Bool) :=
  Primrec.dom_finite fun p : Bool × Bool => xor p.1 p.2

theorem primrec_beq_bool : Primrec₂ fun a b : Bool => a == b :=
  Primrec.dom_finite fun p : Bool × Bool => p.1 == p.2

/-- The `Δ`-letters of a letter of `Λ`. -/
def letters (x : Option ι × Bool) : List (ι × Bool) :=
  (x.1.map fun i => (i, x.2)).toList

theorem deltaWord_eq_flatMap (w : List (Option ι × Bool)) :
    deltaWord w = w.flatMap letters := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    obtain ⟨o, b⟩ := x
    cases o with
    | none => exact ih
    | some i => exact congrArg ((i, b) :: ·) ih

theorem lampPrefixes_eq_foldr (w : List (Option ι × Bool)) :
    lampPrefixes w = w.foldr (fun x rest =>
      bif x.1.isSome then rest.map (letters x ++ ·) else [] :: rest) [] := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    obtain ⟨o, b⟩ := x
    cases o with
    | none => exact congrArg ([] :: ·) ih
    | some i => exact congrArg (List.map ((i, b) :: ·)) ih

theorem primrec_letters : Primrec (letters : Option ι × Bool → List (ι × Bool)) :=
  Primrec.dom_finite _

theorem primrec_deltaWord : Primrec (deltaWord : List (Option ι × Bool) → List (ι × Bool)) := by
  have hg : Primrec₂ fun (_ : List (Option ι × Bool)) (x : Option ι × Bool) => letters x :=
    primrec_letters.comp Primrec.snd
  exact (Primrec.list_flatMap Primrec.id hg).of_eq fun w => (deltaWord_eq_flatMap w).symm

theorem primrec_lampPrefixes :
    Primrec (lampPrefixes : List (Option ι × Bool) → List (List (ι × Bool))) := by
  have hmap : Primrec₂ fun (q : List (Option ι × Bool) × (Option ι × Bool) ×
      List (List (ι × Bool))) (p : List (ι × Bool)) => letters q.2.1 ++ p :=
    Primrec.list_append.comp
      (primrec_letters.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd
  have hstep : Primrec₂ fun (_ : List (Option ι × Bool))
      (p : (Option ι × Bool) × List (List (ι × Bool))) =>
      bif p.1.1.isSome then p.2.map (letters p.1 ++ ·) else [] :: p.2 :=
    Primrec.cond
      ((Primrec.dom_finite fun x : Option ι × Bool => x.1.isSome).comp
        (Primrec.fst.comp Primrec.snd))
      (Primrec.list_map (Primrec.snd.comp Primrec.snd) hmap)
      (Primrec.list_cons.comp (Primrec.const []) (Primrec.snd.comp Primrec.snd))
  exact (Primrec.list_foldr Primrec.id (Primrec.const []) hstep).of_eq fun w =>
    (lampPrefixes_eq_foldr w).symm

theorem primrec_wordInv : Primrec (wordInv : List (ι × Bool) → List (ι × Bool)) := by
  have hg : Primrec₂ fun (_ : List (ι × Bool)) (x : ι × Bool) => (x.1, !x.2) :=
    Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.not.comp (Primrec.snd.comp Primrec.snd))
  exact (Primrec.list_reverse.comp (Primrec.list_map Primrec.id hg)).of_eq fun _ => rfl

theorem primrec_monoMul : Primrec₂ (monoMul : Mono ι → Mono ι → Mono ι) := by
  have hg : Primrec₂ fun (p : Mono ι × Mono ι) (y : List (Option ι × Bool)) => p.1.2 ++ y :=
    Primrec.list_append.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
  exact (Primrec.pair (Primrec.list_append.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.list_map (Primrec.fst.comp Primrec.snd) hg))
    (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))).of_eq
    fun _ => rfl

theorem primrec_entryMul : Primrec₂ (entryMul : Entry ι → Entry ι → Entry ι) := by
  have hin : Primrec₂ fun (q : (Entry ι × Entry ι) × Mono ι) (m' : Mono ι) => monoMul q.2 m' :=
    primrec_monoMul.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hg : Primrec₂ fun (p : Entry ι × Entry ι) (m : Mono ι) => p.2.map (monoMul m) :=
    Primrec.list_map (Primrec.snd.comp Primrec.fst) hin
  exact (Primrec.list_flatMap Primrec.fst hg).of_eq fun _ => rfl

theorem primrec_mat {α : Type*} [Primcodable α] {g : α → Mat ι}
    (h : ∀ i j, Primrec fun a => g a i j) : Primrec g :=
  Primrec.fin_curry.2 (Primrec₂.swap (f := fun i a => g a i)
    (Primrec.fin_curry₁.2 fun i => Primrec.fin_curry.2
      (Primrec₂.swap (f := fun j a => g a i j) (Primrec.fin_curry₁.2 fun j => h i j))))

theorem primrec_mat_apply {α : Type*} [Primcodable α] {A : α → Mat ι} (hA : Primrec A)
    (i j : Fin 3) : Primrec fun a => A a i j :=
  (Primrec.fin_app.comp (Primrec.fin_app.comp hA (Primrec.const i)) (Primrec.const j)).of_eq
    fun _ => rfl

theorem primrec_matMul : Primrec₂ (matMul : Mat ι → Mat ι → Mat ι) := by
  refine primrec_mat fun i j => ?_
  have h : ∀ k : Fin 3, Primrec fun p : Mat ι × Mat ι => entryMul (p.1 i k) (p.2 k j) := fun k =>
    primrec_entryMul.comp (primrec_mat_apply Primrec.fst i k) (primrec_mat_apply Primrec.snd k j)
  exact (Primrec.list_append.comp (Primrec.list_append.comp (h 0) (h 1)) (h 2)).of_eq fun _ => rfl

theorem primrec_wordMat : Primrec (wordMat : List (Gen ι × Bool) → Mat ι) := by
  have hstep : Primrec₂ fun (_ : List (Gen ι × Bool)) (p : (Gen ι × Bool) × Mat ι) =>
      matMul (genMat p.1.1) p.2 :=
    primrec_matMul.comp ((Primrec.dom_finite (genMat : Gen ι → Mat ι)).comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))) (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldr Primrec.id (Primrec.const matOne) hstep).of_eq fun _ => rfl

theorem primrec_diffEntry {α : Type*} [Primcodable α] {A : α → Mat ι} (hA : Primrec A)
    (i j : Fin 3) : Primrec fun a => diffEntry (A a) i j := by
  by_cases h : i = j
  · exact (Primrec.list_append.comp (primrec_mat_apply hA i j) (Primrec.const oneEntry)).of_eq
      fun a => by rw [diffEntry, if_pos h]
  · exact (primrec_mat_apply hA i j).of_eq fun a => by rw [diffEntry, if_neg h]

theorem primrec_fin3_all {α : Type*} [Primcodable α] {f : α → Fin 3 → Bool}
    (h : ∀ i, Primrec fun a => f a i) : Primrec fun a => fin3.all (f a) :=
  (Primrec.and.comp (h 0) (Primrec.and.comp (h 1) (Primrec.and.comp (h 2)
    (Primrec.const true)))).of_eq fun _ => rfl

theorem primrec_fin3_flatMap {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → Fin 3 → List β} (h : ∀ i, Primrec fun a => f a i) :
    Primrec fun a => fin3.flatMap (f a) :=
  (Primrec.list_append.comp (h 0) (Primrec.list_append.comp (h 1) (Primrec.list_append.comp (h 2)
    (Primrec.const [])))).of_eq fun _ => rfl

theorem primrec_entryWords : Primrec (entryWords : Entry ι → List (List (ι × Bool))) := by
  have hp : Primrec₂ fun (_ : Entry ι × Mono ι) (p : List (Option ι × Bool)) =>
      deltaWord p :: lampPrefixes p :=
    Primrec.list_cons.comp (primrec_deltaWord.comp Primrec.snd)
      (primrec_lampPrefixes.comp Primrec.snd)
  have hm : Primrec₂ fun (_ : Entry ι) (m : Mono ι) => deltaWord m.2 :: (lampPrefixes m.2 ++
      m.1.flatMap fun p => deltaWord p :: lampPrefixes p) :=
    Primrec.list_cons.comp (primrec_deltaWord.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.list_append.comp (primrec_lampPrefixes.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.list_flatMap (Primrec.fst.comp Primrec.snd) hp))
  exact (Primrec.list_flatMap Primrec.id hm).of_eq fun _ => rfl

theorem primrec_wordWords :
    Primrec (wordWords : List (Gen ι × Bool) → List (List (ι × Bool))) :=
  (primrec_fin3_flatMap
    (f := fun w i => fin3.flatMap fun j => entryWords (diffEntry (wordMat w) i j))
    fun i => primrec_fin3_flatMap (f := fun w j => entryWords (diffEntry (wordMat w) i j))
      fun j => primrec_entryWords.comp (primrec_diffEntry primrec_wordMat i j)).of_eq fun _ => rfl

theorem primrec_queryCodes : Primrec (queryCodes : List (Gen ι × Bool) → List ℕ) := by
  have hv : Primrec₂ fun (q : List (Gen ι × Bool) × List (ι × Bool)) (v : List (ι × Bool)) =>
      wordInv q.2 ++ v :=
    Primrec.list_append.comp (primrec_wordInv.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
  have hu : Primrec₂ fun (w : List (Gen ι × Bool)) (u : List (ι × Bool)) =>
      (wordWords w).map fun v => wordInv u ++ v :=
    Primrec.list_map (primrec_wordWords.comp Primrec.fst) hv
  exact (Primrec.list_map (Primrec.list_flatMap primrec_wordWords hu)
    (Primrec.encode.comp Primrec.snd).to₂).of_eq fun _ => rfl

theorem primrec_ansE : Primrec fun p : (List (Gen ι × Bool) × List ℕ) ×
    List (ι × Bool) × List (ι × Bool) => ansE p.1.1 p.1.2 p.2.1 p.2.2 := by
  have hk : Primrec₂ fun (p : (List (Gen ι × Bool) × List ℕ) × List (ι × Bool) ×
      List (ι × Bool)) (k : ℕ) => decide (k = encode (wordInv p.2.1 ++ p.2.2)) :=
    Primrec.eq.decide.comp Primrec.snd (Primrec.encode.comp (Primrec.list_append.comp
      (primrec_wordInv.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
  exact (Primrec.eq.decide.comp ((Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.fst)
      (Primrec.list_findIdx (primrec_queryCodes.comp (Primrec.fst.comp Primrec.fst)) hk))
    (Primrec.const 1)).of_eq fun _ => rfl

theorem parity_eq_foldr (E : List (ι × Bool) → List (ι × Bool) → Bool) (q : List (ι × Bool))
    (L : List (List (ι × Bool))) :
    parity E q L = L.foldr (fun q' b => xor (E q' q) b) false := by
  induction L with
  | nil => rfl
  | cons q' L ih => exact congrArg (xor (E q' q)) ih

theorem monoBit_eq_foldr (E : List (ι × Bool) → List (ι × Bool) → Bool)
    (P : List (List (ι × Bool))) (a : List Bool) (F : List (List (Option ι × Bool))) :
    monoBit E P a F = F.foldr (fun p b =>
      xor (bitAt P a (deltaWord p)) (parity E (deltaWord p) (lampPrefixes p)) && b) true := by
  induction F with
  | nil => rfl
  | cons p F ih =>
    exact congrArg
      (xor (bitAt P a (deltaWord p)) (parity E (deltaWord p) (lampPrefixes p)) && ·) ih

theorem classSum_eq_foldr (E : List (ι × Bool) → List (ι × Bool) → Bool)
    (P : List (List (ι × Bool))) (a : List Bool) (m0 : Mono ι) (e : Entry ι) :
    classSum E P a m0 e =
      e.foldr (fun m b => xor (sameUnit E m.2 m0.2 && monoBit E P a m.1) b) false := by
  induction e with
  | nil => rfl
  | cons m e ih => exact congrArg (xor (sameUnit E m.2 m0.2 && monoBit E P a m.1)) ih

theorem allBits_eq_iterate (n : ℕ) :
    allBits n =
      (fun L : List (List Bool) => L.flatMap fun l => [false :: l, true :: l])^[n] [[]] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← ih]
    rfl

theorem primrec_allBits : Primrec allBits := by
  have hl : Primrec₂ fun (_ : ℕ × List (List Bool)) (l : List Bool) => [false :: l, true :: l] :=
    Primrec.list_cons.comp (Primrec.list_cons.comp (Primrec.const false) Primrec.snd)
      (Primrec.list_cons.comp (Primrec.list_cons.comp (Primrec.const true) Primrec.snd)
        (Primrec.const []))
  have hstep : Primrec₂ fun (_ : ℕ) (L : List (List Bool)) =>
      L.flatMap fun l => [false :: l, true :: l] :=
    Primrec.list_flatMap Primrec.snd hl
  exact (Primrec.nat_iterate Primrec.id (Primrec.const [[]]) hstep).of_eq fun n =>
    (allBits_eq_iterate n).symm

theorem primrec_points : Primrec (points : Entry ι → List (List (ι × Bool))) := by
  have hm : Primrec₂ fun (_ : Entry ι) (m : Mono ι) => m.1.map deltaWord :=
    Primrec.list_map (Primrec.fst.comp Primrec.snd) (primrec_deltaWord.comp Primrec.snd).to₂
  exact (Primrec.list_flatMap Primrec.id hm).of_eq fun _ => rfl

theorem primrec_bitAt {α : Type*} [Primcodable α] {P : α → List (List (ι × Bool))}
    {bits : α → List Bool} {γ : α → List (ι × Bool)} (hP : Primrec P) (hbits : Primrec bits)
    (hγ : Primrec γ) : Primrec fun a => bitAt (P a) (bits a) (γ a) := by
  have hp : Primrec₂ fun (a : α) (z : List (ι × Bool)) => decide (z = γ a) :=
    Primrec.eq.decide.comp Primrec.snd (hγ.comp Primrec.fst)
  exact ((Primrec.list_getD false).comp hbits (Primrec.list_findIdx hP hp)).of_eq fun _ => rfl

theorem primrec_parity {α : Type*} [Primcodable α]
    {E : α → List (ι × Bool) → List (ι × Bool) → Bool}
    (hE : Primrec fun p : α × List (ι × Bool) × List (ι × Bool) => E p.1 p.2.1 p.2.2)
    {q : α → List (ι × Bool)} {L : α → List (List (ι × Bool))} (hq : Primrec q)
    (hL : Primrec L) : Primrec fun a => parity (E a) (q a) (L a) := by
  have hstep : Primrec₂ fun (a : α) (p : List (ι × Bool) × Bool) => xor (E a p.1 (q a)) p.2 :=
    primrec_xor.comp (hE.comp (Primrec.pair Primrec.fst (Primrec.pair
      (Primrec.fst.comp Primrec.snd) (hq.comp Primrec.fst)))) (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldr hL (Primrec.const false) hstep).of_eq fun a =>
    (parity_eq_foldr (E a) (q a) (L a)).symm

theorem primrec_sameUnit {α : Type*} [Primcodable α]
    {E : α → List (ι × Bool) → List (ι × Bool) → Bool}
    (hE : Primrec fun p : α × List (ι × Bool) × List (ι × Bool) => E p.1 p.2.1 p.2.2)
    {u u' : α → List (Option ι × Bool)} (hu : Primrec u) (hu' : Primrec u') :
    Primrec fun a => sameUnit (E a) (u a) (u' a) := by
  have hE' : Primrec fun p : (α × List (ι × Bool)) × List (ι × Bool) × List (ι × Bool) =>
      E p.1.1 p.2.1 p.2.2 :=
    hE.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  have hpar : ∀ {w : α → List (Option ι × Bool)}, Primrec w →
      Primrec fun c : α × List (ι × Bool) => parity (E c.1) c.2 (lampPrefixes (w c.1)) :=
    fun hw => primrec_parity (E := fun c : α × List (ι × Bool) => E c.1) hE' Primrec.snd
      (primrec_lampPrefixes.comp (hw.comp Primrec.fst))
  have hq : Primrec₂ fun (a : α) (q : List (ι × Bool)) =>
      parity (E a) q (lampPrefixes (u a)) == parity (E a) q (lampPrefixes (u' a)) :=
    primrec_beq_bool.comp (hpar hu) (hpar hu')
  have hstep : Primrec₂ fun (a : α) (p : List (ι × Bool) × Bool) =>
      (parity (E a) p.1 (lampPrefixes (u a)) == parity (E a) p.1 (lampPrefixes (u' a))) &&
        p.2 :=
    Primrec.and.comp (hq.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have hall : Primrec fun a => (lampPrefixes (u a) ++ lampPrefixes (u' a)).all fun q =>
      parity (E a) q (lampPrefixes (u a)) == parity (E a) q (lampPrefixes (u' a)) :=
    (Primrec.list_foldr (Primrec.list_append.comp (primrec_lampPrefixes.comp hu)
      (primrec_lampPrefixes.comp hu')) (Primrec.const true) hstep).of_eq fun _ => by
        simp only [all_eq_foldr]
  exact (Primrec.and.comp (hE.comp (Primrec.pair Primrec.id (Primrec.pair
    (primrec_deltaWord.comp hu) (primrec_deltaWord.comp hu')))) hall).of_eq fun _ => rfl

theorem primrec_monoBit {α : Type*} [Primcodable α]
    {E : α → List (ι × Bool) → List (ι × Bool) → Bool}
    (hE : Primrec fun p : α × List (ι × Bool) × List (ι × Bool) => E p.1 p.2.1 p.2.2)
    {P : α → List (List (ι × Bool))} {bits : α → List Bool}
    {F : α → List (List (Option ι × Bool))} (hP : Primrec P) (hbits : Primrec bits)
    (hF : Primrec F) : Primrec fun a => monoBit (E a) (P a) (bits a) (F a) := by
  have hE' : Primrec fun p : (α × List (Option ι × Bool) × Bool) × List (ι × Bool) ×
      List (ι × Bool) => E p.1.1 p.2.1 p.2.2 :=
    hE.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  have hdw : Primrec fun r : α × List (Option ι × Bool) × Bool => deltaWord r.2.1 :=
    primrec_deltaWord.comp (Primrec.fst.comp Primrec.snd)
  have hstep : Primrec₂ fun (a : α) (r : List (Option ι × Bool) × Bool) =>
      xor (bitAt (P a) (bits a) (deltaWord r.1))
        (parity (E a) (deltaWord r.1) (lampPrefixes r.1)) && r.2 :=
    Primrec.and.comp (primrec_xor.comp
      (primrec_bitAt (hP.comp Primrec.fst) (hbits.comp Primrec.fst) hdw)
      (primrec_parity (E := fun s : α × List (Option ι × Bool) × Bool => E s.1) hE' hdw
        (primrec_lampPrefixes.comp (Primrec.fst.comp Primrec.snd))))
      (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldr hF (Primrec.const true) hstep).of_eq fun a =>
    (monoBit_eq_foldr (E a) (P a) (bits a) (F a)).symm

theorem primrec_consistent {α : Type*} [Primcodable α]
    {E : α → List (ι × Bool) → List (ι × Bool) → Bool}
    (hE : Primrec fun p : α × List (ι × Bool) × List (ι × Bool) => E p.1 p.2.1 p.2.2)
    {P : α → List (List (ι × Bool))} {bits : α → List Bool} (hP : Primrec P)
    (hbits : Primrec bits) : Primrec fun a => consistent (E a) (P a) (bits a) := by
  have hPs : Primrec fun s : (α × ℕ) × ℕ × Bool => P s.1.1 :=
    hP.comp (Primrec.fst.comp Primrec.fst)
  have hbs : Primrec fun s : (α × ℕ) × ℕ × Bool => bits s.1.1 :=
    hbits.comp (Primrec.fst.comp Primrec.fst)
  have hin : Primrec₂ fun (c : α × ℕ) (r : ℕ × Bool) =>
      (!E c.1 ((P c.1).getD c.2 []) ((P c.1).getD r.1 []) ||
        (bits c.1).getD c.2 false == (bits c.1).getD r.1 false) && r.2 :=
    Primrec.and.comp (Primrec.or.comp (Primrec.not.comp (hE.comp (Primrec.pair
        (Primrec.fst.comp Primrec.fst) (Primrec.pair
          ((Primrec.list_getD []).comp hPs (Primrec.snd.comp Primrec.fst))
          ((Primrec.list_getD []).comp hPs (Primrec.fst.comp Primrec.snd))))))
      (primrec_beq_bool.comp ((Primrec.list_getD false).comp hbs (Primrec.snd.comp Primrec.fst))
        ((Primrec.list_getD false).comp hbs (Primrec.fst.comp Primrec.snd))))
      (Primrec.snd.comp Primrec.snd)
  have hrow : Primrec fun c : α × ℕ => (List.range (P c.1).length).all fun j =>
      !E c.1 ((P c.1).getD c.2 []) ((P c.1).getD j []) ||
        (bits c.1).getD c.2 false == (bits c.1).getD j false :=
    (Primrec.list_foldr (Primrec.list_range.comp (Primrec.list_length.comp (hP.comp Primrec.fst)))
      (Primrec.const true) hin).of_eq fun _ => by simp only [all_eq_foldr]
  have hout : Primrec₂ fun (a : α) (r : ℕ × Bool) =>
      ((List.range (P a).length).all fun j => !E a ((P a).getD r.1 []) ((P a).getD j []) ||
        (bits a).getD r.1 false == (bits a).getD j false) && r.2 :=
    Primrec.and.comp (hrow.comp (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldr (Primrec.list_range.comp (Primrec.list_length.comp hP))
    (Primrec.const true) hout).of_eq fun _ => by simp only [consistent, all_eq_foldr]

theorem primrec_classSum {α : Type*} [Primcodable α]
    {E : α → List (ι × Bool) → List (ι × Bool) → Bool}
    (hE : Primrec fun p : α × List (ι × Bool) × List (ι × Bool) => E p.1 p.2.1 p.2.2)
    {P : α → List (List (ι × Bool))} {bits : α → List Bool} {m0 : α → Mono ι}
    {e : α → Entry ι} (hP : Primrec P) (hbits : Primrec bits) (hm0 : Primrec m0)
    (he : Primrec e) : Primrec fun a => classSum (E a) (P a) (bits a) (m0 a) (e a) := by
  have hE' : Primrec fun p : (α × Mono ι × Bool) × List (ι × Bool) × List (ι × Bool) =>
      E p.1.1 p.2.1 p.2.2 :=
    hE.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  have hstep : Primrec₂ fun (a : α) (r : Mono ι × Bool) =>
      xor (sameUnit (E a) r.1.2 (m0 a).2 && monoBit (E a) (P a) (bits a) r.1.1) r.2 :=
    primrec_xor.comp (Primrec.and.comp
      (primrec_sameUnit (E := fun s : α × Mono ι × Bool => E s.1) hE'
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp (hm0.comp Primrec.fst)))
      (primrec_monoBit (E := fun s : α × Mono ι × Bool => E s.1) hE' (hP.comp Primrec.fst)
        (hbits.comp Primrec.fst) (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))))
      (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldr he (Primrec.const false) hstep).of_eq fun a =>
    (classSum_eq_foldr (E a) (P a) (bits a) (m0 a) (e a)).symm

theorem primrec_entryZero {α : Type*} [Primcodable α]
    {E : α → List (ι × Bool) → List (ι × Bool) → Bool}
    (hE : Primrec fun p : α × List (ι × Bool) × List (ι × Bool) => E p.1 p.2.1 p.2.2)
    {e : α → Entry ι} (he : Primrec e) : Primrec fun a => entryZero (E a) (e a) := by
  have hE1 : Primrec fun p : ((α × Mono ι) × List Bool × Bool) × List (ι × Bool) ×
      List (ι × Bool) => E p.1.1.1 p.2.1 p.2.2 :=
    hE.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
  have hPs : Primrec fun s : (α × Mono ι) × List Bool × Bool => points (e s.1.1) :=
    primrec_points.comp (he.comp (Primrec.fst.comp Primrec.fst))
  have hin : Primrec₂ fun (c : α × Mono ι) (r : List Bool × Bool) =>
      (!consistent (E c.1) (points (e c.1)) r.1 ||
        !classSum (E c.1) (points (e c.1)) r.1 c.2 (e c.1)) && r.2 :=
    Primrec.and.comp (Primrec.or.comp
      (Primrec.not.comp (primrec_consistent
        (E := fun s : (α × Mono ι) × List Bool × Bool => E s.1.1) hE1 hPs
        (Primrec.fst.comp Primrec.snd)))
      (Primrec.not.comp (primrec_classSum
        (E := fun s : (α × Mono ι) × List Bool × Bool => E s.1.1) hE1 hPs
        (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)
        (he.comp (Primrec.fst.comp Primrec.fst)))))
      (Primrec.snd.comp Primrec.snd)
  have hrow : Primrec fun c : α × Mono ι => (allBits (points (e c.1)).length).all fun bits =>
      !consistent (E c.1) (points (e c.1)) bits ||
        !classSum (E c.1) (points (e c.1)) bits c.2 (e c.1) :=
    (Primrec.list_foldr (primrec_allBits.comp (Primrec.list_length.comp
      (primrec_points.comp (he.comp Primrec.fst)))) (Primrec.const true) hin).of_eq fun _ => by
        simp only [all_eq_foldr]
  have hout : Primrec₂ fun (a : α) (r : Mono ι × Bool) =>
      ((allBits (points (e a)).length).all fun bits => !consistent (E a) (points (e a)) bits ||
        !classSum (E a) (points (e a)) bits r.1 (e a)) && r.2 :=
    Primrec.and.comp (hrow.comp (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldr he (Primrec.const true) hout).of_eq fun _ => by
    simp only [entryZero, all_eq_foldr]

theorem primrec_wordTrivial {α : Type*} [Primcodable α]
    {E : α → List (ι × Bool) → List (ι × Bool) → Bool}
    (hE : Primrec fun p : α × List (ι × Bool) × List (ι × Bool) => E p.1 p.2.1 p.2.2)
    {w : α → List (Gen ι × Bool)} (hw : Primrec w) :
    Primrec fun a => wordTrivial (E a) (w a) :=
  (primrec_fin3_all
    (f := fun a i => fin3.all fun j => entryZero (E a) (diffEntry (wordMat (w a)) i j))
    fun i => primrec_fin3_all (f := fun a j => entryZero (E a) (diffEntry (wordMat (w a)) i j))
      fun j => primrec_entryZero hE (primrec_diffEntry (primrec_wordMat.comp hw) i j)).of_eq
    fun _ => rfl

theorem primrec_hostQueries : Primrec (hostQueries (ι := ι)) :=
  (Primrec.option_getD.comp (Primrec.option_map Primrec.decode
    (primrec_queryCodes.comp Primrec.snd).to₂) (Primrec.const [])).of_eq fun _ => rfl

theorem primrec_hostDecide : Primrec₂ (hostDecide (ι := ι)) := by
  have hE : Primrec fun p : ((ℕ × List ℕ) × List (Gen ι × Bool)) × List (ι × Bool) ×
      List (ι × Bool) => ansE p.1.2 p.1.1.2 p.2.1 p.2.2 :=
    primrec_ansE.comp (Primrec.pair (Primrec.pair (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd)
  have hw : Primrec₂ fun (p : ℕ × List ℕ) (w : List (Gen ι × Bool)) =>
      bif wordTrivial (ansE w p.2) w then 1 else 0 :=
    Primrec.cond (primrec_wordTrivial (E := fun c : (ℕ × List ℕ) × List (Gen ι × Bool) =>
      ansE c.2 c.1.2) hE Primrec.snd) (Primrec.const 1) (Primrec.const 0)
  exact (Primrec.option_getD.comp (Primrec.option_map (Primrec.decode.comp Primrec.fst) hw)
    (Primrec.const 0)).of_eq fun _ => rfl

end Primrec

end Host

open Host in
/-- **`G_Δ` has solvable word problem** (tex l.447–455): when `Δ` has solvable word problem, so has
the lamplighter host `G_Δ = EL_3(LC(Ω, F_2) ⋊ Λ)`. -/
theorem printedLamplighterHostSolvableWordProblem : PrintedLamplighterHostSolvableWordProblem := by
  intro Δ _ hΔ
  obtain ⟨ι, _, _, t, ht, hpart⟩ := hΔ
  classical
  refine ⟨Gen ι, inferInstance, inferInstance, gens t, closure_range_gens ht, ?_⟩
  have hred : TuringReducible (wordProblemOracle (gens t)) (wordProblemOracle t) :=
    OracleTruthTable.turingReducible_of_truthTable (gt := answer t) (fun _ => rfl)
      (primrec_hostQueries (ι := ι)) (primrec_hostDecide (ι := ι)) (wordProblemOracle_gens t)
  exact partrec_iff_forall_turingReducible.mpr fun o =>
    TuringReducible.trans hred (partrec_iff_forall_turingReducible.mp hpart o)

end Lamplighter
end SimpleKazhdanSofic
end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.Lamplighter.Host.wordProblemOracle_gens
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.Lamplighter.printedLamplighterHostSolvableWordProblem
