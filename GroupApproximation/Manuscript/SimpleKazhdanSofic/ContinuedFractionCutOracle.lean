import GroupApproximation.Manuscript.SimpleKazhdanSofic.ContinuedFractionDigitOracle
import GroupApproximation.Manuscript.SimpleKazhdanSofic.ContinuedFractionIntervals
import GroupApproximation.Meta.AxiomGuard

/-!
# `S` computes `α = [0; 1 + χ_S(0), 1 + χ_S(1), …]`

`simple_kazhdan_sofic_group.tex` (origin tip f34e9c0b1), proof of `cor:wp`, second paragraph
(sentence sha256 `a686ac809830`): "Every $D\subseteq\mathbb N$ has the degree of
$[0;1+\chi_D(0),1+\chi_D(1),\dots]$". This module proves the half `slopeOracle α ≤_T charOracle S`,
for digits `a_k ∈ {1, 2}` with `k ∈ S ↔ a_k = 2` (the printed `D`):
* `S` gives the digits, hence `conv a n`, by `n` queries (`cutState_exists`);
* at level `n` the flag `cutFlag` is `0` once `c/e` is on one side of both endpoints of
  `ContinuedFractionIntervals` (or `e = 0`), and such a level exists (`cutFlag_exists`, from
  `exists_sep`);
* `Nat.RecursiveIn.rfind` finds the least such level, and the side there is `[c < e α]`
  (`cutSide_correct`).
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace ContinuedFractionOracle

open ContinuedFractionExpansion

variable {a : ℕ → ℕ}

open Classical in
/-- The answers of `charOracle S`. -/
noncomputable def charValue (S : Set ℕ) (n : ℕ) : ℕ :=
  if n ∈ S then 1 else 0

theorem charOracle_eq (S : Set ℕ) (n : ℕ) : charOracle S n = Part.some (charValue S n) :=
  rfl

theorem digit_eq_one_add_charValue (ha : ∀ k, a k = 1 ∨ a k = 2) {S : Set ℕ}
    (hS : ∀ k, k ∈ S ↔ a k = 2) (k : ℕ) : a k = 1 + charValue S k := by
  unfold charValue
  by_cases h : k ∈ S
  · rw [if_pos h, (hS k).1 h]
  · rw [if_neg h]
    rcases ha k with h1 | h1
    · rw [h1]
    · exact absurd ((hS k).2 h1) h

/-- Start from `conv a 0`. -/
def cutInit (_N : ℕ) : ℕ :=
  stateCode (1, 0, 0, 1) 0

/-- Step `j` asks whether `j ∈ S`. -/
def cutQuery (_N j _i : ℕ) : ℕ :=
  j

/-- Step `j` appends the digit `1 + χ_S(j)`. -/
def cutStep (_N _j i o : ℕ) : ℕ :=
  advance i (1 + o)

/-- On `N = ⟪m, n⟫`, run `n` steps. -/
def cutLen (N : ℕ) : ℕ :=
  (Nat.unpair N).2

/-- `c/e` is at most both endpoints of the state `i`, for `m = ⟪c, e⟫`. -/
abbrev CutBelow (m i : ℕ) : Prop :=
  (Nat.unpair m).1 * (3 * qCur i + qPrev i) ≤ (3 * pCur i + pPrev i) * (Nat.unpair m).2 ∧
    (Nat.unpair m).1 * (4 * qCur i + 3 * qPrev i) ≤ (4 * pCur i + 3 * pPrev i) * (Nat.unpair m).2

/-- `c/e` is at least both endpoints of the state `i`, for `m = ⟪c, e⟫`. -/
abbrev CutAbove (m i : ℕ) : Prop :=
  (3 * pCur i + pPrev i) * (Nat.unpair m).2 ≤ (Nat.unpair m).1 * (3 * qCur i + qPrev i) ∧
    (4 * pCur i + 3 * pPrev i) * (Nat.unpair m).2 ≤ (Nat.unpair m).1 * (4 * qCur i + 3 * qPrev i)

/-- `0` once the level of `N = ⟪m, n⟫` separates `c/e` from `α`. -/
def cutFlag (N i : ℕ) : ℕ :=
  if (Nat.unpair (Nat.unpair N).1).2 = 0 ∨ CutBelow (Nat.unpair N).1 i ∨
      CutAbove (Nat.unpair N).1 i then 0 else 1

/-- The answer `[c < e α]` read off a separating level. -/
def cutSide (N i : ℕ) : ℕ :=
  if ¬(Nat.unpair (Nat.unpair N).1).2 = 0 ∧ CutBelow (Nat.unpair N).1 i then 1 else 0

theorem primrec_cutInit : Primrec cutInit :=
  (Primrec.const (stateCode (1, 0, 0, 1) 0)).of_eq fun _ => rfl

theorem primrec_cutQuery : Primrec fun p : ℕ × ℕ × ℕ => cutQuery p.1 p.2.1 p.2.2 :=
  (Primrec.fst.comp Primrec.snd).of_eq fun _ => rfl

theorem primrec_cutStep : Primrec fun p : (ℕ × ℕ × ℕ) × ℕ => cutStep p.1.1 p.1.2.1 p.1.2.2 p.2 :=
  (primrec_advance.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    (Primrec.nat_add.comp (Primrec.const 1) Primrec.snd)).of_eq fun _ => rfl

theorem primrec_cutLen : Primrec cutLen :=
  primrec_unpair_snd

theorem primrec_cutC : Primrec fun p : ℕ × ℕ => (Nat.unpair (Nat.unpair p.1).1).1 :=
  Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)))

theorem primrec_cutE : Primrec fun p : ℕ × ℕ => (Nat.unpair (Nat.unpair p.1).1).2 :=
  Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)))

theorem primrec_lin (x y : ℕ) {f g : ℕ → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun p : ℕ × ℕ => x * f p.2 + y * g p.2 :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const x) (hf.comp Primrec.snd))
    (Primrec.nat_mul.comp (Primrec.const y) (hg.comp Primrec.snd))

theorem primrecPred_cutBelow : PrimrecPred fun p : ℕ × ℕ => CutBelow (Nat.unpair p.1).1 p.2 :=
  (PrimrecPred.and
    (Primrec.nat_le.comp (Primrec.nat_mul.comp primrec_cutC (primrec_lin 3 1 primrec_qCur primrec_qPrev))
      (Primrec.nat_mul.comp (primrec_lin 3 1 primrec_pCur primrec_pPrev) primrec_cutE))
    (Primrec.nat_le.comp (Primrec.nat_mul.comp primrec_cutC (primrec_lin 4 3 primrec_qCur primrec_qPrev))
      (Primrec.nat_mul.comp (primrec_lin 4 3 primrec_pCur primrec_pPrev) primrec_cutE))).of_eq
    fun p => by simp only [one_mul]

theorem primrecPred_cutAbove : PrimrecPred fun p : ℕ × ℕ => CutAbove (Nat.unpair p.1).1 p.2 :=
  (PrimrecPred.and
    (Primrec.nat_le.comp (Primrec.nat_mul.comp (primrec_lin 3 1 primrec_pCur primrec_pPrev) primrec_cutE)
      (Primrec.nat_mul.comp primrec_cutC (primrec_lin 3 1 primrec_qCur primrec_qPrev)))
    (Primrec.nat_le.comp (Primrec.nat_mul.comp (primrec_lin 4 3 primrec_pCur primrec_pPrev) primrec_cutE)
      (Primrec.nat_mul.comp primrec_cutC (primrec_lin 4 3 primrec_qCur primrec_qPrev)))).of_eq
    fun p => by simp only [one_mul]

theorem primrec_cutFlag : Primrec₂ cutFlag :=
  (Primrec.ite (PrimrecPred.or (Primrec.eq.comp primrec_cutE (Primrec.const 0))
    (PrimrecPred.or primrecPred_cutBelow primrecPred_cutAbove)) (Primrec.const 0)
    (Primrec.const 1)).of_eq fun _ => rfl

theorem primrec_cutSide : Primrec₂ cutSide :=
  (Primrec.ite (PrimrecPred.and (PrimrecPred.not (Primrec.eq.comp primrec_cutE (Primrec.const 0)))
    primrecPred_cutBelow) (Primrec.const 1) (Primrec.const 0)).of_eq fun _ => rfl

theorem cutState_exists (ha : ∀ k, a k = 1 ∨ a k = 2) {S : Set ℕ} (hS : ∀ k, k ∈ S ↔ a k = 2)
    (N : ℕ) : ∀ k, ∃ d, oracleRecState (charValue S) cutInit cutQuery cutStep N k =
      stateCode (conv a k) d
  | 0 => ⟨0, rfl⟩
  | k + 1 => by
    obtain ⟨d, hd⟩ := cutState_exists ha hS N k
    refine ⟨1 + charValue S k, ?_⟩
    rw [oracleRecState_succ, hd]
    show advance (stateCode (conv a k) d) (1 + charValue S k) = _
    rw [← digit_eq_one_add_charValue ha hS k, advance_stateCode]

theorem lt_mul_tail_of_cutBelow (ha : ∀ k, a k = 1 ∨ a k = 2) {m n d : ℕ}
    (he : 0 < (Nat.unpair m).2) (hb : CutBelow m (stateCode (conv a n) d)) :
    ((Nat.unpair m).1 : ℝ) < (Nat.unpair m).2 * tail a ha 0 := by
  have hq := one_le_conv_q ha n
  have hY3 : 0 < 3 * (conv a n).2.2.2 + (conv a n).2.2.1 := by omega
  have hY4 : 0 < 4 * (conv a n).2.2.2 + 3 * (conv a n).2.2.1 := by omega
  simp only [CutBelow, pCur_stateCode, pPrev_stateCode, qCur_stateCode, qPrev_stateCode] at hb
  have h1 : ((Nat.unpair m).1 : ℝ) / (Nat.unpair m).2 ≤ endA a n :=
    (natCast_div_le_iff he hY3).2 hb.1
  have h2 : ((Nat.unpair m).1 : ℝ) / (Nat.unpair m).2 ≤ endB a n :=
    (natCast_div_le_iff he hY4).2 hb.2
  have hlt : ((Nat.unpair m).1 : ℝ) / (Nat.unpair m).2 < tail a ha 0 := by
    rcases mul_neg_iff.1 (sub_endA_mul_sub_endB_neg ha n) with ⟨h3, -⟩ | ⟨-, h4⟩
    · linarith
    · linarith
  rw [div_lt_iff₀ (by exact_mod_cast he), mul_comm] at hlt
  exact hlt

theorem not_lt_mul_tail_of_cutAbove (ha : ∀ k, a k = 1 ∨ a k = 2) {m n d : ℕ}
    (he : 0 < (Nat.unpair m).2) (hb : CutAbove m (stateCode (conv a n) d)) :
    ¬ ((Nat.unpair m).1 : ℝ) < (Nat.unpair m).2 * tail a ha 0 := by
  have hq := one_le_conv_q ha n
  have hY3 : 0 < 3 * (conv a n).2.2.2 + (conv a n).2.2.1 := by omega
  have hY4 : 0 < 4 * (conv a n).2.2.2 + 3 * (conv a n).2.2.1 := by omega
  simp only [CutAbove, pCur_stateCode, pPrev_stateCode, qCur_stateCode, qPrev_stateCode] at hb
  have h1 : endA a n ≤ ((Nat.unpair m).1 : ℝ) / (Nat.unpair m).2 :=
    (natCast_le_div_iff he hY3).2 hb.1
  have h2 : endB a n ≤ ((Nat.unpair m).1 : ℝ) / (Nat.unpair m).2 :=
    (natCast_le_div_iff he hY4).2 hb.2
  have hlt : tail a ha 0 < ((Nat.unpair m).1 : ℝ) / (Nat.unpair m).2 := by
    rcases mul_neg_iff.1 (sub_endA_mul_sub_endB_neg ha n) with ⟨-, h4⟩ | ⟨h3, -⟩
    · linarith
    · linarith
  rw [lt_div_iff₀ (by exact_mod_cast he)] at hlt
  rw [mul_comm, not_lt]
  exact hlt.le

theorem cutFlag_exists (ha : ∀ k, a k = 1 ∨ a k = 2) {S : Set ℕ} (hS : ∀ k, k ∈ S ↔ a k = 2)
    (m : ℕ) : ∃ n, cutFlag (Nat.pair m n) (oracleRecState (charValue S) cutInit cutQuery cutStep
      (Nat.pair m n) (cutLen (Nat.pair m n))) = 0 := by
  by_cases he : (Nat.unpair m).2 = 0
  · refine ⟨0, ?_⟩
    simp only [cutFlag, Nat.unpair_pair]
    rw [if_pos (Or.inl he)]
  · obtain ⟨n, hn⟩ := exists_sep ha (Nat.unpair m).1 (Nat.unpair m).2
    refine ⟨n, ?_⟩
    obtain ⟨d, hd⟩ := cutState_exists ha hS (Nat.pair m n) n
    simp only [cutLen, Nat.unpair_pair]
    rw [hd]
    simp only [cutFlag, Nat.unpair_pair]
    rw [if_pos (Or.inr ?_)]
    have hq := one_le_conv_q ha n
    have hY3 : 0 < 3 * (conv a n).2.2.2 + (conv a n).2.2.1 := by omega
    have hY4 : 0 < 4 * (conv a n).2.2.2 + 3 * (conv a n).2.2.1 := by omega
    have he' : 0 < (Nat.unpair m).2 := Nat.pos_of_ne_zero he
    simp only [CutBelow, CutAbove, pCur_stateCode, pPrev_stateCode, qCur_stateCode, qPrev_stateCode]
    rcases hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨((natCast_div_lt_iff he' hY3).1 h1).le, ((natCast_div_lt_iff he' hY4).1 h2).le⟩
    · exact Or.inr ⟨((natCast_lt_div_iff he' hY3).1 h1).le, ((natCast_lt_div_iff he' hY4).1 h2).le⟩

theorem cutSide_correct (ha : ∀ k, a k = 1 ∨ a k = 2) {S : Set ℕ} (hS : ∀ k, k ∈ S ↔ a k = 2)
    (m n : ℕ) (hflag : cutFlag (Nat.pair m n) (oracleRecState (charValue S) cutInit cutQuery
      cutStep (Nat.pair m n) (cutLen (Nat.pair m n))) = 0) :
    cutSide (Nat.pair m n) (oracleRecState (charValue S) cutInit cutQuery cutStep (Nat.pair m n)
      (cutLen (Nat.pair m n))) = slopeValue (tail a ha 0) m := by
  obtain ⟨d, hd⟩ := cutState_exists ha hS (Nat.pair m n) n
  simp only [cutLen, Nat.unpair_pair] at hflag ⊢
  rw [hd] at hflag ⊢
  simp only [cutFlag, cutSide, slopeValue, Nat.unpair_pair] at hflag ⊢
  by_cases he0 : (Nat.unpair m).2 = 0
  · rw [if_neg fun h => h.1 he0, he0, Nat.cast_zero, zero_mul,
      if_neg (not_lt.2 (Nat.cast_nonneg _))]
  · by_cases hb : CutBelow m (stateCode (conv a n) d)
    · rw [if_pos ⟨he0, hb⟩, if_pos (lt_mul_tail_of_cutBelow ha (Nat.pos_of_ne_zero he0) hb)]
    · have hcond : (Nat.unpair m).2 = 0 ∨ CutBelow m (stateCode (conv a n) d) ∨
          CutAbove m (stateCode (conv a n) d) := by
        by_contra h
        rw [if_neg h] at hflag
        exact one_ne_zero hflag
      have habove : CutAbove m (stateCode (conv a n) d) := by
        rcases hcond with h | h | h
        · exact absurd h he0
        · exact absurd h hb
        · exact h
      rw [if_neg fun h => hb h.2,
        if_neg (not_lt_mul_tail_of_cutAbove ha (Nat.pos_of_ne_zero he0) habove)]

/-- **`S` computes `α`**: `slopeOracle [0; a_0, a_1, …] ≤_T charOracle S` when `k ∈ S ↔ a_k = 2`. -/
theorem slopeOracle_turingReducible_charOracle (ha : ∀ k, a k = 1 ∨ a k = 2) {S : Set ℕ}
    (hS : ∀ k, k ∈ S ↔ a k = 2) : TuringReducible (slopeOracle (tail a ha 0)) (charOracle S) := by
  classical
  have hflag : TuringReducible (fun N => Part.some (cutFlag N
      (oracleRecState (charValue S) cutInit cutQuery cutStep N (cutLen N)))) (charOracle S) :=
    turingReducible_of_oracleRec (charValue S) (charOracle_eq S) cutInit cutQuery cutStep cutLen
      cutFlag primrec_cutInit primrec_cutQuery primrec_cutStep primrec_cutLen primrec_cutFlag
      fun _ => rfl
  have hside : TuringReducible (fun N => Part.some (cutSide N
      (oracleRecState (charValue S) cutInit cutQuery cutStep N (cutLen N)))) (charOracle S) :=
    turingReducible_of_oracleRec (charValue S) (charOracle_eq S) cutInit cutQuery cutStep cutLen
      cutSide primrec_cutInit primrec_cutQuery primrec_cutStep primrec_cutLen primrec_cutSide
      fun _ => rfl
  have hex := cutFlag_exists ha hS
  have hsep : Nat.RecursiveIn {charOracle S} fun m => Part.some (Nat.find (hex m)) := by
    refine Nat.RecursiveIn.of_eq (Nat.RecursiveIn.rfind (RecursiveIn.iff_nat.1 hflag)) fun m => ?_
    refine Part.eq_some_iff.2 (Nat.mem_rfind.2 ⟨?_, fun hk => ?_⟩)
    · simp only [Part.map_eq_map, Part.map_some, Part.mem_some_iff]
      exact (decide_eq_true (Nat.find_spec (hex m))).symm
    · simp only [Part.map_eq_map, Part.map_some, Part.mem_some_iff]
      exact (decide_eq_false (Nat.find_min (hex m) hk)).symm
  have hid : Nat.RecursiveIn {charOracle S} fun n => Part.some n :=
    Nat.Primrec.recursiveIn Nat.Primrec.id
  refine RecursiveIn.iff_nat.2 (Nat.RecursiveIn.of_eq (Nat.RecursiveIn.comp
    (RecursiveIn.iff_nat.1 hside) (Nat.RecursiveIn.pair hid hsep)) fun m => ?_)
  simp only [seq_eq_bind_map, Part.bind_eq_bind, Part.map_eq_map, Part.map_some, Part.bind_some]
  exact congrArg Part.some (cutSide_correct ha hS m (Nat.find (hex m)) (Nat.find_spec (hex m)))

end ContinuedFractionOracle
end SimpleKazhdanSofic
end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.ContinuedFractionOracle.cutSide_correct
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ContinuedFractionOracle.slopeOracle_turingReducible_charOracle
