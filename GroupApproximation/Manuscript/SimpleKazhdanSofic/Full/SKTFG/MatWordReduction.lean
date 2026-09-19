import GroupApproximation.Manuscript.SimpleKazhdanSofic.WordProblemReducesToLanguage
import GroupApproximation.Meta.AxiomGuard

/-!
# `L(X)` computes the triviality of any primitive recursive matrix of tables

`CylinderTables.turingReducible_of_wordTables` multiplies out words in elementary letters. The
decision procedure behind it only uses the multiplied-out matrix of tables. This file states it for
any primitive recursive map `F` from codes of words to `3 × 3` matrices of tables. A word is
decided by asking the language oracle about the words of length `2K + 1`, where `K = matRadius
(F w)`, and checking the table parities (`matEval_eq_one_iff_language`).

This is used for the derived topological full group of a subshift, whose generators are
diagonal matrices of tables, not elementary letters (`SKTFG.WordProblemToLanguage`).
-/

namespace GroupApproximation
namespace CylinderTables

open Encodable SymbolicDynamics.FullShift

variable {A : Type*} {ι : Type*}

/-- The words of length `2K + 1` asked about `w`. -/
def gWords (L : List A) (F : ι → Mat A) (w : ι) : List (List A) :=
  allWords L (2 * matRadius (F w) + 1)

/-- Their codes. -/
def gQueries [Primcodable A] (L : List A) (F : ι → Mat A) (w : ι) : List ℕ :=
  (gWords L F w).map encode

/-- Accept iff every table parity vanishes at every word answered `1`. -/
def gDecide [DecidableEq A] (L : List A) (F : ι → Mat A) (w : ι) (answers : List ℕ) : Bool :=
  (List.range (gWords L F w).length).all fun k =>
    !decide (answers.getD k 0 = 1) ||
      windowCheck (matRadius (F w)) (F w) ((gWords L F w).getD k [])

theorem primrec_gWords [Primcodable A] [Primcodable ι] (L : List A) {F : ι → Mat A}
    (hF : Primrec F) : Primrec (gWords L F) :=
  (primrec_allWords L).comp (Primrec.nat_double_succ.comp (primrec_matRadius.comp hF))

theorem primrec_gQueries [Primcodable A] [Primcodable ι] (L : List A) {F : ι → Mat A}
    (hF : Primrec F) : Primrec (gQueries L F) :=
  (Primrec.list_map (primrec_gWords L hF) (Primrec.encode.comp Primrec.snd).to₂).of_eq
    fun _ => rfl

theorem primrec_gDecide [Primcodable A] [DecidableEq A] [Primcodable ι] (L : List A)
    {F : ι → Mat A} (hF : Primrec F) : Primrec₂ (gDecide L F) := by
  show Primrec fun a : ι × List ℕ => gDecide L F a.1 a.2
  have hW : Primrec fun q : (ι × List ℕ) × (ℕ × Bool) => gWords L F q.1.1 :=
    (primrec_gWords L hF).comp (Primrec.fst.comp Primrec.fst)
  refine (Primrec.list_foldr (Primrec.list_range.comp (Primrec.list_length.comp
      ((primrec_gWords L hF).comp Primrec.fst))) (Primrec.const true)
    (Primrec.and.comp (Primrec.or.comp (Primrec.not.comp ((Primrec.eq (α := ℕ)).decide.comp
        ((Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
        (Primrec.const 1)))
      (primrec_windowCheck.comp (Primrec.pair
        (Primrec.pair ((primrec_matRadius.comp hF).comp (Primrec.fst.comp Primrec.fst))
          ((Primrec.list_getD []).comp hW (Primrec.fst.comp Primrec.snd)))
        (hF.comp (Primrec.fst.comp Primrec.fst)))))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun a => ?_
  simp only [gDecide, all_eq_foldr]

theorem gDecide_map_eq_true [DecidableEq A] (L : List A) (F : ι → Mat A) (w : ι)
    (φ : List A → ℕ) :
    gDecide L F w ((gWords L F w).map φ) = true ↔
      ∀ v ∈ gWords L F w, φ v = 1 → windowCheck (matRadius (F w)) (F w) v = true := by
  unfold gDecide
  rw [List.all_eq_true]
  constructor
  · intro h v hv h1
    obtain ⟨k, hk, hkv⟩ := List.getElem_of_mem hv
    have h2 := h k (List.mem_range.2 hk)
    have e1 : ((gWords L F w).map φ).getD k 0 = φ v := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, hkv]
    have e2 : (gWords L F w).getD k [] = v := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, hkv]
    rw [e1, e2, h1] at h2
    simpa using h2
  · intro h k hk
    have hk' := List.mem_range.1 hk
    have e1 : ((gWords L F w).map φ).getD k 0 = φ (gWords L F w)[k] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']
    have e2 : (gWords L F w).getD k [] = (gWords L F w)[k] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']
    rw [e1, e2]
    by_cases h1 : φ (gWords L F w)[k] = 1
    · simp [h (gWords L F w)[k] (List.getElem_mem hk') h1]
    · simp [h1]

open Classical in
/-- **`L(X)` computes the triviality of a primitive recursive matrix of tables.** -/
theorem turingReducible_of_matWord [Primcodable A] [DecidableEq A] [Primcodable ι]
    [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
    {X : Set (ℤ → A)} (hX : ∀ n : ℤ, Set.MapsTo (shift n) X X) (T : ↥X ≃ₜ ↥X)
    {F : ι → Mat A} (hF : Primrec F) (P : ι → Prop) (hP : ∀ w, P w ↔ matEval T (F w) = 1)
    {f g : ℕ →. ℕ}
    (hf : ∀ n, f n = Part.some (if ∃ w : ι, decode n = some w ∧ P w then 1 else 0))
    (hg : ∀ n, g n = Part.some
      (if ∃ v : List A, decode n = some v ∧ v ∈ listLanguage X then 1 else 0)) :
    TuringReducible f g := by
  obtain ⟨L, hL⟩ : ∃ L : List A, ∀ a, a ∈ L :=
    ⟨Finset.univ.toList, fun a => Finset.mem_toList.2 (Finset.mem_univ a)⟩
  let gt : ℕ → ℕ := fun n =>
    if ∃ v : List A, decode n = some v ∧ v ∈ listLanguage X then 1 else 0
  refine OracleTruthTable.turingReducible_of_truthTable (gt := gt) hg
    (Q := fun n => ((decode n : Option ι).map (gQueries L F)).getD [])
    (Primrec.option_getD.comp (Primrec.option_map Primrec.decode
      ((primrec_gQueries L hF).comp Primrec.snd).to₂) (Primrec.const []))
    (D := fun n answers => ((decode n : Option ι).map
      fun w => bif gDecide L F w answers then 1 else 0).getD 0)
    ?_ fun n => ?_
  · exact Primrec.option_getD.comp (Primrec.option_map (Primrec.decode.comp Primrec.fst)
      (Primrec.cond ((primrec_gDecide L hF).comp Primrec.snd (Primrec.snd.comp Primrec.fst))
        (Primrec.const 1) (Primrec.const 0)).to₂) (Primrec.const 0)
  rw [hf n]
  congr 1
  cases hd : (decode n : Option ι) with
  | none => simp
  | some w =>
    show (if ∃ w' : ι, some w = some w' ∧ P w' then 1 else 0) =
      (bif gDecide L F w ((gQueries L F w).map gt) then 1 else 0)
    have hex : (∃ w' : ι, some w = some w' ∧ P w') ↔ P w :=
      ⟨fun ⟨_, e, h⟩ => Option.some.inj e ▸ h, fun h => ⟨w, rfl, h⟩⟩
    have hans : (gQueries L F w).map gt =
        (gWords L F w).map fun v => if v ∈ listLanguage X then 1 else 0 := by
      rw [gQueries, List.map_map]
      refine List.map_congr_left fun v _ => ?_
      simp [gt, Encodable.encodek]
    have hdec : gDecide L F w ((gQueries L F w).map gt) = true ↔ P w := by
      rw [hans, gDecide_map_eq_true, hP,
        matEval_eq_one_iff_language hX T hL (F w)
          (fun p q => tableRadius_le_matRadius (F w) (p, q))]
      constructor
      · intro h p q j hj v hv hvL
        exact (windowCheck_eq_true _ _ v).1 (h v hv (by simp [hvL])) (p, q) j hj
      · intro h v hv hvL
        refine (windowCheck_eq_true _ _ v).2 fun pq j hj => h pq.1 pq.2 j hj v hv ?_
        by_contra hn
        simp [hn] at hvL
    by_cases hw : P w
    · rw [if_pos (hex.2 hw)]
      simp [hdec.2 hw]
    · rw [if_neg fun h => hw (hex.1 h)]
      have hfalse : gDecide L F w ((gQueries L F w).map gt) = false := by
        by_contra h
        exact hw (hdec.1 (by simpa using h))
      simp [hfalse]

end CylinderTables
end GroupApproximation

#audit_axioms GroupApproximation.CylinderTables.turingReducible_of_matWord
