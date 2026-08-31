import GroupApproximation.GGT.HullSCRelatorSeparation2ExactSideParser

/-!
# Exact-design exclusion for cyclic side spans

This file applies the cyclic normal forms to the three finite-avoidance clauses
of `ExactRelatorDesign₂`: a pure run, a run crossing the unique base letter,
and the exceptional seam beginning at the base after the final block.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Bookkeeping

variable {G : Type u} [Group G]

/-- An even nonempty alternating run beginning at `false` ends at `true`. -/
theorem exists_last_true_of_even_blockWord (h₀ h₁ : G) (ms : List ℕ)
    (heven : Even ms.length) (hpos : 0 < ms.length) :
    ∃ x : G, (blockWord h₀ h₁ false ms)[ms.length - 1]? =
      some (GGT.RelLetter.comp true x) := by
  obtain ⟨r, hr⟩ := heven
  cases r with
  | zero =>
      exfalso
      omega
  | succ r =>
      have hlen : ms.length = 2 + 2 * r := by omega
      obtain ⟨n₀, n₁, rest, rfl⟩ :
          ∃ n₀ n₁ rest, ms = n₀ :: n₁ :: rest := by
        cases ms with
        | nil =>
            exfalso
            simp at hlen
            omega
        | cons n₀ tail =>
            cases tail with
            | nil =>
                exfalso
                simp at hlen
                omega
            | cons n₁ rest => exact ⟨n₀, n₁, rest, rfl⟩
      have hrest : rest.length = 2 * r := by simp at hlen; omega
      cases rest with
      | nil =>
          refine ⟨h₁ ^ n₁, ?_⟩
          simp [blockWord]
      | cons n₂ tail =>
          have hrestPos : 0 < (n₂ :: tail).length := by simp
          have hrestEven : Even (n₂ :: tail).length := by
            refine ⟨r, ?_⟩
            omega
          obtain ⟨x, hx⟩ :=
            exists_last_true_of_even_blockWord h₀ h₁ (n₂ :: tail)
              hrestEven hrestPos
          refine ⟨x, ?_⟩
          simpa [blockWord] using hx
termination_by ms.length

/-- If the first letter of a rotation of the singleton-base relator is the
`q`-th block, the rotation itself is the canonical rotation by `q+1`. -/
theorem rotate_eq_at_block_of_head
    (base h₀ h₁ : G) (ms : List ℕ) {c q : ℕ}
    {s : Bool} {x : G}
    (hinj : ∀ b : Bool,
      Function.Injective (fun n : ℕ => (if b then h₁ else h₀) ^ n))
    (hnd : ms.Nodup)
    (hq : q < ms.length)
    (hhead : ((relatorWord₂ [base] h₀ h₁ ms).rotate c)[0]? =
      some (GGT.RelLetter.comp s x))
    (hqread : (blockWord h₀ h₁ false ms)[q]? =
      some (GGT.RelLetter.comp s x)) :
    (relatorWord₂ [base] h₀ h₁ ms).rotate c =
      (relatorWord₂ [base] h₀ h₁ ms).rotate (q + 1) := by
  let R := relatorWord₂ [base] h₀ h₁ ms
  have hRpos : 0 < R.length := by simp [R, length_relatorWord₂]
  have hqR : q + 1 < R.length := by simp [R, length_relatorWord₂]; omega
  have hcRead : R[c % R.length]? =
      some (GGT.RelLetter.comp s x) := by
    change (R.rotate c)[0]? = some (GGT.RelLetter.comp s x) at hhead
    rw [getElem?_rotate_head hRpos] at hhead
    exact hhead
  have hcBlock := blockIndex_of_relatorWord₂ hcRead
  obtain ⟨q', hq'eq, hq'lt, hq'read⟩ := hcBlock
  have hqeq : q' = q := by
    exact getElem?_eq_of_nodup (nodup_blockWord hinj false ms hnd)
      hq'read hqread
  subst q'
  simp only [List.length_singleton, Nat.one_add] at hq'eq
  rw [← List.rotate_mod R c, ← List.rotate_mod R (q + 1), hq'eq,
    Nat.mod_eq_of_lt hqR]

/-- Dropping through a block of index `s` starts the remaining run at `!s`. -/
theorem blockWord_drop_succ_of_read (h₀ h₁ : G) (ms : List ℕ)
    {q : ℕ} {s : Bool} {x : G}
    (hq : q + 1 < ms.length)
    (hread : (blockWord h₀ h₁ false ms)[q]? =
      some (GGT.RelLetter.comp s x)) :
    (blockWord h₀ h₁ false ms).drop (q + 1) =
      blockWord h₀ h₁ (!s) (ms.drop (q + 1)) := by
  obtain ⟨s', hs'⟩ := exists_blockWord_drop h₀ h₁ (q + 1) false ms
  obtain ⟨b, y, hnext⟩ := blockWord_getElem?_comp h₀ h₁ false ms hq
  have hb := blockWord_index_alternates h₀ h₁ false ms q s b x y hread hnext
  rw [hb] at hnext
  have hdropHead :
      ((blockWord h₀ h₁ false ms).drop (q + 1))[0]? =
        some (GGT.RelLetter.comp (!s) y) := by
    rw [List.getElem?_drop]
    simpa only [Nat.zero_add] using hnext
  have hdropPos : 0 < (ms.drop (q + 1)).length := by
    simp only [List.length_drop]
    omega
  obtain ⟨m, rest, hdrop⟩ :
      ∃ m rest, ms.drop (q + 1) = m :: rest := by
    cases h : ms.drop (q + 1) with
    | nil => simp [h] at hdropPos
    | cons m rest => exact ⟨m, rest, rfl⟩
  rw [hs', hdrop, blockWord_cons, List.getElem?_cons_zero] at hdropHead
  have heq := Option.some.inj hdropHead
  rw [GGT.RelLetter.comp.injEq] at heq
  rw [heq.1] at hs'
  exact hs'

end Bookkeeping

section ExactAvoidance

variable {G : Type u} [Group G]
  {A : HullGeneratingSet G} {N : Subgroup G}

/-- A nonempty peeled tail which has not yet reached the base seam is excluded
by the pure-window clause of the exact design. -/
theorem ExactRelatorDesign₂.peeledPure_not_mem
    (E : HypEmbeddedCore₂ A N) {baseLetter : G}
    {rho eps diffRadius W target : ℕ} {ms : List ℕ}
    (h : ExactRelatorDesign₂ E baseLetter rho eps diffRadius W target ms)
    {q k : ℕ} {s : Bool} {x : G}
    (hq : q + 1 < ms.length)
    (hread : (blockWord (E.lox false) (E.lox true) false ms)[q]? =
      some (GGT.RelLetter.comp s x))
    (hk0 : 0 < k) (hkW : k ≤ W)
    (hbefore : k ≤ ms.length - (q + 1)) :
    GGT.RelLetter.listVal
        (((blockWord (E.lox false) (E.lox true) false ms).drop (q + 1) ++
          GGT.RelLetter.base baseLetter ::
            (blockWord (E.lox false) (E.lox true) false ms).take q).take k)
      ∉ E.rel.fam s := by
  have hdrop := blockWord_drop_succ_of_read
    (E.lox false) (E.lox true) ms hq hread
  obtain ⟨n, hn⟩ : ∃ n, ms[q + 1]? = some n := by
    exact ⟨ms[q + 1], List.getElem?_eq_getElem hq⟩
  have hdropms : ms.drop (q + 1) = n :: ms.drop (q + 2) := by
    rw [List.drop_eq_getElem_cons hq, getElem_eq_of_getElem? hq hn]
  have hsplit : ms = ms.take (q + 1) ++ n :: ms.drop (q + 2) := by
    calc
      ms = ms.take (q + 1) ++ ms.drop (q + 1) :=
        (List.take_append_drop (q + 1) ms).symm
      _ = ms.take (q + 1) ++ n :: ms.drop (q + 2) := by rw [hdropms]
  have hpure := h.pureWindow_not_mem_anchorFamily hsplit s s
    (r := k - 1) (by omega)
  intro hmem
  apply hpure
  rw [List.take_append_of_le_length (by
      rw [List.length_drop, length_blockWord]
      exact hbefore), hdrop, hdropms, blockWord_cons,
    show k = (k - 1) + 1 by omega, List.take_succ_cons,
    RelWord.listVal_cons, GGT.RelLetter.val, blockWord_take] at hmem
  cases s <;> simpa using hmem

end ExactAvoidance

end HullSC
end GroupApproximation
