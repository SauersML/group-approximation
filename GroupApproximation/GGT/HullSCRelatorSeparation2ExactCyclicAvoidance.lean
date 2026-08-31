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

/-- Away from the base seam, the second letter after rotating to the `q`-th
block is the `(q+1)`-st block. -/
theorem getElem?_one_rotate_at_block_of_succ_lt
    (base h₀ h₁ : G) (ms : List ℕ) {q : ℕ}
    (hq : q + 1 < ms.length) :
    ((relatorWord₂ [base] h₀ h₁ ms).rotate (q + 1))[1]? =
      (blockWord h₀ h₁ false ms)[q + 1]? := by
  rw [rotate_relatorWord₂_singleton_at_block base h₀ h₁ ms (by omega)]
  have hqB : q < (blockWord h₀ h₁ false ms).length := by
    simpa only [length_blockWord] using (show q < ms.length by omega)
  have hdrop : (blockWord h₀ h₁ false ms).drop q =
      (blockWord h₀ h₁ false ms)[q]'hqB ::
        (blockWord h₀ h₁ false ms).drop (q + 1) :=
    List.drop_eq_getElem_cons hqB
  rw [hdrop]
  change
    ((blockWord h₀ h₁ false ms).drop (q + 1) ++
      GGT.RelLetter.base base ::
        (blockWord h₀ h₁ false ms).take q)[0]? =
      (blockWord h₀ h₁ false ms)[q + 1]?
  rw [List.getElem?_append_left]
  · rw [List.getElem?_drop]
  · simp only [List.length_drop, length_blockWord]
    omega

/-- At the final block, the second letter of the canonical rotation is the
unique base letter. -/
theorem getElem?_one_rotate_at_last_block
    (base h₀ h₁ : G) (ms : List ℕ) {q : ℕ}
    (hq : q + 1 = ms.length) :
    ((relatorWord₂ [base] h₀ h₁ ms).rotate (q + 1))[1]? =
      some (GGT.RelLetter.base base) := by
  rw [rotate_relatorWord₂_singleton_at_block base h₀ h₁ ms (by omega)]
  have hqB : q < (blockWord h₀ h₁ false ms).length := by
    rw [length_blockWord]
    omega
  have hdrop : (blockWord h₀ h₁ false ms).drop q =
      (blockWord h₀ h₁ false ms)[q]'hqB :: [] := by
    rw [List.drop_eq_getElem_cons hqB]
    apply congrArg (fun tail =>
      (blockWord h₀ h₁ false ms)[q]'hqB :: tail)
    apply List.drop_eq_nil_of_le
    rw [length_blockWord]
    omega
  rw [hdrop]
  change
    (GGT.RelLetter.base base ::
      (blockWord h₀ h₁ false ms).take q)[0]? =
        some (GGT.RelLetter.base base)
  simp

/-- If the run has at least two blocks, the third letter after its final block
is the first block (the second letter is the base seam). -/
theorem getElem?_two_rotate_at_last_block
    (base h₀ h₁ : G) (ms : List ℕ) {q : ℕ}
    (hq : q + 1 = ms.length) (hms2 : 2 ≤ ms.length) :
    ((relatorWord₂ [base] h₀ h₁ ms).rotate (q + 1))[2]? =
      (blockWord h₀ h₁ false ms)[0]? := by
  rw [rotate_relatorWord₂_singleton_at_block base h₀ h₁ ms (by omega)]
  have hqB : q < (blockWord h₀ h₁ false ms).length := by
    rw [length_blockWord]
    omega
  have hdrop : (blockWord h₀ h₁ false ms).drop q =
      (blockWord h₀ h₁ false ms)[q]'hqB :: [] := by
    rw [List.drop_eq_getElem_cons hqB]
    apply congrArg (fun tail =>
      (blockWord h₀ h₁ false ms)[q]'hqB :: tail)
    apply List.drop_eq_nil_of_le
    rw [length_blockWord]
    omega
  rw [hdrop]
  change ((blockWord h₀ h₁ false ms).take q)[0]? =
    (blockWord h₀ h₁ false ms)[0]?
  exact List.getElem?_take_of_lt (by omega)

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

/-- Once the peeled tail crosses the unique base letter, it is excluded by the
corrected cyclic `post/base/pre` clause. -/
theorem ExactRelatorDesign₂.peeledThroughBase_not_mem
    (E : HypEmbeddedCore₂ A N) {baseLetter : G}
    {rho eps diffRadius W target : ℕ} {ms : List ℕ}
    (h : ExactRelatorDesign₂ E baseLetter rho eps diffRadius W target ms)
    {q k : ℕ} {s : Bool} {x : G}
    (hq : q + 1 < ms.length)
    (hread : (blockWord (E.lox false) (E.lox true) false ms)[q]? =
      some (GGT.RelLetter.comp s x))
    (hkW : k ≤ W) (hklen : k ≤ ms.length)
    (hcross : ms.length - (q + 1) < k) :
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
  let r₀ := (ms.drop (q + 2)).length
  let r₁ := k - (ms.length - (q + 1)) - 1
  have hr₀W : r₀ ≤ W := by
    simp only [r₀, List.length_drop]
    omega
  have hr₁W : r₁ ≤ W := by omega
  have hr₁q : r₁ ≤ q := by
    simp only [r₁]
    omega
  have hthrough := h.throughBase_not_mem_anchorFamily hsplit s s false
    hr₀W hr₁W
  have hr₀all : (ms.drop (q + 2)).take r₀ = ms.drop (q + 2) := by
    simp only [r₀, List.take_length]
  rw [hr₀all] at hthrough
  intro hmem
  apply hthrough
  rw [List.take_append, List.take_of_length_le (le_of_lt (by
      simpa only [List.length_drop, length_blockWord] using hcross)),
    show k - ((blockWord (E.lox false) (E.lox true) false ms).drop
        (q + 1)).length = r₁ + 1 by
      simp only [List.length_drop, length_blockWord, r₁]
      omega,
    List.take_succ_cons, RelWord.listVal_append, hdrop, hdropms,
    blockWord_cons, RelWord.listVal_cons, GGT.RelLetter.val,
    blockWord_take, RelWord.listVal_cons, GGT.RelLetter.val] at hmem
  have htake : (ms.take q).take r₁ = (ms.take (q + 1)).take r₁ := by
    rw [List.take_take, List.take_take]
    congr 1
    omega
  rw [blockWord_take] at hmem
  rw [htake] at hmem
  cases s <;> simpa [mul_assoc] using hmem

/-- At the final block of an even run, peeling the `true` anchor leaves the
exceptional `base/false/...` seam controlled by `BaseFirstAvoidance`. -/
theorem ExactRelatorDesign₂.peeledLastBaseFirst_not_mem
    (E : HypEmbeddedCore₂ A N) {baseLetter : G}
    {rho eps diffRadius W target : ℕ} {ms : List ℕ}
    (h : ExactRelatorDesign₂ E baseLetter rho eps diffRadius W target ms)
    {q k : ℕ} (hq : q + 1 = ms.length)
    (hk2 : 2 ≤ k) (hkW : k ≤ W) (hklen : k ≤ ms.length) :
    GGT.RelLetter.listVal
        (((blockWord (E.lox false) (E.lox true) false ms).drop (q + 1) ++
          GGT.RelLetter.base baseLetter ::
            (blockWord (E.lox false) (E.lox true) false ms).take q).take k)
      ∉ E.rel.fam true := by
  obtain ⟨n, post, hms⟩ : ∃ n post, ms = n :: post := by
    cases ms with
    | nil =>
        exfalso
        simp at hklen
        omega
    | cons n post => exact ⟨n, post, rfl⟩
  have hbase := h.baseFirst_not_mem_trueFamily hms
    (r := k - 2) (by omega)
  intro hmem
  apply hbase
  have hdropnil :
      (blockWord (E.lox false) (E.lox true) false ms).drop (q + 1) = [] := by
    apply List.drop_eq_nil_of_le
    rw [length_blockWord]
    omega
  rw [hdropnil, List.nil_append,
    show k = (k - 1) + 1 by omega, List.take_succ_cons,
    RelWord.listVal_cons, GGT.RelLetter.val] at hmem
  have htakeq :
      ((blockWord (E.lox false) (E.lox true) false ms).take q).take (k - 1) =
        (blockWord (E.lox false) (E.lox true) false ms).take (k - 1) := by
    rw [List.take_take, Nat.min_eq_left]
    omega
  rw [htakeq, hms, blockWord_cons,
    show k - 1 = (k - 2) + 1 by omega, List.take_succ_cons,
    RelWord.listVal_cons, GGT.RelLetter.val, blockWord_take] at hmem
  simpa [mul_assoc] using hmem

/-- A positive bounded prefix of a direct cyclic relator, starting and ending
at component letters of the same index, cannot spell an element of that
peripheral subgroup. -/
theorem ExactRelatorDesign₂.directCyclicPrefix_not_mem
    (E : HypEmbeddedCore₂ A N) {baseLetter : G}
    {rho eps diffRadius W target : ℕ} {ms : List ℕ}
    (h : ExactRelatorDesign₂ E baseLetter rho eps diffRadius W target ms)
    (heven : Even ms.length) {c k : ℕ} {s : Bool} {x y : G}
    (hk0 : 0 < k) (hkW : k ≤ W)
    (hhead : ((relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms).rotate c)[0]?
      = some (GGT.RelLetter.comp s x))
    (hend : ((relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms).rotate c)[k]?
      = some (GGT.RelLetter.comp s y)) :
    GGT.RelLetter.listVal
        ((relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms).rotate c |>.take k)
      ∉ E.rel.fam s := by
  let R := relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms
  have hRpos : 0 < R.length := by simp [R, length_relatorWord₂]
  have hcRead := getElem?_of_rotate (l := R) (c := c) (d := 0)
    hRpos hhead
  obtain ⟨q, hqpos, hq, hqread⟩ := blockIndex_of_relatorWord₂ hcRead
  simp only [List.length_singleton] at hqpos
  have hcanon : R.rotate c = R.rotate (q + 1) :=
    rotate_eq_at_block_of_head baseLetter (E.lox false) (E.lox true) ms
      (by
        intro b
        cases b
        · simpa using injective_pow_lox₂ E false
        · simpa using injective_pow_lox₂ E true)
      h.2.1 hq hhead hqread
  change GGT.RelLetter.listVal ((R.rotate c).take k) ∉ E.rel.fam s
  rw [hcanon] at hend ⊢
  have hkR : k < R.length := by
    have hkrot := (List.getElem?_eq_some_iff.mp hend).choose
    simpa only [List.length_rotate] using hkrot
  have hklen : k ≤ ms.length := by
    simp only [R, length_relatorWord₂, List.length_singleton] at hkR
    omega
  rcases lt_or_eq_of_le (show q + 1 ≤ ms.length by omega) with hqnext | hqlast
  · have hsecond := getElem?_one_rotate_at_block_of_succ_lt
      baseLetter (E.lox false) (E.lox true) ms hqnext
    obtain ⟨b, z, hnext⟩ := blockWord_getElem?_comp
      (E.lox false) (E.lox true) false ms hqnext
    have hb := blockWord_index_alternates
      (E.lox false) (E.lox true) false ms q s b x z hqread hnext
    have hk2 : 2 ≤ k := by
      by_contra hnot
      have hk1 : k = 1 := by omega
      subst k
      rw [hsecond, hnext] at hend
      have heq := Option.some.inj hend
      rw [GGT.RelLetter.comp.injEq] at heq
      rw [hb] at heq
      cases s <;> simp at heq
    have htail :
        GGT.RelLetter.listVal
          (((blockWord (E.lox false) (E.lox true) false ms).drop (q + 1) ++
            GGT.RelLetter.base baseLetter ::
              (blockWord (E.lox false) (E.lox true) false ms).take q).take
                (k - 1)) ∉ E.rel.fam s := by
      rcases le_or_gt (k - 1) (ms.length - (q + 1)) with hbefore | hcross
      · exact h.peeledPure_not_mem E hqnext hqread (by omega) (by omega) hbefore
      · exact h.peeledThroughBase_not_mem E hqnext hqread (by omega) (by omega)
          hcross
    intro hmem
    apply htail
    have hword := take_succ_rotate_relatorWord₂_singleton_at_block
      baseLetter (E.lox false) (E.lox true) ms hq hqread (k := k - 1)
    have hword' : (R.rotate (q + 1)).take k =
        GGT.RelLetter.comp s x ::
          ((blockWord (E.lox false) (E.lox true) false ms).drop (q + 1) ++
            GGT.RelLetter.base baseLetter ::
              (blockWord (E.lox false) (E.lox true) false ms).take q).take
                (k - 1) := by
      rw [show k = (k - 1) + 1 by omega]
      exact hword
    rw [hword', RelWord.listVal_cons, GGT.RelLetter.val] at hmem
    obtain ⟨m, -, hxpow⟩ := blockWord_getElem?_exponent
      (E.lox false) (E.lox true) false ms q s x hqread
    have hxmem : x ∈ E.rel.fam s := by
      rw [hxpow]
      have hloxfam : E.lox s ∈ E.rel.fam s := by
        rw [E.fam_eq]
        exact E.lox_mem s
      cases s <;> simpa using pow_mem hloxfam m
    exact ((E.rel.fam s).mul_mem_cancel_left hxmem).mp hmem
  · have hsecond := getElem?_one_rotate_at_last_block
      baseLetter (E.lox false) (E.lox true) ms hqlast
    have hk2 : 2 ≤ k := by
      by_contra hnot
      have hk1 : k = 1 := by omega
      subst k
      rw [hsecond] at hend
      cases hend
    have hms0 : 0 < ms.length := by omega
    obtain ⟨z, hlast⟩ := exists_last_true_of_even_blockWord
      (E.lox false) (E.lox true) ms heven hms0
    have hqeq : q = ms.length - 1 := by omega
    rw [← hqeq] at hlast
    rw [hqread] at hlast
    have hs : s = true := (GGT.RelLetter.comp.inj (Option.some.inj hlast)).1
    subst s
    have hms2 : 2 ≤ ms.length := by
      obtain ⟨r, hr⟩ := heven
      omega
    have hthird := getElem?_two_rotate_at_last_block
      baseLetter (E.lox false) (E.lox true) ms hqlast hms2
    obtain ⟨b₀, z₀, hfirst⟩ := blockWord_getElem?_comp
      (E.lox false) (E.lox true) false ms (show 0 < ms.length by omega)
    have hb₀ : b₀ = false := by
      obtain ⟨n₀, post, hms⟩ : ∃ n₀ post, ms = n₀ :: post := by
        cases ms with
        | nil => simp at hms2
        | cons n₀ post => exact ⟨n₀, post, rfl⟩
      rw [hms, blockWord_cons, List.getElem?_cons_zero] at hfirst
      exact (GGT.RelLetter.comp.inj (Option.some.inj hfirst)).1.symm
    have hk3 : 3 ≤ k := by
      by_contra hnot
      have hk2eq : k = 2 := by omega
      subst k
      rw [hthird, hfirst] at hend
      have heq := GGT.RelLetter.comp.inj (Option.some.inj hend)
      rw [hb₀] at heq
      simp at heq
    have htail := h.peeledLastBaseFirst_not_mem E (k := k - 1)
      hqlast (by omega) (by omega) (by omega)
    intro hmem
    apply htail
    have hword := take_succ_rotate_relatorWord₂_singleton_at_block
      baseLetter (E.lox false) (E.lox true) ms hq hqread (k := k - 1)
    have hword' : (R.rotate (q + 1)).take k =
        GGT.RelLetter.comp true x ::
          ((blockWord (E.lox false) (E.lox true) false ms).drop (q + 1) ++
            GGT.RelLetter.base baseLetter ::
              (blockWord (E.lox false) (E.lox true) false ms).take q).take
                (k - 1) := by
      rw [show k = (k - 1) + 1 by omega]
      exact hword
    rw [hword', RelWord.listVal_cons, GGT.RelLetter.val] at hmem
    obtain ⟨m, -, hxpow⟩ := blockWord_getElem?_exponent
      (E.lox false) (E.lox true) false ms q true x hqread
    have hxmem : x ∈ E.rel.fam true := by
      rw [hxpow]
      have hloxfam : E.lox true ∈ E.rel.fam true := by
        rw [E.fam_eq]
        exact E.lox_mem true
      simpa using pow_mem hloxfam m
    exact ((E.rel.fam true).mul_mem_cancel_left hxmem).mp hmem

end ExactAvoidance

end HullSC
end GroupApproximation
