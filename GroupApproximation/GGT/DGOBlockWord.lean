import GroupApproximation.GGT.DGOAlternatingWord

/-!
# The block word `(w h)^n`, for a word `w` and a letter `h` of `H lam`

`GGT/DGOAlternatingWord.lean` builds the path labelled `a, h, a, h, …` for a
single letter `a ∈ X`, which is what Dahmani--Guirardel--Osin's Theorem 6.11
needs.  Hull's Lemma `yi` needs the same construction with `a` replaced by a
*word*: it applies Corollary 6.12 to `g = a₁ ⋯ a_{k-1}` over the alphabet
`𝒜 ⊔ E(f₁) ⊔ … ⊔ E(f_k)`, where each `aᵢ` is a letter of a *different* member of
the family, so `g` is a product of `k-1` letters and not a letter.  This module
is that generalisation --- the word

    w, h, w, h, …, w, h

for an arbitrary admissible `w` --- and the alternating word is its
`w = [base a]` case.

## The hypothesis that replaces "the neighbours are `X`-letters"

For the two-letter block, the `h`-letter is a component of its own because both
its neighbours carry `X`-letters.  For a general block the neighbours are the
last letter of `w` and the first letter of the next copy of `w`, so what is
needed is that **no letter of `w` is a `lam`-letter**.  That is exactly Hull's
configuration, `aᵢ` being an `E(fᵢ)`-letter with `i ≠ lam`, and it is `hno`
below.  It does more than isolate the `h`-letters: it makes every position
inside a copy of `w` fail to start a `lam`-component at all, so the parity
bookkeeping of the two-letter case is replaced by a hypothesis that does the
same work more directly (`not_isCompStart_of_mem_pre`).

`0 < w.length` is needed too, and is not restrictive: `w = []` spells `g = 1`,
which lies in `H lam`, and the consumers exclude that.

## Indices

Positions of `blockWord lam w h n` are `t * (r + 1) + j` with `r = w.length`,
`t < n` and `j ≤ r`: the letter is `w[j]` for `j < r`, and `h` for `j = r`.  The
vertex at the `h`-letter of block `t` is `v * (a h)^t * a` with `a = listVal w`
--- the same group elements as in the two-letter case, which is why every
connectedness computation of `GGT/DGOAlternatingCycle.lean` carries over
unchanged.

Index facts are proved for `getElem?` first.  `getElem` carries a proof of the
bound, so rewriting the list underneath it needs `List.getElem_of_eq` and a
transported proof; `getElem?` carries none and can be rewritten freely.
`getElem_eq_of_getElem?_eq` reads the results back.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

/-- Read a `getElem?` fact back as a `getElem` fact. -/
theorem getElem_eq_of_getElem?_eq {α : Type u} {l : List α} {i : ℕ} {x : α}
    (hi : i < l.length) (h : l[i]? = some x) : l[i]'hi = x := by
  rw [List.getElem?_eq_getElem hi] at h
  exact Option.some.inj h

/-! ## The word -/

section Combinatorics

variable {G : Type u} {Λ : Type w}

/-- **The block word**: `n` copies of the block `pre` followed by the
`lam`-letter `h`. -/
def blockWord (lam : Λ) (pre : List (RelLetter G Λ)) (h : G) :
    ℕ → List (RelLetter G Λ)
  | 0 => []
  | n + 1 => pre ++ RelLetter.comp lam h :: blockWord lam pre h n

@[simp] theorem blockWord_zero (lam : Λ) (pre : List (RelLetter G Λ)) (h : G) :
    blockWord lam pre h 0 = ([] : List (RelLetter G Λ)) := rfl

@[simp] theorem blockWord_succ (lam : Λ) (pre : List (RelLetter G Λ)) (h : G)
    (n : ℕ) :
    blockWord lam pre h (n + 1)
      = pre ++ RelLetter.comp lam h :: blockWord lam pre h n := rfl

@[simp] theorem length_blockWord (lam : Λ) (pre : List (RelLetter G Λ)) (h : G)
    (n : ℕ) : (blockWord lam pre h n).length = n * (pre.length + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [blockWord_succ, List.length_append, List.length_cons, ih]
      ring

/-- Concatenating blocks concatenates words. -/
theorem blockWord_append (lam : Λ) (pre : List (RelLetter G Λ)) (h : G)
    (m n : ℕ) :
    blockWord lam pre h (m + n)
      = blockWord lam pre h m ++ blockWord lam pre h n := by
  induction m with
  | zero => simp
  | succ p ih =>
      have hidx : p + 1 + n = p + n + 1 := by omega
      rw [hidx, blockWord_succ, blockWord_succ, ih]
      simp

/-- Splitting off the first `t` blocks, with the next one displayed.  The tail
`q` is a parameter rather than `n - t - 1`, so that substituting `n` cannot
rewrite the residual on the right. -/
theorem blockWord_split (lam : Λ) (pre : List (RelLetter G Λ)) (h : G)
    {n t q : ℕ} (hn : n = t + q + 1) :
    blockWord lam pre h n
      = blockWord lam pre h t
          ++ (pre ++ RelLetter.comp lam h :: blockWord lam pre h q) := by
  subst hn
  show blockWord lam pre h (t + (q + 1)) = _
  rw [blockWord_append, blockWord_succ]

/-- The block part of the cycle is long enough to contain block `t`. -/
theorem lt_length_blockWord (lam : Λ) (pre : List (RelLetter G Λ)) (h : G)
    {n t : ℕ} (htn : t < n) :
    t * (pre.length + 1) + pre.length < (blockWord lam pre h n).length := by
  rw [length_blockWord]
  calc t * (pre.length + 1) + pre.length
      < t * (pre.length + 1) + (pre.length + 1) := by omega
    _ = (t + 1) * (pre.length + 1) := by ring
    _ ≤ n * (pre.length + 1) := Nat.mul_le_mul_right _ htn

/-! ## Letters, by position inside the block -/

theorem getElem?_blockWord_pre (lam : Λ) (pre : List (RelLetter G Λ)) (h : G)
    {n t j : ℕ} (htn : t < n) (hjr : j < pre.length) :
    (blockWord lam pre h n)[t * (pre.length + 1) + j]? = pre[j]? := by
  have hle : (blockWord lam pre h t).length ≤ t * (pre.length + 1) + j := by
    rw [length_blockWord]
    exact Nat.le_add_right _ _
  rw [blockWord_split lam pre h (n := n) (t := t) (q := n - t - 1) (by omega), List.getElem?_append_right hle,
    length_blockWord, Nat.add_sub_cancel_left, List.getElem?_append_left hjr]

theorem getElem?_blockWord_comp (lam : Λ) (pre : List (RelLetter G Λ)) (h : G)
    {n t : ℕ} (htn : t < n) :
    (blockWord lam pre h n)[t * (pre.length + 1) + pre.length]?
      = some (RelLetter.comp lam h) := by
  have hle : (blockWord lam pre h t).length
      ≤ t * (pre.length + 1) + pre.length := by
    rw [length_blockWord]
    exact Nat.le_add_right _ _
  rw [blockWord_split lam pre h (n := n) (t := t) (q := n - t - 1) (by omega), List.getElem?_append_right hle,
    length_blockWord, Nat.add_sub_cancel_left,
    List.getElem?_append_right (le_refl pre.length), Nat.sub_self,
    List.getElem?_cons_zero]

theorem getElem?_blockWordAppend_pre (lam : Λ) (pre : List (RelLetter G Λ))
    (h : G) (u : List (RelLetter G Λ)) {n t j : ℕ} (htn : t < n)
    (hjr : j < pre.length) :
    (blockWord lam pre h n ++ u)[t * (pre.length + 1) + j]? = pre[j]? := by
  have hlt : t * (pre.length + 1) + j < (blockWord lam pre h n).length := by
    have := lt_length_blockWord lam pre h htn
    omega
  rw [List.getElem?_append_left hlt]
  exact getElem?_blockWord_pre lam pre h htn hjr

theorem getElem?_blockWordAppend_comp (lam : Λ) (pre : List (RelLetter G Λ))
    (h : G) (u : List (RelLetter G Λ)) {n t : ℕ} (htn : t < n) :
    (blockWord lam pre h n ++ u)[t * (pre.length + 1) + pre.length]?
      = some (RelLetter.comp lam h) := by
  rw [List.getElem?_append_left (lt_length_blockWord lam pre h htn)]
  exact getElem?_blockWord_comp lam pre h htn

theorem getElem_blockWordAppend_pre (lam : Λ) (pre : List (RelLetter G Λ))
    (h : G) (u : List (RelLetter G Λ)) {n t j : ℕ} (htn : t < n)
    (hjr : j < pre.length)
    (hlt : t * (pre.length + 1) + j < (blockWord lam pre h n ++ u).length) :
    (blockWord lam pre h n ++ u)[t * (pre.length + 1) + j]'hlt = pre[j]'hjr :=
  getElem_eq_of_getElem?_eq hlt
    ((getElem?_blockWordAppend_pre lam pre h u htn hjr).trans
      (List.getElem?_eq_getElem hjr))

theorem getElem_blockWordAppend_comp (lam : Λ) (pre : List (RelLetter G Λ))
    (h : G) (u : List (RelLetter G Λ)) {n t : ℕ} (htn : t < n)
    (hlt : t * (pre.length + 1) + pre.length
      < (blockWord lam pre h n ++ u).length) :
    (blockWord lam pre h n ++ u)[t * (pre.length + 1) + pre.length]'hlt
      = RelLetter.comp lam h :=
  getElem_eq_of_getElem?_eq hlt (getElem?_blockWordAppend_comp lam pre h u htn)

/-! ## The component structure -/

/-- **The `h`-letter of a block is a `lam`-component on its own.**  Its two
neighbours are letters of `pre`, and `hno` says no letter of `pre` is a
`lam`-letter.  The hypothesis `t + 1 < n` keeps the following position inside
the block part, where the letter is `pre[0]`; at `t + 1 = n` the next letter is
the first letter of the continuation `u`, which may be a `lam`-letter. -/
theorem isComp_blockWordAppend (lam : Λ) (pre : List (RelLetter G Λ)) (h : G)
    (u : List (RelLetter G Λ)) (hno : ∀ c ∈ pre, ¬ c.IsCompOf lam)
    (hr : 0 < pre.length) {n t : ℕ} (htn : t + 1 < n) :
    IsComp lam (blockWord lam pre h n ++ u)
      (t * (pre.length + 1) + pre.length)
      (t * (pre.length + 1) + pre.length + 1) := by
  have hlen : (blockWord lam pre h n ++ u).length
      = n * (pre.length + 1) + u.length := by
    rw [List.length_append, length_blockWord]
  have hnext := lt_length_blockWord lam pre h (n := n) (t := t + 1) (by omega)
  have hexp : (t + 1) * (pre.length + 1)
      = t * (pre.length + 1) + pre.length + 1 := by ring
  rw [length_blockWord] at hnext
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · intro j hj1 hj2 hjw
    have hje : j = t * (pre.length + 1) + pre.length := by omega
    subst hje
    rw [getElem_blockWordAppend_comp lam pre h u (by omega) hjw]
    rfl
  · intro j hj hjw
    have hje : j = t * (pre.length + 1) + (pre.length - 1) := by omega
    subst hje
    rw [getElem_blockWordAppend_pre lam pre h u (n := n) (t := t)
      (j := pre.length - 1) (by omega) (by omega) hjw]
    exact hno _ (List.getElem_mem _)
  · intro hk
    have hq : (blockWord lam pre h n ++ u)[t * (pre.length + 1)
        + pre.length + 1]? = pre[0]? := by
      have hidx : t * (pre.length + 1) + pre.length + 1
          = (t + 1) * (pre.length + 1) + 0 := by omega
      rw [hidx]
      exact getElem?_blockWordAppend_pre lam pre h u (by omega) hr
    rw [getElem_eq_of_getElem?_eq hk (hq.trans (List.getElem?_eq_getElem hr))]
    exact hno _ (List.getElem_mem _)

/-- **A position inside a copy of `pre` starts no `lam`-component**, because it
does not carry a `lam`-letter. -/
theorem not_isCompStart_of_mem_pre (lam : Λ) (pre : List (RelLetter G Λ))
    (h : G) (u : List (RelLetter G Λ)) (hno : ∀ c ∈ pre, ¬ c.IsCompOf lam)
    {n t j : ℕ} (htn : t < n) (hjr : j < pre.length) :
    ¬ IsCompStart lam (blockWord lam pre h n ++ u)
        (t * (pre.length + 1) + j) := by
  rintro ⟨k, hcomp⟩
  have hjw : t * (pre.length + 1) + j < (blockWord lam pre h n ++ u).length := by
    have h1 := hcomp.1
    have h2 := hcomp.2.1
    omega
  have hc := hcomp.2.2.1 _ le_rfl hcomp.1 hjw
  rw [getElem_blockWordAppend_pre lam pre h u htn hjr hjw] at hc
  exact hno _ (List.getElem_mem _) hc

/-- **The first position after the block part starts no `lam`-component**: the
letter before it is the last `h`.  This is the clause that survives an arbitrary
continuation `u`, which may itself begin with a `lam`-letter. -/
theorem not_isCompStart_boundary (lam : Λ) (pre : List (RelLetter G Λ)) (h : G)
    (u : List (RelLetter G Λ)) {n : ℕ} (hn : 0 < n) :
    ¬ IsCompStart lam (blockWord lam pre h n ++ u) (n * (pre.length + 1)) := by
  rintro ⟨k, hcomp⟩
  have hlen : (blockWord lam pre h n ++ u).length
      = n * (pre.length + 1) + u.length := by
    rw [List.length_append, length_blockWord]
  have hn1 : n = (n - 1) + 1 := by omega
  have hexp : (n - 1) * (pre.length + 1) + pre.length + 1
      = n * (pre.length + 1) := by
    calc (n - 1) * (pre.length + 1) + pre.length + 1
        = ((n - 1) + 1) * (pre.length + 1) := by ring
      _ = n * (pre.length + 1) := by rw [← hn1]
  have hpred : (n - 1) * (pre.length + 1) + pre.length
      < (blockWord lam pre h n ++ u).length := by omega
  have hc := hcomp.2.2.2.1 ((n - 1) * (pre.length + 1) + pre.length)
    (by omega) hpred
  rw [getElem_blockWordAppend_comp lam pre h u (by omega) hpred] at hc
  exact hc rfl

/-- **Every `lam`-component start inside the block part is an `h`-position.** -/
theorem exists_of_isCompStart_lt (lam : Λ) (pre : List (RelLetter G Λ)) (h : G)
    (u : List (RelLetter G Λ)) (hno : ∀ c ∈ pre, ¬ c.IsCompOf lam)
    {n j : ℕ} (hjn : j < n * (pre.length + 1))
    (hstart : IsCompStart lam (blockWord lam pre h n ++ u) j) :
    ∃ t : ℕ, t < n ∧ j = t * (pre.length + 1) + pre.length := by
  have hdm : j = (j / (pre.length + 1)) * (pre.length + 1)
      + j % (pre.length + 1) := by
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod j (pre.length + 1)).symm
  have htn : j / (pre.length + 1) < n := by
    by_contra hcon
    have hge : n ≤ j / (pre.length + 1) := by omega
    have hbig : n * (pre.length + 1) ≤ j := by
      calc n * (pre.length + 1)
          ≤ (j / (pre.length + 1)) * (pre.length + 1) :=
            Nat.mul_le_mul_right _ hge
        _ ≤ j := Nat.div_mul_le_self _ _
    omega
  refine ⟨j / (pre.length + 1), htn, ?_⟩
  by_contra hcon
  have hmod : j % (pre.length + 1) < pre.length + 1 :=
    Nat.mod_lt _ (by omega)
  have hlt : j % (pre.length + 1) < pre.length := by omega
  refine not_isCompStart_of_mem_pre lam pre h u hno htn hlt ?_
  rw [← hdm]
  exact hstart

/-! ## Prefixes -/

/-- The prefix of the cycle up to the start of block `t`. -/
theorem take_blockWordAppend_block (lam : Λ) (pre : List (RelLetter G Λ))
    (h : G) (u : List (RelLetter G Λ)) {n t : ℕ} (htn : t ≤ n) :
    (blockWord lam pre h n ++ u).take (t * (pre.length + 1))
      = blockWord lam pre h t := by
  have hsum : t + (n - t) = n := by omega
  have hsplit : blockWord lam pre h n
      = blockWord lam pre h t ++ blockWord lam pre h (n - t) := by
    rw [← blockWord_append, hsum]
  have hle : t * (pre.length + 1) ≤ (blockWord lam pre h n).length := by
    rw [length_blockWord]
    exact Nat.mul_le_mul_right _ htn
  rw [List.take_append_of_le_length hle, hsplit,
    List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]

/-- The prefix of the cycle up to the `h`-letter of block `t`. -/
theorem take_blockWordAppend_comp (lam : Λ) (pre : List (RelLetter G Λ))
    (h : G) (u : List (RelLetter G Λ)) {n t : ℕ} (htn : t < n) :
    (blockWord lam pre h n ++ u).take (t * (pre.length + 1) + pre.length)
      = blockWord lam pre h t ++ pre := by
  have hle : t * (pre.length + 1) + pre.length
      ≤ (blockWord lam pre h n).length :=
    le_of_lt (lt_length_blockWord lam pre h htn)
  have hlen : (blockWord lam pre h t).length = t * (pre.length + 1) :=
    length_blockWord lam pre h t
  rw [List.take_append_of_le_length hle, blockWord_split lam pre h (n := n) (t := t) (q := n - t - 1) (by omega),
    List.take_append, hlen, Nat.add_sub_cancel_left,
    List.take_of_length_le (by rw [hlen]; exact Nat.le_add_right _ _),
    List.take_append_of_le_length (le_refl _), List.take_of_length_le (le_refl _)]

end Combinatorics

/-! ## What the word spells, and where its vertices are -/

section Metric

variable {G : Type u} [Group G] {Λ : Type w}

@[simp] theorem listVal_blockWord (lam : Λ) (pre : List (RelLetter G Λ)) (h : G)
    (n : ℕ) :
    RelLetter.listVal (blockWord lam pre h n)
      = (RelLetter.listVal pre * h) ^ n := by
  induction n with
  | zero => simp [RelLetter.listVal]
  | succ m ih =>
      rw [blockWord_succ, listVal_append]
      simp only [RelLetter.listVal, List.map_cons, List.prod_cons,
        RelLetter.val] at ih ⊢
      rw [ih, pow_succ', ← mul_assoc]

/-- Every letter of the block word is admissible. -/
theorem isLetter_of_mem_blockWord (D : RelGenSet G Λ) (lam : Λ)
    {pre : List (RelLetter G Λ)} (hpre : ∀ c ∈ pre, D.IsLetter c) {h : G}
    (hh : h ∈ D.fam lam) (n : ℕ) :
    ∀ c ∈ blockWord lam pre h n, D.IsLetter c := by
  induction n with
  | zero => simp
  | succ m ih =>
      intro c hc
      rw [blockWord_succ] at hc
      rcases List.mem_append.mp hc with hc' | hc'
      · exact hpre c hc'
      · rcases List.mem_cons.mp hc' with rfl | hc''
        · exact hh
        · exact ih c hc''

theorem vertex_blockWordAppend_block (lam : Λ) (pre : List (RelLetter G Λ))
    (h v : G) (u : List (RelLetter G Λ)) {n t : ℕ} (htn : t ≤ n) :
    vertex v (blockWord lam pre h n ++ u) (t * (pre.length + 1))
      = v * (RelLetter.listVal pre * h) ^ t := by
  rw [vertex_eq_mul_listVal_take, take_blockWordAppend_block lam pre h u htn,
    listVal_blockWord]

/-- The vertex at the `h`-letter of block `t`. -/
theorem vertex_blockWordAppend_comp (lam : Λ) (pre : List (RelLetter G Λ))
    (h v : G) (u : List (RelLetter G Λ)) {n t : ℕ} (htn : t < n) :
    vertex v (blockWord lam pre h n ++ u) (t * (pre.length + 1) + pre.length)
      = v * (RelLetter.listVal pre * h) ^ t * RelLetter.listVal pre := by
  rw [vertex_eq_mul_listVal_take, take_blockWordAppend_comp lam pre h u htn,
    listVal_append, listVal_blockWord, mul_assoc]

end Metric

end OsinComponents
end GGT
end GroupApproximation
