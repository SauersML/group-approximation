import GroupApproximation.GGT.DGOIsolatedComponentBridge

/-!
# The alternating word `(a h)^n` in `Γ(G, X ⊔ ℋ)`

Dahmani--Guirardel--Osin's Theorem 6.11 produces a loxodromic element of the
form `a h` with `a ∈ X` and `h ∈ H_λ` far from `1` in `d̂_λ`, and every estimate
in its proof is read off the path labelled by the word

    a, h, a, h, …, a, h

`altWord a h n` is that word: `n` copies of the two-letter block `base a`,
`comp () h`.  This module is its calculus --- length, spelled element, letters,
vertices, and the component structure of `altWord a h n ++ u` for an arbitrary
continuation `u`.  Everything here is bookkeeping; the geometry is in
`GGT.DGOAlternatingCycle`.

## What the indices say

Positions of `altWord a h n` alternate: even positions carry the `X`-letter `a`
and odd positions carry the `H`-letter `h`.  So

* an even position is never the start of a component
  (`not_isCompStart_of_even`) --- it does not even carry an `H`-letter;
* an even position `j > 0` at most `2n` is never the start of a component
  either, for the opposite reason (`not_isCompStart_of_even_pos`): the letter
  *before* it is an `H`-letter, so the run through `j` began earlier.  This is
  the clause that matters at `j = 2n`, where the continuation `u` may begin with
  an `H`-letter of its own;
* every odd position `2t+1` with `t + 1 < n` starts a component of length one
  (`isComp_altWordAppend`), because both its neighbours are `X`-letters.  The
  hypothesis is `t + 1 < n` rather than `t < n`: the last block's `H`-letter sits
  next to the first letter of `u`, which may be an `H`-letter, and then the run
  is longer than one.

The vertices are `vertex v (altWord a h n) (2t) = v (ah)^t` and
`vertex v (altWord a h n) (2t+1) = v (ah)^t a`, which is what turns
`Connected` into a statement about powers of `a h`.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

/-! ## Reading a prefix of a concatenation -/

section Append

variable {G : Type u} [Group G] {Λ : Type w}

/-- **A vertex inside the first factor is a vertex of that factor.**  Both sides
are the basepoint times what the prefix of length `j` spells, and for
`j ≤ w.length` the two prefixes agree. -/
theorem vertex_append_left (v : G) (w u : List (RelLetter G Λ)) {j : ℕ}
    (hj : j ≤ w.length) : vertex v (w ++ u) j = vertex v w j := by
  rw [vertex_eq_mul_listVal_take, vertex_eq_mul_listVal_take,
    List.take_append_of_le_length hj]

end Append

/-! ## The word -/

variable {G : Type u} [Group G]

/-- **The alternating word `(a h)^n`**, as a word in `X ⊔ ℋ`: `n` copies of the
block `base a`, `comp () h`. -/
def altWord (a h : G) : ℕ → List (RelLetter G Unit)
  | 0 => []
  | n + 1 => RelLetter.base a :: RelLetter.comp () h :: altWord a h n

omit [Group G] in
@[simp] theorem altWord_zero (a h : G) :
    altWord a h 0 = ([] : List (RelLetter G Unit)) := rfl

omit [Group G] in
@[simp] theorem altWord_succ (a h : G) (n : ℕ) :
    altWord a h (n + 1)
      = RelLetter.base a :: RelLetter.comp () h :: altWord a h n := rfl

omit [Group G] in
@[simp] theorem length_altWord (a h : G) (n : ℕ) :
    (altWord a h n).length = 2 * n := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [altWord_succ, List.length_cons, List.length_cons, ih]
      omega

@[simp] theorem listVal_altWord (a h : G) (n : ℕ) :
    RelLetter.listVal (altWord a h n) = (a * h) ^ n := by
  induction n with
  | zero => simp [RelLetter.listVal]
  | succ m ih =>
      rw [altWord_succ]
      simp only [RelLetter.listVal, List.map_cons, List.prod_cons,
        RelLetter.val] at ih ⊢
      rw [ih, pow_succ', mul_assoc]

omit [Group G] in
/-- Concatenating blocks concatenates words. -/
theorem altWord_append (a h : G) (m n : ℕ) :
    altWord a h (m + n) = altWord a h m ++ altWord a h n := by
  induction m with
  | zero => simp
  | succ p ih =>
      have hidx : p + 1 + n = p + n + 1 := by omega
      rw [hidx, altWord_succ, altWord_succ, ih]
      rfl

/-- Every letter of the word is admissible. -/
theorem isLetter_of_mem_altWord (D : RelGenSet G Unit) {a h : G}
    (ha : a ∈ D.base) (hh : h ∈ D.fam ()) (n : ℕ) :
    ∀ x ∈ altWord a h n, D.IsLetter x := by
  induction n with
  | zero => simp
  | succ m ih =>
      intro x hx
      rw [altWord_succ] at hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ha
      · rcases List.mem_cons.mp hx' with rfl | hx''
        · exact hh
        · exact ih x hx''

/-! ## Letters, by parity of the position -/

omit [Group G] in
/-- **The letters alternate.**  Even positions carry `a`, odd positions
carry `h`. -/
theorem getElem_altWord (a h : G) :
    ∀ (n j : ℕ) (hj : j < (altWord a h n).length),
      (altWord a h n)[j]'hj
        = if j % 2 = 0 then RelLetter.base a else RelLetter.comp () h := by
  intro n
  induction n with
  | zero =>
      intro j hj
      simp only [altWord_zero, List.length_nil] at hj
      exact absurd hj (by omega)
  | succ m ih =>
      intro j hj
      rcases j with _ | j'
      · simp
      · rcases j' with _ | k
        · simp
        · have hk : k < (altWord a h m).length := by
            rw [altWord_succ, List.length_cons, List.length_cons] at hj
            omega
          have hget : (altWord a h (m + 1))[k + 1 + 1]'hj
              = (altWord a h m)[k]'hk := rfl
          rw [hget, ih k hk]
          have hmod : (k + 1 + 1) % 2 = k % 2 := by omega
          rw [hmod]

omit [Group G] in
theorem getElem_altWord_even (a h : G) {n j : ℕ} (hj : j % 2 = 0)
    (hlt : j < (altWord a h n).length) :
    (altWord a h n)[j]'hlt = RelLetter.base a := by
  rw [getElem_altWord a h n j hlt, if_pos hj]

omit [Group G] in
theorem getElem_altWord_odd (a h : G) {n j : ℕ} (hj : j % 2 = 1)
    (hlt : j < (altWord a h n).length) :
    (altWord a h n)[j]'hlt = RelLetter.comp () h := by
  rw [getElem_altWord a h n j hlt, if_neg (by omega)]

omit [Group G] in
theorem getElem_altWordAppend_even (a h : G) (u : List (RelLetter G Unit))
    {n j : ℕ} (hjn : j < 2 * n) (hj : j % 2 = 0)
    (hlt : j < (altWord a h n ++ u).length) :
    (altWord a h n ++ u)[j]'hlt = RelLetter.base a := by
  have h1 : j < (altWord a h n).length := by rw [length_altWord]; omega
  rw [List.getElem_append_left h1]
  exact getElem_altWord_even a h hj h1

omit [Group G] in
theorem getElem_altWordAppend_odd (a h : G) (u : List (RelLetter G Unit))
    {n j : ℕ} (hjn : j < 2 * n) (hj : j % 2 = 1)
    (hlt : j < (altWord a h n ++ u).length) :
    (altWord a h n ++ u)[j]'hlt = RelLetter.comp () h := by
  have h1 : j < (altWord a h n).length := by rw [length_altWord]; omega
  rw [List.getElem_append_left h1]
  exact getElem_altWord_odd a h hj h1

/-! ## Vertices -/

theorem vertex_altWord_two_mul (a h v : G) {n t : ℕ} (ht : t ≤ n) :
    vertex v (altWord a h n) (2 * t) = v * (a * h) ^ t := by
  have hsplit : altWord a h n = altWord a h t ++ altWord a h (n - t) := by
    rw [← altWord_append]
    congr 1
    omega
  have hTake : (altWord a h n).take (2 * t) = altWord a h t := by
    rw [hsplit,
      List.take_append_of_le_length (by simp),
      List.take_of_length_le (by simp)]
  rw [vertex_eq_mul_listVal_take, hTake, listVal_altWord]

theorem vertex_altWord_two_mul_succ (a h v : G) {n t : ℕ} (ht : t < n) :
    vertex v (altWord a h n) (2 * t + 1) = v * (a * h) ^ t * a := by
  have hlt : 2 * t < (altWord a h n).length := by rw [length_altWord]; omega
  rw [vertex_succ (altWord a h n) v (2 * t) hlt,
    vertex_altWord_two_mul a h v (le_of_lt ht),
    getElem_altWord_even a h (by omega) hlt]
  rfl

theorem vertex_altWordAppend_two_mul (a h v : G) (u : List (RelLetter G Unit))
    {n t : ℕ} (ht : t ≤ n) :
    vertex v (altWord a h n ++ u) (2 * t) = v * (a * h) ^ t := by
  rw [vertex_append_left v _ u (by rw [length_altWord]; omega)]
  exact vertex_altWord_two_mul a h v ht

theorem vertex_altWordAppend_two_mul_succ (a h v : G)
    (u : List (RelLetter G Unit)) {n t : ℕ} (ht : t < n) :
    vertex v (altWord a h n ++ u) (2 * t + 1) = v * (a * h) ^ t * a := by
  rw [vertex_append_left v _ u (by rw [length_altWord]; omega)]
  exact vertex_altWord_two_mul_succ a h v ht

/-! ## The component structure -/

omit [Group G] in
/-- **An `H`-letter of the alternating part is a component on its own.**  Both
its neighbours are `X`-letters, so the run through it is the single position
`2t+1`.  The hypothesis `t + 1 < n` keeps the position `2t+2` inside the
alternating part: at `t + 1 = n` the letter after it is the first letter of the
continuation `u`, which may be an `H`-letter. -/
theorem isComp_altWordAppend (a h : G) (u : List (RelLetter G Unit)) {n t : ℕ}
    (ht : t + 1 < n) :
    IsComp () (altWord a h n ++ u) (2 * t + 1) (2 * t + 2) := by
  have hlen : (altWord a h n ++ u).length = 2 * n + u.length := by
    rw [List.length_append, length_altWord]
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · intro j hj1 hj2 hjw
    have hje : j = 2 * t + 1 := by omega
    subst hje
    rw [getElem_altWordAppend_odd a h u (by omega) (by omega) hjw]
    rfl
  · intro j hj hjw
    have hje : j = 2 * t := by omega
    subst hje
    rw [getElem_altWordAppend_even a h u (by omega) (by omega) hjw]
    exact not_false
  · intro hk
    rw [getElem_altWordAppend_even a h u (by omega) (by omega) hk]
    exact not_false

omit [Group G] in
/-- An even position of the alternating part carries an `X`-letter, so it starts
no component. -/
theorem not_isCompStart_of_even (a h : G) (u : List (RelLetter G Unit))
    {n j : ℕ} (hjn : j < 2 * n) (hj : j % 2 = 0) :
    ¬ IsCompStart () (altWord a h n ++ u) j := by
  rintro ⟨k, hcomp⟩
  have hjw : j < (altWord a h n ++ u).length := by
    have h1 := hcomp.1
    have h2 := hcomp.2.1
    omega
  have hc := hcomp.2.2.1 j le_rfl hcomp.1 hjw
  rw [getElem_altWordAppend_even a h u hjn hj hjw] at hc
  exact hc

omit [Group G] in
/-- A positive even position at most `2n` is preceded by an `H`-letter, so it
starts no component either: the run through it began one position earlier.  This
is the clause that excludes `j = 2n`, where the continuation may begin with an
`H`-letter. -/
theorem not_isCompStart_of_even_pos (a h : G) (u : List (RelLetter G Unit))
    {n j : ℕ} (hj0 : 0 < j) (hjn : j ≤ 2 * n) (hj : j % 2 = 0) :
    ¬ IsCompStart () (altWord a h n ++ u) j := by
  rintro ⟨k, hcomp⟩
  have hpred : j - 1 < (altWord a h n ++ u).length := by
    rw [List.length_append, length_altWord]
    omega
  have hc := hcomp.2.2.2.1 (j - 1) (by omega) hpred
  rw [getElem_altWordAppend_odd a h u (by omega) (by omega) hpred] at hc
  exact hc rfl

omit [Group G] in
/-- Inside the alternating part every component start is odd. -/
theorem odd_of_isCompStart_lt (a h : G) (u : List (RelLetter G Unit))
    {n j : ℕ} (hjn : j < 2 * n)
    (hstart : IsCompStart () (altWord a h n ++ u) j) : j % 2 = 1 := by
  by_contra hne
  exact not_isCompStart_of_even a h u hjn (by omega) hstart

end OsinComponents
end GGT
end GroupApproximation
