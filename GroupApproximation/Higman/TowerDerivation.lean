import GroupApproximation.Higman.NormalClosureProduct

/-!
# Chiodo's tower as a raw-word recursion

`Higman.RadicalDirectSum` reduces (B2) to the radical-membership predicate of a
single finitely presented group, and `Higman.NormalClosureProduct` expresses one
level of Chiodo's tower as a list of conjugation data.  This file puts the two
together into a recursion on the stage:

    TowerDeriv gen 0       v  =  evalRaw gen v = 1
    TowerDeriv gen (i + 1) v  =  ∃ a list of (conjugator, base, exponent),
                                 each base's power derivable at stage i, whose
                                 conjugates multiply to the value of v

and proves it equivalent to membership in `Chiodo.torsionTower`
(`mem_torsionTower_iff_towerDeriv`), hence to membership in the radical
(`mem_radical_iff_exists_towerDeriv`).

Everything in `TowerDeriv` is raw data --- lists of raw words and naturals ---
except the two equations `evalRaw gen v = 1` and `conjProd … = evalRaw gen v`,
which are instances of the group's word problem.  So what (B2) still owes is
only this: **that `∃ i, TowerDeriv gen i v` is recursively enumerable**, given
that the word problem is.  That is a flattening argument --- a derivation is a
list of claims, each justified by earlier ones, checked against its own prefix
--- of the kind `Higman.BlockSearch` already carried out for (B1), and it is
not done here.

The one piece of plumbing worth naming is `list_choice`: choosing a witness at
every element of a list, packaged so that the resulting list of pairs has
`map Prod.fst` equal to the original.  Without that equation the subsequent
`List.map_map` rewrites do not go through, and `List.attach` leaves them in a
shape that needs its own lemmas.
-/

namespace GroupApproximation
namespace Higman

variable {A : Type} [Group A]

/-! ## 1.  Choosing witnesses along a list -/

/-- **Dependent choice along a list**, in the form later `List.map_map`
rewrites can use. -/
theorem list_choice {α β : Type} (P : α → β → Prop) :
    ∀ l : List α, (∀ a ∈ l, ∃ b, P a b) →
      ∃ m : List (α × β), m.map Prod.fst = l ∧ ∀ q ∈ m, P q.1 q.2 := by
  intro l
  induction l with
  | nil =>
      intro _
      exact ⟨[], rfl, by simp⟩
  | cons a l ih =>
      intro h
      obtain ⟨b, hb⟩ := h a (by simp)
      obtain ⟨m, hm1, hm2⟩ := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
      refine ⟨(a, b) :: m, by simp [hm1], ?_⟩
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq'
      · exact hb
      · exact hm2 q hq'

/-! ## 2.  Powers, spelled as raw words -/

/-- The raw word spelling the `n`-th power of the word `v`. -/
def rawPow (v : RawWord) : ℕ → RawWord
  | 0 => []
  | n + 1 => v ++ rawPow v n

theorem evalRaw_rawPow (gen : ℕ → A) (v : RawWord) (n : ℕ) :
    evalRaw gen (rawPow v n) = evalRaw gen v ^ n := by
  induction n with
  | zero => simp [rawPow]
  | succ n ih =>
      show evalRaw gen (v ++ rawPow v n) = _
      rw [evalRaw_append, ih]
      exact (pow_succ' _ n).symm

/-! ## 3.  The derivation predicate -/

/-- **Chiodo's tower, as a recursion on raw data.** -/
def TowerDeriv (gen : ℕ → A) : ℕ → RawWord → Prop
  | 0, v => evalRaw gen v = 1
  | i + 1, v =>
      ∃ l : List (RawWord × RawWord × ℕ),
        (∀ p ∈ l, 0 < p.2.2 ∧ TowerDeriv gen i (rawPow p.2.1 p.2.2)) ∧
        conjProd (l.map fun p ↦ (evalRaw gen p.1, evalRaw gen p.2.1))
          = evalRaw gen v

@[simp] theorem towerDeriv_zero (gen : ℕ → A) (v : RawWord) :
    TowerDeriv gen 0 v ↔ evalRaw gen v = 1 := Iff.rfl

@[simp] theorem towerDeriv_succ (gen : ℕ → A) (i : ℕ) (v : RawWord) :
    TowerDeriv gen (i + 1) v ↔
      ∃ l : List (RawWord × RawWord × ℕ),
        (∀ p ∈ l, 0 < p.2.2 ∧ TowerDeriv gen i (rawPow p.2.1 p.2.2)) ∧
        conjProd (l.map fun p ↦ (evalRaw gen p.1, evalRaw gen p.2.1))
          = evalRaw gen v := Iff.rfl

/-! ## 4.  It computes the tower -/

theorem mem_torsionTower_iff_towerDeriv (gen : ℕ → A)
    (hspan : Subgroup.closure (Set.range gen) = ⊤) :
    ∀ (i : ℕ) (v : RawWord),
      evalRaw gen v ∈ Chiodo.torsionTower A i ↔ TowerDeriv gen i v := by
  intro i
  induction i with
  | zero =>
      intro v
      rw [towerDeriv_zero, Chiodo.torsionTower_zero, Subgroup.mem_bot]
  | succ i ih =>
      intro v
      rw [mem_torsionTower_succ_iff_raw gen hspan i (evalRaw gen v),
        towerDeriv_succ]
      constructor
      · rintro ⟨l, hl, heq⟩
        obtain ⟨m, hm1, hm2⟩ :=
          list_choice
            (fun (p : RawWord × RawWord) (n : ℕ) ↦
              0 < n ∧ evalRaw gen p.2 ^ n ∈ Chiodo.torsionTower A i) l hl
        refine ⟨m.map fun q ↦ (q.1.1, q.1.2, q.2), ?_, ?_⟩
        · intro p hp
          obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
          refine ⟨(hm2 q hq).1, ?_⟩
          rw [← ih]
          rw [evalRaw_rawPow]
          exact (hm2 q hq).2
        · rw [List.map_map, ← heq, ← hm1, List.map_map]
          rfl
      · rintro ⟨l, hl, heq⟩
        refine ⟨l.map fun p ↦ (p.1, p.2.1), ?_, ?_⟩
        · intro p hp
          obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
          refine ⟨q.2.2, (hl q hq).1, ?_⟩
          have h := (hl q hq).2
          rw [← ih, evalRaw_rawPow] at h
          exact h
        · rw [List.map_map, ← heq]
          rfl

/-! ## 5.  The radical -/

/-- **Radical membership, as a raw-word derivation.**  This is the predicate
(B2) has to make recursively enumerable. -/
theorem mem_radical_iff_exists_towerDeriv (gen : ℕ → A)
    (hspan : Subgroup.closure (Set.range gen) = ⊤) (v : RawWord) :
    evalRaw gen v ∈ Chiodo.torsionFreeRadical A ↔ ∃ i : ℕ, TowerDeriv gen i v := by
  rw [Chiodo.torsionFreeRadical_eq_torsionOmega, Chiodo.mem_torsionOmega_iff]
  exact exists_congr fun i => mem_torsionTower_iff_towerDeriv gen hspan i v

/-! ## 6.  Every atomic condition is a word-problem instance

`TowerDeriv` still mentions `conjProd`, a product formed in the group.  For a
certificate checker that has to be *computable*, every atomic condition must be
an instance of the word problem and nothing else.  `conjWord` spells the
product of conjugates as a raw word, and `towerDeriv_succ_iff_triv` then puts
the whole recursion in the form

    stage 0     :  the word `v` is trivial
    stage i + 1 :  a list of (conjugator, base, exponent) raw words, each base's
                   power derivable at stage `i`, with the single raw word
                   `conjWord l ++ invRaw v` trivial

in which the only non-syntactic conditions are two triviality tests.  That is
the interface the flattening needs. -/

/-- The raw word spelling the product of conjugates of a list of
(conjugator, base, exponent) triples. -/
def conjWord (l : List (RawWord × RawWord × ℕ)) : RawWord :=
  (l.map fun p ↦ p.1 ++ p.2.1 ++ invRaw p.1).flatten

theorem evalRaw_conjWord (gen : ℕ → A) (l : List (RawWord × RawWord × ℕ)) :
    evalRaw gen (conjWord l)
      = conjProd (l.map fun p ↦ (evalRaw gen p.1, evalRaw gen p.2.1)) := by
  induction l with
  | nil => simp [conjWord]
  | cons p l ih =>
      show evalRaw gen ((p.1 ++ p.2.1 ++ invRaw p.1) ++ conjWord l) = _
      rw [evalRaw_append, evalRaw_append, evalRaw_append, evalRaw_invRaw, ih]
      simp [conjProd_cons, mul_assoc]

/-- **The recursion, with only triviality tests left.** -/
theorem towerDeriv_succ_iff_triv (gen : ℕ → A) (i : ℕ) (v : RawWord) :
    TowerDeriv gen (i + 1) v ↔
      ∃ l : List (RawWord × RawWord × ℕ),
        (∀ p ∈ l, 0 < p.2.2 ∧ TowerDeriv gen i (rawPow p.2.1 p.2.2)) ∧
        evalRaw gen (conjWord l ++ invRaw v) = 1 := by
  rw [towerDeriv_succ]
  refine exists_congr fun l => and_congr_right fun _ => ?_
  rw [evalRaw_append, evalRaw_invRaw, evalRaw_conjWord, mul_inv_eq_one]

end Higman
end GroupApproximation
