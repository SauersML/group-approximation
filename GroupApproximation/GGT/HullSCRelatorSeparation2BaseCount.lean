import GroupApproximation.GGT.HullSCRelatorSeparation2Word

/-!
# Every member of the symmetrized closure has `|p|` base letters

The block count of item 2 is a statement about a member of the symmetrized
closure, not about the relator, and the reduction of
`GGT/HullSCRelatorSeparation2QuasiGeodesic.lean` turns a count of COMPONENT
letters into the quasi-geodesic clause by subtracting the base letters.  Over
the relator itself that subtraction is free, the base part being an initial
segment; over a rotation of a formal inverse it is not, and the Ledger asserted
in prose that the number is still `|p|`, "because rotation permutes the letters
and formal inversion carries base letters to base letters".

This module proves that, and the arithmetic that goes with it: a range of a
member carries at least `(j - i) - |p|` component letters, which is what the
count has to account for.  Nothing here is geometric and nothing here is
conditional --- it is the half of item 2 that is pure bookkeeping, separated so
that whatever discharges the geometric half does not have to redo it.

The counts are defined by recursion rather than through `List.countP`, because
every fact wanted about them is an induction over the two constructors of
`GGT.RelLetter` and this way each step is an equation rather than a case split
on a `Bool`.
-/

namespace GroupApproximation
namespace HullSC

universe u w

section BaseCount

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The number of base letters of a word.** -/
def baseCount : List (GGT.RelLetter G Λ) → ℕ
  | [] => 0
  | GGT.RelLetter.base _ :: t => baseCount t + 1
  | GGT.RelLetter.comp _ _ :: t => baseCount t

/-- **The number of component letters of a word.** -/
def compCount : List (GGT.RelLetter G Λ) → ℕ
  | [] => 0
  | GGT.RelLetter.base _ :: t => compCount t
  | GGT.RelLetter.comp _ _ :: t => compCount t + 1

omit [Group G] in
/-- **The two counts partition the letters.** -/
theorem baseCount_add_compCount (v : List (GGT.RelLetter G Λ)) :
    baseCount v + compCount v = v.length := by
  induction v with
  | nil => rfl
  | cons a t ih =>
      cases a with
      | base g =>
          show baseCount t + 1 + compCount t = t.length + 1
          omega
      | comp b g =>
          show baseCount t + (compCount t + 1) = t.length + 1
          omega

omit [Group G] in
/-- **The base count is additive.** -/
theorem baseCount_append (v z : List (GGT.RelLetter G Λ)) :
    baseCount (v ++ z) = baseCount v + baseCount z := by
  induction v with
  | nil =>
      show baseCount z = 0 + baseCount z
      omega
  | cons a t ih =>
      cases a with
      | base g =>
          show baseCount (t ++ z) + 1 = baseCount t + 1 + baseCount z
          rw [ih]
          omega
      | comp b g =>
          show baseCount (t ++ z) = baseCount t + baseCount z
          exact ih

omit [Group G] in
/-- **Reversal does not change the base count.** -/
theorem baseCount_reverse (v : List (GGT.RelLetter G Λ)) :
    baseCount v.reverse = baseCount v := by
  induction v with
  | nil => rfl
  | cons a t ih =>
      rw [List.reverse_cons, baseCount_append, ih]
      cases a with
      | base g =>
          show baseCount t + (0 + 1) = baseCount t + 1
          omega
      | comp b g =>
          show baseCount t + 0 = baseCount t
          omega

/-- **Formal inversion of letters does not change the base count.** -/
theorem baseCount_map_inv (v : List (GGT.RelLetter G Λ)) :
    baseCount (v.map RelWord.inv) = baseCount v := by
  induction v with
  | nil => rfl
  | cons a t ih =>
      cases a with
      | base g =>
          show baseCount (t.map RelWord.inv) + 1 = baseCount t + 1
          rw [ih]
      | comp b g =>
          show baseCount (t.map RelWord.inv) = baseCount t
          exact ih

/-- **The formal inverse has the base count of the word.** -/
theorem baseCount_revInv (v : List (GGT.RelLetter G Λ)) :
    baseCount (RelWord.revInv v) = baseCount v := by
  show baseCount (v.map RelWord.inv).reverse = baseCount v
  rw [baseCount_reverse, baseCount_map_inv]

omit [Group G] in
/-- **A rotation has the base count of the word**, the two pieces of the
rotation being the two pieces of the word in the other order. -/
theorem baseCount_rotate (v : List (GGT.RelLetter G Λ)) (n : ℕ) :
    baseCount (v.rotate n) = baseCount v := by
  rcases Nat.eq_zero_or_pos v.length with h0 | hpos
  · have hv : v = [] := List.length_eq_zero_iff.mp h0
    subst hv
    rw [List.rotate_nil]
  · have hmod : n % v.length ≤ v.length := le_of_lt (Nat.mod_lt _ hpos)
    rw [← List.rotate_mod, List.rotate_eq_drop_append_take hmod, baseCount_append,
      Nat.add_comm, ← baseCount_append, List.take_append_drop]

/-- **Every member of the symmetrized closure has the base count of the
relator.** -/
theorem baseCount_of_sym {v z : List (GGT.RelLetter G Λ)} (h : RelWord.Sym v z) :
    baseCount z = baseCount v := by
  induction h with
  | base => rfl
  | rot n _hz ih =>
      rw [baseCount_rotate]
      exact ih
  | inv _hz ih =>
      rw [baseCount_revInv]
      exact ih

end BaseCount

section Relator

variable {G : Type u} [Group G]

/-- **The run has no base letters.** -/
theorem baseCount_blockWord (h₀ h₁ : G) :
    ∀ (s : Bool) (ms : List ℕ), baseCount (blockWord h₀ h₁ s ms) = 0 := by
  intro s ms
  induction ms generalizing s with
  | nil => rfl
  | cons m t ih =>
      show baseCount (blockWord h₀ h₁ (!s) t) = 0
      exact ih (!s)

omit [Group G] in
/-- **The base part has one base letter per letter of `p`.** -/
theorem baseCount_map_base (p : List G) :
    baseCount (p.map (GGT.RelLetter.base : G → GGT.RelLetter G Bool))
      = p.length := by
  induction p with
  | nil => rfl
  | cons g t ih =>
      show baseCount (t.map (GGT.RelLetter.base : G → GGT.RelLetter G Bool)) + 1
        = t.length + 1
      rw [ih]

/-- **The relator has `|p|` base letters.** -/
theorem baseCount_relatorWord₂ (p : List G) (h₀ h₁ : G) (ms : List ℕ) :
    baseCount (relatorWord₂ p h₀ h₁ ms) = p.length := by
  show baseCount (p.map GGT.RelLetter.base ++ blockWord h₀ h₁ false ms)
    = p.length
  rw [baseCount_append, baseCount_map_base, baseCount_blockWord, Nat.add_zero]

/-- **So does every member of its symmetrized closure**, which is what a side of
the quadrilateral is. -/
theorem baseCount_of_sym_relatorWord₂ {p : List G} {h₀ h₁ : G} {ms : List ℕ}
    {z : List (GGT.RelLetter G Bool)}
    (h : RelWord.Sym (relatorWord₂ p h₀ h₁ ms) z) : baseCount z = p.length := by
  rw [baseCount_of_sym h, baseCount_relatorWord₂]

end Relator

section Range

variable {G : Type u} [Group G] {Λ : Type w}

omit [Group G] in
/-- **A range has the base letters it has**, at most those of the whole word:
the word splits as the part before, the range, and the part after. -/
theorem baseCount_range_le (v : List (GGT.RelLetter G Λ)) (i j : ℕ) :
    baseCount ((v.drop i).take j) ≤ baseCount v := by
  have h1 : baseCount (v.take i ++ v.drop i)
      = baseCount (v.take i) + baseCount (v.drop i) := baseCount_append _ _
  rw [List.take_append_drop] at h1
  have h2 : baseCount ((v.drop i).take j ++ (v.drop i).drop j)
      = baseCount ((v.drop i).take j) + baseCount ((v.drop i).drop j) :=
    baseCount_append _ _
  rw [List.take_append_drop] at h2
  omega

omit [Group G] in
/-- **A range inside the word has the length its endpoints say.** -/
theorem length_range (v : List (GGT.RelLetter G Λ)) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ v.length) : ((v.drop i).take (j - i)).length = j - i := by
  rw [List.length_take, List.length_drop]
  omega

end Range

section RangeRelator

variable {G : Type u} [Group G]

/-- **A range of a member of the closure carries at least `(j - i) - |p|`
component letters.**

This is the arithmetic the count is stated against: what a component count of
the range has to reach is `(j - i)` less the base letters, and those are at most
`|p|` wherever the rotation has put them. -/
theorem compCount_range_ge {p : List G} {h₀ h₁ : G} {ms : List ℕ}
    {z : List (GGT.RelLetter G Bool)}
    (h : RelWord.Sym (relatorWord₂ p h₀ h₁ ms) z) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ z.length) :
    j - i ≤ compCount ((z.drop i).take (j - i)) + p.length := by
  have hlen := length_range z hij hj
  have hsum := baseCount_add_compCount ((z.drop i).take (j - i))
  have hle := baseCount_range_le z i (j - i)
  have hb := baseCount_of_sym_relatorWord₂ h
  omega

end RangeRelator

end HullSC
end GroupApproximation
