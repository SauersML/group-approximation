import GroupApproximation.GGT.HullEeCycle

/-!
# Closing a word changes no component

`GGT/HullEeCycle.lean` closes a word with one base letter.  This module proves
that the closure is invisible to the component structure, in both directions, and
carries isolation across.

That is the promise the base letter was chosen for.  A component is a *maximal*
run of letters of one index, and maximality is the clause that a naive closure
would break: a component of the open word that runs all the way to the end has
its maximality witnessed vacuously, there being no letter after it, and appending
a letter puts one there.  If that letter were peripheral of the same index the
run would extend and the component would change; because it is a **base** letter,
`IsCompOf` is `False` at it and the maximality clause is witnessed rather than
violated.

So the appended position is the only place either direction can go wrong, and it
is exactly where the base letter does its work:

* going **out**, the fifth clause of `IsComp` splits on whether the run ends
  before the join or at it, and at the join the new letter supplies the witness;
* coming **back**, a component of the cycle cannot reach past the join --- its
  third clause would demand that the base letter be a component letter --- so
  `k ≤ |u|` and every clause restricts.

## Isolation crosses because vertices do

`IsIsolated` is `IsCompStart` plus a statement about `Connected`, and `Connected`
compares vertices.  `vertex_cycleWord` says the cycle traces the original path
below the join, and both indices in play are component starts, hence strictly
below it.  So the two `Connected` statements are the same statement, and
isolation on the open word is isolation on the polygon.

With this, `isIsolated_transfer_of_minimal` reaches the polygon the estimate
consumes, and the isolation half of Hull's Lemma `ee` is finished.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

section CycleComponents

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## 1.  The appended letter is not a component letter -/

omit [Group G] in
/-- **The letter at the join is the base letter it was built from**, and a base
letter is a component of no index.  Every case below reduces to this. -/
theorem not_isCompOf_getElem_cycleWord_length {lam : Λ}
    (u : List (RelLetter G Λ)) (x : G)
    (hh : u.length < (cycleWord u x).length) :
    ¬ ((cycleWord u x)[u.length]'hh).IsCompOf lam := by
  have heq : (cycleWord u x)[u.length]'hh = RelLetter.base x := by
    show (u ++ [RelLetter.base x])[u.length]'hh = RelLetter.base x
    rw [List.getElem_append_right (le_refl u.length)]
    simp
  rw [heq]
  exact id

omit [Group G] in
/-- **Below the join the cycle reads the original word.** -/
theorem getElem_cycleWord_of_lt (u : List (RelLetter G Λ)) (x : G) {m : ℕ}
    (hm : m < u.length) (hm' : m < (cycleWord u x).length) :
    (cycleWord u x)[m]'hm' = u[m]'hm := by
  show (u ++ [RelLetter.base x])[m]'hm' = u[m]'hm
  rw [List.getElem_append_left hm]

/-! ## 2.  Components survive the closure -/

omit [Group G] in
/-- **A component of the open word is a component of the cycle.**  The only new
obligation is the fifth clause at the join, where the base letter is the
witness. -/
theorem isComp_cycleWord {lam : Λ} {u : List (RelLetter G Λ)} {i k : ℕ} (x : G)
    (h : IsComp lam u i k) : IsComp lam (cycleWord u x) i k := by
  obtain ⟨hik, hkl, hall, hpre, hpost⟩ := h
  have hlen : (cycleWord u x).length = u.length + 1 := length_cycleWord u x
  refine ⟨hik, by omega, ?_, ?_, ?_⟩
  · intro m him hmk hm'
    have hm : m < u.length := by omega
    rw [getElem_cycleWord_of_lt u x hm hm']
    exact hall m him hmk hm
  · intro m him hm'
    have hm : m < u.length := by omega
    rw [getElem_cycleWord_of_lt u x hm hm']
    exact hpre m him hm
  · intro hk'
    rcases lt_or_eq_of_le hkl with hlt | heq
    · rw [getElem_cycleWord_of_lt u x hlt hk']
      exact hpost hlt
    · subst heq
      exact not_isCompOf_getElem_cycleWord_length u x hk'

omit [Group G] in
/-- **A component of the cycle is a component of the open word.**  It cannot
reach past the join: its third clause would ask the base letter to be a component
letter. -/
theorem isComp_of_isComp_cycleWord {lam : Λ} {u : List (RelLetter G Λ)} {x : G}
    {j k : ℕ} (h : IsComp lam (cycleWord u x) j k) : IsComp lam u j k := by
  obtain ⟨hjk, hkl, hall, hpre, hpost⟩ := h
  have hlen : (cycleWord u x).length = u.length + 1 := length_cycleWord u x
  have hku : k ≤ u.length := by
    by_contra hcon
    have hh : u.length < (cycleWord u x).length := by omega
    exact not_isCompOf_getElem_cycleWord_length u x hh
      (hall u.length (by omega) (by omega) hh)
  refine ⟨hjk, hku, ?_, ?_, ?_⟩
  · intro m hjm hmk hm
    have hm' : m < (cycleWord u x).length := by omega
    have hc := hall m hjm hmk hm'
    rwa [getElem_cycleWord_of_lt u x hm hm'] at hc
  · intro m hjm hm
    have hm' : m < (cycleWord u x).length := by omega
    have hc := hpre m hjm hm'
    rwa [getElem_cycleWord_of_lt u x hm hm'] at hc
  · intro hk
    have hk' : k < (cycleWord u x).length := by omega
    have hc := hpost hk'
    rwa [getElem_cycleWord_of_lt u x hk hk'] at hc

omit [Group G] in
/-- The component-start form, outwards. -/
theorem isCompStart_cycleWord {lam : Λ} {u : List (RelLetter G Λ)} {i : ℕ}
    (x : G) (h : IsCompStart lam u i) :
    IsCompStart lam (cycleWord u x) i := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, isComp_cycleWord x hk⟩

omit [Group G] in
/-- The component-start form, back. -/
theorem isCompStart_of_isCompStart_cycleWord {lam : Λ}
    {u : List (RelLetter G Λ)} {x : G} {j : ℕ}
    (h : IsCompStart lam (cycleWord u x) j) : IsCompStart lam u j := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, isComp_of_isComp_cycleWord hk⟩

/-! ## 3.  Isolation crosses -/

/-- **An isolated component of the open word is isolated in the cycle.**

Both indices are component starts, so both lie strictly below the join, so
`vertex_cycleWord` makes the two `Connected` statements the same statement.  The
converse transfer of §2 is what turns a competitor in the cycle back into a
competitor in the open word, which is the only place it is needed. -/
theorem isIsolated_cycleWord {H : Λ → Subgroup G} {lam : Λ} {v : G}
    {u : List (RelLetter G Λ)} (x : G) {i : ℕ}
    (h : IsIsolated H lam v u i) : IsIsolated H lam v (cycleWord u x) i := by
  obtain ⟨hstart, hiso⟩ := h
  refine ⟨isCompStart_cycleWord x hstart, ?_⟩
  intro j hji hj hconn
  have hju0 : IsCompStart lam u j := isCompStart_of_isCompStart_cycleWord hj
  obtain ⟨hiu, -⟩ := isCompOf_getElem_of_isCompStart hstart
  obtain ⟨hju, -⟩ := isCompOf_getElem_of_isCompStart hju0
  have hc : Connected H lam v u i j := by
    show (vertex v u i)⁻¹ * vertex v u j ∈ H lam
    rw [← vertex_cycleWord u x v (le_of_lt hiu),
      ← vertex_cycleWord u x v (le_of_lt hju)]
    exact hconn
  exact hiso j hji hju0 hc

end CycleComponents

end OsinComponents
end GGT
end GroupApproximation
