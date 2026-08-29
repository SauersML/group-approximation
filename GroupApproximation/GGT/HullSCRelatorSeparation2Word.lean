import GroupApproximation.GGT.HullSCRelatorSeparationNotQG

/-!
# Hull's relator, alternating between two hyperbolically embedded subgroups

M. Hull, *Small cancellation in acylindrically hyperbolic groups*, §6: the
relator is `t⁻¹ u` with `u = h₁^{n₁} h₂^{n₂} ⋯` in **independent** loxodromic
elements.  Independence is what puts the letters in different members of the
family `{H_λ}`, and that is what keeps consecutive letters in different
components.

`GGT/HullSCRelatorSeparationNotQG.lean` shows what happens without it: over
`Λ = Unit` the whole run merges into one component spanning a single edge, and
the relator is not quasi-geodesic for any constants.  This module writes down
the faithful shape over `Λ = Bool`.

`blockWord h₀ h₁ s ms` reads the exponents of `ms` alternately as letters of the
two subgroups, starting at index `s`, and `relatorWord₂` puts a base spelling in
front of it.  The alternation is in the definition rather than in a side
condition, so it costs nothing to maintain:

* `blockWord_index_alternates` -- consecutive block letters carry opposite
  indices.  Since `GGT.RelLetter.IsCompOf lam (comp mu h)` is `mu = lam`, no two
  consecutive letters belong to one component, so each block letter is a
  maximal run by itself.  That is the property the whole redesign turns on, and
  it is what makes the per-letter matching of
  `HullSC.exponent_eq_of_blockMatch` reachable.
* `mem_blockWord` -- every block letter is a power of one of the two elements,
  which is what admissibility consumes.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Word

variable {G : Type u} [Group G]

/-- **The alternating run of Hull's relator.**  The exponents are read as
letters of the two subgroups in turn, starting at index `s`. -/
def blockWord (h₀ h₁ : G) : Bool → List ℕ → List (GGT.RelLetter G Bool)
  | _, [] => []
  | s, m :: ms =>
      GGT.RelLetter.comp s ((if s then h₁ else h₀) ^ m)
        :: blockWord h₀ h₁ (!s) ms

theorem blockWord_nil (h₀ h₁ : G) (s : Bool) :
    blockWord h₀ h₁ s [] = [] := by
  simp [blockWord]

theorem blockWord_cons (h₀ h₁ : G) (s : Bool) (m : ℕ) (ms : List ℕ) :
    blockWord h₀ h₁ s (m :: ms)
      = GGT.RelLetter.comp s ((if s then h₁ else h₀) ^ m)
          :: blockWord h₀ h₁ (!s) ms := by
  simp [blockWord]

theorem length_blockWord (h₀ h₁ : G) :
    ∀ (s : Bool) (ms : List ℕ), (blockWord h₀ h₁ s ms).length = ms.length := by
  intro s ms
  induction ms generalizing s with
  | nil => rfl
  | cons m t ih =>
      rw [blockWord_cons, List.length_cons, List.length_cons, ih]

/-- **Hull's relator, faithfully**: a base spelling of `t⁻¹` followed by the
alternating run. -/
def relatorWord₂ (p : List G) (h₀ h₁ : G) (ms : List ℕ) :
    List (GGT.RelLetter G Bool) :=
  p.map GGT.RelLetter.base ++ blockWord h₀ h₁ false ms

theorem length_relatorWord₂ (p : List G) (h₀ h₁ : G) (ms : List ℕ) :
    (relatorWord₂ p h₀ h₁ ms).length = p.length + ms.length := by
  show (p.map GGT.RelLetter.base ++ blockWord h₀ h₁ false ms).length
    = p.length + ms.length
  rw [List.length_append, List.length_map, length_blockWord]

/-- **Every block letter is a power of one of the two elements.** -/
theorem mem_blockWord (h₀ h₁ : G) :
    ∀ (s : Bool) (ms : List ℕ) (x : GGT.RelLetter G Bool),
      x ∈ blockWord h₀ h₁ s ms →
        ∃ (b : Bool) (m : ℕ), m ∈ ms ∧
          x = GGT.RelLetter.comp b ((if b then h₁ else h₀) ^ m) := by
  intro s ms
  induction ms generalizing s with
  | nil =>
      intro x hx
      rw [blockWord_nil] at hx
      simp at hx
  | cons m t ih =>
      intro x hx
      rw [blockWord_cons] at hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨s, m, List.mem_cons.mpr (Or.inl rfl), rfl⟩
      · obtain ⟨b, m', hm', hx'eq⟩ := ih (!s) x hx'
        exact ⟨b, m', List.mem_cons.mpr (Or.inr hm'), hx'eq⟩

/-- **Consecutive block letters carry opposite indices.**

`GGT.RelLetter.IsCompOf lam (comp mu h)` is `mu = lam`, so this says no two
consecutive letters of the run belong to one component: every block letter is a
maximal run by itself.  Over `Λ = Unit` the corresponding statement is false,
and that failure is what
`HullSC.not_quasiGeodesic_relatorWord` turns into a refutation. -/
theorem blockWord_index_alternates (h₀ h₁ : G) :
    ∀ (s : Bool) (ms : List ℕ) (i : ℕ) (b b' : Bool) (x x' : G),
      (blockWord h₀ h₁ s ms)[i]? = some (GGT.RelLetter.comp b x) →
        (blockWord h₀ h₁ s ms)[i + 1]? = some (GGT.RelLetter.comp b' x') →
          b' = !b := by
  intro s ms
  induction ms generalizing s with
  | nil =>
      intro i b b' x x' hi _
      rw [blockWord_nil] at hi
      simp at hi
  | cons m t ih =>
      intro i b b' x x' hi hi'
      rw [blockWord_cons] at hi hi'
      cases i with
      | zero =>
          rw [List.getElem?_cons_zero] at hi
          rw [List.getElem?_cons_succ] at hi'
          have hb : s = b := by
            have heq := Option.some.inj hi
            rw [GGT.RelLetter.comp.injEq] at heq
            exact heq.1
          cases t with
          | nil =>
              rw [blockWord_nil] at hi'
              simp at hi'
          | cons m' t' =>
              rw [blockWord_cons, List.getElem?_cons_zero] at hi'
              have heq' := Option.some.inj hi'
              rw [GGT.RelLetter.comp.injEq] at heq'
              rw [← hb, ← heq'.1]
      | succ i' =>
          rw [List.getElem?_cons_succ] at hi
          rw [List.getElem?_cons_succ] at hi'
          exact ih (!s) i' b b' x x' hi hi'

end Word

end HullSC
end GroupApproximation
