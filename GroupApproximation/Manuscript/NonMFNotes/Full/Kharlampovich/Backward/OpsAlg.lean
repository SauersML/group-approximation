import Mathlib.Tactic.Abel
import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Backward.Ops

/-!
# Linear algebra of the local operators

Input for the "if" direction of KMS Theorem `tmm`(b) (`l789` of
Kharlampovich--Myasnikov--Sapir, arXiv:1204.6506, Sec. 4.1), used in
`thm:fixed-radical-membership` of `non_mf_group_notes.tex`.

All operators are additive (`opL_add`).  The operator of `A_i` is `φ ↦ φ + P φ`
(`opB_eq`), where `P φ` is `φ ∘ β` on active classes and `0` elsewhere.  Since `β`
moves active classes to inactive ones, `P ∘ P = 0` (`opP_opP`), and `P` ignores any
operator that is the identity on inactive classes (`opP_opL`).  A table differing from
another by the identity gives an operator differing by the identity on functions
vanishing on inactive classes (`opL_eq_add`).  Letters of different blocks commute
(`opB_comm`, `opB_opL_comm`).
-/

namespace GroupApproximation.Full.Kharlampovich

namespace KMS

namespace Backward

variable {K : ℕ}

section Local

variable {C : Type*} (n : Fin K) (act : C → Prop) [DecidablePred act] (σ : C → C)

theorem opL_add (T : Tab) (φ ψ : Fn K C) :
    opL n act σ T (φ + ψ) = opL n act σ T φ + opL n act σ T ψ := by
  funext v c
  by_cases hc : act c
  · simp only [opL, hc, ↓reduceIte, Pi.add_apply, Tab.app]
    ring
  · simp only [opL, hc, ↓reduceIte, Pi.add_apply]

/-- A table differing from `T` by the identity gives an operator differing from that
of `T` by the identity, on functions vanishing on inactive classes. -/
theorem opL_eq_add (T T' : Tab) (hT : ∀ t g y, T'.app t g y = T.app t g y + g t)
    (ψ : Fn K C) (hψ : ∀ v c, ¬ act c → ψ v c = 0) :
    opL n act σ T' ψ = opL n act σ T ψ + ψ := by
  funext v c
  by_cases hc : act c
  · simp only [opL, hc, ↓reduceIte, Pi.add_apply]
    rw [hT, Function.update_eq_self]
  · simp only [opL, hc, ↓reduceIte, Pi.add_apply]
    rw [hψ v c hc, add_zero]

end Local

section Big

variable {C : Type*} (act : C → Prop) [DecidablePred act] (β : C → C)

/-- The shift part `P` of the operator of `A_i` (KMS `l789`). -/
def opP (φ : Fn K C) : Fn K C := fun v c ↦ if act c then φ v (β c) else 0

theorem opP_of_not (φ : Fn K C) (v : Fin K → Tri) {c : C} (hc : ¬ act c) :
    opP act β φ v c = 0 := by
  simp only [opP, hc, ↓reduceIte]

theorem opB_eq (φ : Fn K C) : opB act β φ = φ + opP act β φ := by
  funext v c
  by_cases hc : act c
  · simp only [opB, opP, hc, ↓reduceIte, Pi.add_apply]
  · simp only [opB, opP, hc, ↓reduceIte, Pi.add_apply, add_zero]

theorem opP_add (φ ψ : Fn K C) : opP act β (φ + ψ) = opP act β φ + opP act β ψ := by
  funext v c
  by_cases hc : act c
  · simp only [opP, hc, ↓reduceIte, Pi.add_apply]
  · simp only [opP, hc, ↓reduceIte, Pi.add_apply, add_zero]

theorem opP_opP (hβ : ∀ c, act c → ¬ act (β c)) (φ : Fn K C) :
    opP act β (opP act β φ) = 0 := by
  funext v c
  by_cases hc : act c
  · have hc' : ¬ act (β c) := hβ c hc
    simp only [opP, hc, hc', ↓reduceIte, Pi.zero_apply]
  · simp only [opP, hc, ↓reduceIte, Pi.zero_apply]

/-- `P` ignores a local operator whose activity fails at the shifted classes. -/
theorem opP_opL {act' : C → Prop} [DecidablePred act'] {m : Fin K} {σ' : C → C} {T : Tab}
    (hβ : ∀ c, act c → ¬ act' (β c)) (φ : Fn K C) :
    opP act β (opL m act' σ' T φ) = opP act β φ := by
  funext v c
  by_cases hc : act c
  · have hc' : ¬ act' (β c) := hβ c hc
    simp only [opP, opL, hc, hc', ↓reduceIte]
  · simp only [opP, hc, ↓reduceIte]

/-- Operators of two letters `A_i`, `A_j` commute. -/
theorem opB_comm {act' : C → Prop} [DecidablePred act'] {β' : C → C}
    (h1 : ∀ c, act' (β c) ↔ act' c) (h2 : ∀ c, act (β' c) ↔ act c)
    (hβ : ∀ c, act c → act' c → β (β' c) = β' (β c)) (φ : Fn K C) :
    opB act β (opB act' β' φ) = opB act' β' (opB act β φ) := by
  funext v c
  by_cases hc : act c
  · by_cases hc' : act' c
    · have e1 : act' (β c) := (h1 c).2 hc'
      have e2 : act (β' c) := (h2 c).2 hc
      simp only [opB, hc, hc', e1, e2, ↓reduceIte, hβ c hc hc']
      ring
    · have e1 : ¬ act' (β c) := fun h ↦ hc' ((h1 c).1 h)
      simp only [opB, hc, hc', e1, ↓reduceIte]
  · by_cases hc' : act' c
    · have e2 : ¬ act (β' c) := fun h ↦ hc ((h2 c).1 h)
      simp only [opB, hc, hc', e2, ↓reduceIte]
    · simp only [opB, hc, hc', ↓reduceIte]

/-- The operator of `A_i` commutes with a small letter of another block. -/
theorem opB_opL_comm (n : Fin K) {act' : C → Prop} [DecidablePred act'] {σ : C → C}
    (T : Tab) (h1 : ∀ c, act' (β c) ↔ act' c) (h2 : ∀ c, act (σ c) ↔ act c)
    (hσ : ∀ c, act c → act' c → β (σ c) = σ (β c)) (φ : Fn K C) :
    opB act β (opL n act' σ T φ) = opL n act' σ T (opB act β φ) := by
  funext v c
  by_cases hc : act c
  · by_cases hc' : act' c
    · have e1 : act' (β c) := (h1 c).2 hc'
      have e2 : act (σ c) := (h2 c).2 hc
      simp only [opB, opL, hc, hc', e1, e2, ↓reduceIte, hσ c hc hc', Tab.app]
      ring
    · have e1 : ¬ act' (β c) := fun h ↦ hc' ((h1 c).1 h)
      simp only [opB, opL, hc, hc', e1, ↓reduceIte]
  · by_cases hc' : act' c
    · have e2 : ¬ act (σ c) := fun h ↦ hc ((h2 c).1 h)
      simp only [opB, opL, hc, hc', e2, ↓reduceIte]
    · simp only [opB, opL, hc, hc', ↓reduceIte]

end Big

end Backward

end KMS

end GroupApproximation.Full.Kharlampovich
