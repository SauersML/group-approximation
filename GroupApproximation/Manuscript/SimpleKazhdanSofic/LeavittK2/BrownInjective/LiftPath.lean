import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.Triangle
import GroupApproximation.Meta.AxiomGuard

/-!
# Brown presentation II: lifting edge paths (lane sk-leavitt-12)

Khanh, tex l.460: "Starting at a vertex represented by a transporter $g$, it is encoded by a
word $jT$ [...]. At the endpoint, the difference from a prescribed transporter is again in $J$."

`LiftEnd x l z`: the edge path `l` (list of successive vertices) is lifted step by step from
the transporter `x`, ending at the transporter `z`.  Lifts exist along edge paths, their
endpoints are unique up to right `J`-cosets, and they split and concatenate along `++`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective

universe u v

variable {G : Type u} {V : Type v} [Group G] [MulAction G V]

namespace BrownSetting

variable (S : BrownSetting G V)

/-- A step-by-step lift of an edge path, from the transporter `x` to the transporter `z`. -/
inductive LiftEnd : S.PiGroup → List V → S.PiGroup → Prop
  | nil (x : S.PiGroup) : LiftEnd x [] x
  | cons {x y z : S.PiGroup} {w : V} {l : List V} :
      S.Step x y → S.p y • S.v0 = w → LiftEnd y l z → LiftEnd x (w :: l) z

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.LiftEnd

theorem LiftEnd.target {x z : S.PiGroup} {l : List V} (h : S.LiftEnd x l z) :
    S.p z • S.v0 = S.endpoint (S.p x • S.v0) l := by
  induction h with
  | nil _ => simp only [endpoint]
  | @cons _ _ _ _ _ _ hw _ ih =>
    simp only [endpoint]
    rw [ih, hw]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.LiftEnd.target

theorem LiftEnd.isPath {x z : S.PiGroup} {l : List V} (h : S.LiftEnd x l z) :
    S.IsPath (S.p x • S.v0) l := by
  induction h with
  | nil _ => simp only [IsPath]
  | @cons _ _ _ _ _ hs hw _ ih =>
    subst hw
    simp only [IsPath]
    exact ⟨S.step_edge hs, ih⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.LiftEnd.isPath

/-- Lift endpoints are unique up to right `J`-cosets. -/
theorem LiftEnd.unique {x z : S.PiGroup} {l : List V} (h : S.LiftEnd x l z) :
    ∀ {x' z' : S.PiGroup}, S.LiftEnd x' l z' → S.SameCoset x x' → S.SameCoset z z' := by
  induction h with
  | nil _ =>
    intro _ _ h' hx
    cases h'
    exact hx
  | @cons _ _ _ _ _ hs hw _ ih =>
    intro _ _ h' hx
    cases h' with
    | cons hs' hw' hl' => exact ih hl' (S.step_unique hs hs' hx (by rw [hw, hw']))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.LiftEnd.unique

theorem LiftEnd.exists_of_isPath (l : List V) :
    ∀ x : S.PiGroup, S.IsPath (S.p x • S.v0) l → ∃ z, S.LiftEnd x l z := by
  induction l with
  | nil => exact fun x _ => ⟨x, LiftEnd.nil x⟩
  | cons w _ ih =>
    intro x hp
    simp only [IsPath] at hp
    obtain ⟨y, hs, hy⟩ := S.step_exists x w hp.1
    obtain ⟨z, hz⟩ := ih y (by rw [hy]; exact hp.2)
    exact ⟨z, LiftEnd.cons hs hy hz⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.LiftEnd.exists_of_isPath

theorem LiftEnd.append {x y : S.PiGroup} {l₁ : List V} (h1 : S.LiftEnd x l₁ y) :
    ∀ {z : S.PiGroup} {l₂ : List V}, S.LiftEnd y l₂ z → S.LiftEnd x (l₁ ++ l₂) z := by
  induction h1 with
  | nil _ =>
    intro _ _ h2
    rw [List.nil_append]
    exact h2
  | @cons _ _ _ _ _ hs hw _ ih =>
    intro _ _ h2
    rw [List.cons_append]
    exact LiftEnd.cons hs hw (ih h2)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.LiftEnd.append

theorem LiftEnd.split (l₁ : List V) :
    ∀ {x z : S.PiGroup} {l₂ : List V}, S.LiftEnd x (l₁ ++ l₂) z →
      ∃ y, S.LiftEnd x l₁ y ∧ S.LiftEnd y l₂ z := by
  induction l₁ with
  | nil =>
    intro x _ _ h
    rw [List.nil_append] at h
    exact ⟨x, LiftEnd.nil x, h⟩
  | cons _ _ ih =>
    intro _ _ _ h
    rw [List.cons_append] at h
    cases h with
    | cons hs hw hl =>
      obtain ⟨y', h1, h2⟩ := ih hl
      exact ⟨y', LiftEnd.cons hs hw h1, h2⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.LiftEnd.split

end BrownSetting

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective
