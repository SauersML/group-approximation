import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.MatuiFullGroup
import GroupApproximation.GroupTheory.HydeLodha.HigmanEpstein
import GroupApproximation.Meta.AxiomGuard

namespace GroupApproximation
namespace Full
namespace StepanovMatui
namespace Matui

/-!
# Three-cycles over disjoint unions

`simple_kazhdan_sofic_group.tex`, remark at tex l.307–309:

> For derived topological full groups, Matui showed by a similar argument that a nontrivial normal
> subgroup meets a simple union of products of alternating groups on towers
> [Matui, Lemma 3.4 and Theorem 4.9].

Part of work order WO-A2.  A three-cycle `threeCycle f U` splits along any partition of `U` into
two pieces (`threeCycle_union`): the swaps split as products (`swapAlong_union`), the pieces have
disjoint towers `A ∪ f A ∪ f² A` (`disjoint_tower`), and the commutator of two products of commuting
factors is the product of the commutators (`commutatorElement_mul_mul_of_commute`).
-/

open scoped commutatorElement

section GroupIdentity

variable {M : Type*} [Group M]

/-- `⁅a b, c d⁆ = ⁅a, c⁆ ⁅b, d⁆` when `b` and `d` commute with `a` and `c`. -/
theorem commutatorElement_mul_mul_of_commute {a b c d : M} (hba : Commute b a)
    (hbc : Commute b c) (hda : Commute d a) (hdc : Commute d c) :
    ⁅a * b, c * d⁆ = ⁅a, c⁆ * ⁅b, d⁆ := by
  simp only [commutatorElement_def]
  have hQ : Commute (b * d * b⁻¹) a⁻¹ :=
    ((hba.mul_left hda).mul_left hba.inv_left).inv_right
  have hP : Commute (b * d * b⁻¹ * d⁻¹) c⁻¹ :=
    (((hbc.mul_left hdc).mul_left hbc.inv_left).mul_left hdc.inv_left).inv_right
  calc a * b * (c * d) * (a * b)⁻¹ * (c * d)⁻¹
        = a * (b * c) * d * b⁻¹ * a⁻¹ * d⁻¹ * c⁻¹ := by group
    _ = a * (c * b) * d * b⁻¹ * a⁻¹ * d⁻¹ * c⁻¹ := by rw [hbc.eq]
    _ = a * c * (b * d * b⁻¹ * a⁻¹) * d⁻¹ * c⁻¹ := by group
    _ = a * c * (a⁻¹ * (b * d * b⁻¹)) * d⁻¹ * c⁻¹ := by rw [hQ.eq]
    _ = a * c * a⁻¹ * (b * d * b⁻¹ * d⁻¹ * c⁻¹) := by group
    _ = a * c * a⁻¹ * (c⁻¹ * (b * d * b⁻¹ * d⁻¹)) := by rw [hP.eq]
    _ = a * c * a⁻¹ * c⁻¹ * (b * d * b⁻¹ * d⁻¹) := by group

end GroupIdentity

variable {X : Type*}

/-- The swap along `g` is supported in `A ∪ g A`. -/
theorem supportedIn_swapAlong (g : Equiv.Perm X) (A : Set X) :
    HydeLodha.SupportedIn (swapAlong g A) {y | y ∈ A ∨ g⁻¹ y ∈ A} := by
  intro x hx
  have h1 : x ∉ A := fun h => hx (Or.inl h)
  have h2 : g⁻¹ x ∉ A := fun h => hx (Or.inr h)
  by_cases hA : ∀ y ∈ A, g y ∉ A
  · rw [swapAlong_apply hA, swapFun_of_not_mem h1 h2]
  · rw [swapAlong_of_not hA, Equiv.Perm.one_apply]

/-- The swap along `g` on a disjoint union is the product of the swaps on the pieces. -/
theorem swapAlong_union {g : Equiv.Perm X} {A B : Set X} (hAB : Disjoint A B)
    (hg : ∀ x ∈ A ∪ B, g x ∉ A ∪ B) : swapAlong g (A ∪ B) = swapAlong g A * swapAlong g B := by
  have hA : ∀ x ∈ A, g x ∉ A := fun x hx h => hg x (Or.inl hx) (Or.inl h)
  have hB : ∀ x ∈ B, g x ∉ B := fun x hx h => hg x (Or.inr hx) (Or.inr h)
  refine Equiv.ext fun x => ?_
  rw [Equiv.Perm.mul_apply, swapAlong_apply hg, swapAlong_apply hA, swapAlong_apply hB]
  by_cases hxB : x ∈ B
  · have hxU : x ∈ A ∪ B := Or.inr hxB
    have hgx : g x ∉ A := fun h => hg x hxU (Or.inl h)
    have hgi : g⁻¹ (g x) ∉ A := by
      rw [perm_inv_apply_self]
      exact Set.disjoint_right.mp hAB hxB
    rw [swapFun_of_mem hxB, swapFun_of_not_mem hgx hgi, swapFun_of_mem hxU]
  by_cases hxA : x ∈ A
  · have hxU : x ∈ A ∪ B := Or.inl hxA
    have hiB : g⁻¹ x ∉ B := fun h =>
      hg (g⁻¹ x) (Or.inr h) (by rw [perm_apply_inv_self]; exact hxU)
    rw [swapFun_of_not_mem hxB hiB, swapFun_of_mem hxA, swapFun_of_mem hxU]
  have hxU : x ∉ A ∪ B := by
    rintro (h | h)
    exacts [hxA h, hxB h]
  by_cases hiB : g⁻¹ x ∈ B
  · have hiU : g⁻¹ x ∈ A ∪ B := Or.inr hiB
    have hiA : g⁻¹ x ∉ A := Set.disjoint_right.mp hAB hiB
    have hiiA : g⁻¹ (g⁻¹ x) ∉ A := fun h =>
      hg (g⁻¹ (g⁻¹ x)) (Or.inl h) (by rw [perm_apply_inv_self]; exact hiU)
    rw [swapFun_of_inv_mem hxB hiB, swapFun_of_not_mem hiA hiiA, swapFun_of_inv_mem hxU hiU]
  by_cases hiA : g⁻¹ x ∈ A
  · have hiU : g⁻¹ x ∈ A ∪ B := Or.inl hiA
    rw [swapFun_of_not_mem hxB hiB, swapFun_of_inv_mem hxA hiA, swapFun_of_inv_mem hxU hiU]
  have hiU : g⁻¹ x ∉ A ∪ B := by
    rintro (h | h)
    exacts [hiA h, hiB h]
  rw [swapFun_of_not_mem hxB hiB, swapFun_of_not_mem hxA hiA, swapFun_of_not_mem hxU hiU]

/-- The swap along `f` is supported in the tower `A ∪ f A ∪ f² A`. -/
theorem supportedIn_swapAlong_tower (f : Equiv.Perm X) (A : Set X) :
    HydeLodha.SupportedIn (swapAlong f A) {y | y ∈ A ∨ f⁻¹ y ∈ A ∨ (f * f)⁻¹ y ∈ A} :=
  (supportedIn_swapAlong f A).mono fun y hy => by
    rcases hy with hy | hy
    exacts [Or.inl hy, Or.inr (Or.inl hy)]

/-- The swap along `f²` is supported in the tower `A ∪ f A ∪ f² A`. -/
theorem supportedIn_swapAlong_sq_tower (f : Equiv.Perm X) (A : Set X) :
    HydeLodha.SupportedIn (swapAlong (f * f) A) {y | y ∈ A ∨ f⁻¹ y ∈ A ∨ (f * f)⁻¹ y ∈ A} :=
  (supportedIn_swapAlong (f * f) A).mono fun y hy => by
    rcases hy with hy | hy
    exacts [Or.inl hy, Or.inr (Or.inr hy)]

theorem perm_mul_self_inv_apply (f : Equiv.Perm X) (y : X) : (f * f)⁻¹ y = f⁻¹ (f⁻¹ y) := by
  rw [mul_inv_rev, Equiv.Perm.mul_apply]

/-- Disjoint pieces of a three-cycle datum have disjoint towers. -/
theorem disjoint_tower {f : Equiv.Perm X} {U A B : Set X} (h : IsThreeCycleDatum f U)
    (hAU : A ⊆ U) (hBU : B ⊆ U) (hAB : Disjoint A B) :
    Disjoint {y | y ∈ A ∨ f⁻¹ y ∈ A ∨ (f * f)⁻¹ y ∈ A}
      {y | y ∈ B ∨ f⁻¹ y ∈ B ∨ (f * f)⁻¹ y ∈ B} := by
  refine Set.disjoint_left.mpr fun y hyA hyB => ?_
  rcases hyA with hy | hy | hy <;> rcases hyB with hz | hz | hz
  · exact Set.disjoint_left.mp hAB hy hz
  · exact h.1 _ (hBU hz) (by rw [perm_apply_inv_self]; exact hAU hy)
  · rw [perm_mul_self_inv_apply] at hz
    exact h.2 _ (hBU hz) (by rw [perm_apply_inv_self, perm_apply_inv_self]; exact hAU hy)
  · exact h.1 _ (hAU hy) (by rw [perm_apply_inv_self]; exact hBU hz)
  · exact Set.disjoint_left.mp hAB hy hz
  · rw [perm_mul_self_inv_apply] at hz
    exact h.1 _ (hBU hz) (by rw [perm_apply_inv_self]; exact hAU hy)
  · rw [perm_mul_self_inv_apply] at hy
    exact h.2 _ (hAU hy) (by rw [perm_apply_inv_self, perm_apply_inv_self]; exact hBU hz)
  · rw [perm_mul_self_inv_apply] at hy
    exact h.1 _ (hAU hy) (by rw [perm_apply_inv_self]; exact hBU hz)
  · exact Set.disjoint_left.mp hAB hy hz

/-- **A three-cycle splits over a partition** of its base into two pieces. -/
theorem threeCycle_union {f : Equiv.Perm X} {U A B : Set X} (h : IsThreeCycleDatum f U)
    (hAU : A ⊆ U) (hBU : B ⊆ U) (hAB : Disjoint A B) :
    threeCycle f (A ∪ B) = threeCycle f A * threeCycle f B := by
  have hABU : A ∪ B ⊆ U := Set.union_subset hAU hBU
  have hg1 : ∀ x ∈ A ∪ B, f x ∉ A ∪ B := fun x hx hfx => h.1 x (hABU hx) (hABU hfx)
  have hg2 : ∀ x ∈ A ∪ B, (f * f) x ∉ A ∪ B := fun x hx hfx => h.2 x (hABU hx) (hABU hfx)
  have hdisj := disjoint_tower h hAU hBU hAB
  have hba : Commute (swapAlong f B) (swapAlong f A) :=
    HydeLodha.commute_of_supportedIn (supportedIn_swapAlong_tower f B)
      (supportedIn_swapAlong_tower f A) hdisj.symm
  have hbc : Commute (swapAlong f B) (swapAlong (f * f) A) :=
    HydeLodha.commute_of_supportedIn (supportedIn_swapAlong_tower f B)
      (supportedIn_swapAlong_sq_tower f A) hdisj.symm
  have hda : Commute (swapAlong (f * f) B) (swapAlong f A) :=
    HydeLodha.commute_of_supportedIn (supportedIn_swapAlong_sq_tower f B)
      (supportedIn_swapAlong_tower f A) hdisj.symm
  have hdc : Commute (swapAlong (f * f) B) (swapAlong (f * f) A) :=
    HydeLodha.commute_of_supportedIn (supportedIn_swapAlong_sq_tower f B)
      (supportedIn_swapAlong_sq_tower f A) hdisj.symm
  show ⁅swapAlong f (A ∪ B), swapAlong (f * f) (A ∪ B)⁆ =
    ⁅swapAlong f A, swapAlong (f * f) A⁆ * ⁅swapAlong f B, swapAlong (f * f) B⁆
  rw [swapAlong_union hAB hg1, swapAlong_union hAB hg2]
  exact commutatorElement_mul_mul_of_commute hba hbc hda hdc

/-- The three-cycle on the empty set is trivial. -/
theorem threeCycle_empty (f : Equiv.Perm X) : threeCycle f ∅ = 1 := by
  have hs : ∀ g : Equiv.Perm X, swapAlong g ∅ = 1 := fun g => by
    have hg : ∀ x ∈ (∅ : Set X), g x ∉ (∅ : Set X) := fun y hy => absurd hy (Set.notMem_empty y)
    refine Equiv.ext fun x => ?_
    rw [swapAlong_apply hg, swapFun_of_not_mem (Set.notMem_empty x)
      (Set.notMem_empty (g⁻¹ x)), Equiv.Perm.one_apply]
  show ⁅swapAlong f ∅, swapAlong (f * f) ∅⁆ = 1
  rw [hs, hs, commutatorElement_one_left]

end Matui
end StepanovMatui
end Full
end GroupApproximation

#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.commutatorElement_mul_mul_of_commute
#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.swapAlong_union
#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.threeCycle_union
#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.threeCycle_empty
