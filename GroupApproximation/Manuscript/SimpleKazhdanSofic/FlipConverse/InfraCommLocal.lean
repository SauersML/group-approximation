import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RigidCentralizer
import GroupApproximation.Meta.AxiomGuard

/-!
# Infrastructure: commutator localisation (lane `sk-flip-02`)

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds"; the row is
absent from the current tex, so there is no line number).  Infrastructure for the lane
`sk-flip-07` witness `⁅⁅⁅a, f⁆, b⁆, ⁅⁅c, k⁆, d⁆⁆ ≠ 1`.

Truth check (on paper).  With Mathlib's convention `⁅x, y⁆ = x * y * x⁻¹ * y⁻¹` and
`(x * y) z = x (y z)` for homeomorphisms:

* `⁅a, g⁆ = a * c` with `c = g * a⁻¹ * g⁻¹`.
* If `a` is supported in `W`, then `a⁻¹` is supported in `W` and `c` is supported in `g '' W`
  (`supportedIn_conj_iff` and `W ⊆ g ⁻¹' (g '' W)`).  So `⁅a, g⁆` is supported in `W ∪ g '' W`.
* If moreover `W` and `g '' W` are disjoint and `b` is supported in `W`, then `c` is supported in
  `Wᶜ`, so `b * c = c * b` (`SupportedIn.commute_of_compl`), and then
  `⁅a * c, b⁆ = a c b c⁻¹ a⁻¹ b⁻¹ = a b c c⁻¹ a⁻¹ b⁻¹ = ⁅a, b⁆`.

All three lane targets are true as printed; no hypothesis is missing.

Declarations:
* `SupportedIn.mul_union`, `SupportedIn.inv_supportedIn`: support calculus.
* `supportedIn_conj_image`: `SupportedIn a W → SupportedIn (g * a * g⁻¹) (g '' W)`.
* `supportedIn_commutator`: `SupportedIn a W → SupportedIn ⁅a, g⁆ (W ∪ g '' W)`.
* `commutatorElement_mul_eq_of_commute`: pure group algebra, `b c = c b → ⁅a c, b⁆ = ⁅a, b⁆`.
* `commutator_commutator_eq_of_displaced`: the lane endpoint `⁅⁅a, g⁆, b⁆ = ⁅a, b⁆`.
* `commutator_commutator_eq_of_displaced_subgroup`: the same identity inside any subgroup of
  `X ≃ₜ X` (e.g. `topologicalFullGroup T`), which is the form used by lane `sk-flip-07`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open scoped commutatorElement

section CommLocal

variable {X : Type*} [TopologicalSpace X]

/-- A product of elements supported in `U` and `V` is supported in `U ∪ V`. -/
theorem SupportedIn.mul_union {f g : X ≃ₜ X} {U V : Set X} (hf : SupportedIn f U)
    (hg : SupportedIn g V) : SupportedIn (f * g) (U ∪ V) := by
  intro x hx
  have hxU : x ∉ U := fun h => hx (Or.inl h)
  have hxV : x ∉ V := fun h => hx (Or.inr h)
  show f (g x) = x
  rw [hg x hxV, hf x hxU]

/-- The inverse of an element supported in `U` is supported in `U`. -/
theorem SupportedIn.inv_supportedIn {g : X ≃ₜ X} {U : Set X} (hg : SupportedIn g U) :
    SupportedIn g⁻¹ U := by
  intro x hx
  have h1 : g.symm (g x) = x := g.symm_apply_apply x
  rw [hg x hx] at h1
  exact h1

/-- Conjugating an element supported in `W` by `g` gives an element supported in `g '' W`. -/
theorem supportedIn_conj_image {a g : X ≃ₜ X} {W : Set X} (ha : SupportedIn a W) :
    SupportedIn (g * a * g⁻¹) (g '' W) :=
  (supportedIn_conj_iff g a (g '' W)).2 (ha.mono (Set.subset_preimage_image (g : X → X) W))

/-- The commutator of an element supported in `W` with `g` is supported in `W ∪ g '' W`. -/
theorem supportedIn_commutator {a g : X ≃ₜ X} {W : Set X} (ha : SupportedIn a W) :
    SupportedIn ⁅a, g⁆ (W ∪ g '' W) := by
  have e : ⁅a, g⁆ = a * (g * a⁻¹ * g⁻¹) := by
    rw [commutatorElement_def]
    simp only [mul_assoc]
  rw [e]
  exact ha.mul_union (supportedIn_conj_image ha.inv_supportedIn)

end CommLocal

/-- Pure group algebra: if `c` commutes with `b`, then `⁅a * c, b⁆ = ⁅a, b⁆`. -/
theorem commutatorElement_mul_eq_of_commute {G : Type*} [Group G] {a b c : G}
    (hbc : b * c = c * b) : ⁅a * c, b⁆ = ⁅a, b⁆ := by
  simp only [commutatorElement_def]
  rw [mul_inv_rev]
  calc a * c * b * (c⁻¹ * a⁻¹) * b⁻¹ = a * (b * c) * c⁻¹ * a⁻¹ * b⁻¹ := by
        rw [hbc]
        simp only [mul_assoc]
    _ = a * b * a⁻¹ * b⁻¹ := by
        simp only [mul_assoc, mul_inv_cancel_left]

section CommLocalDisplaced

variable {X : Type*} [TopologicalSpace X]

/-- **Commutator localisation.**  If `a` and `b` are supported in `W` and `g` displaces `W`
(`W ∩ g W = ∅`), then `⁅⁅a, g⁆, b⁆ = ⁅a, b⁆`. -/
theorem commutator_commutator_eq_of_displaced {a b g : X ≃ₜ X} {W : Set X}
    (ha : SupportedIn a W) (hb : SupportedIn b W) (hW : Disjoint W (g '' W)) :
    ⁅⁅a, g⁆, b⁆ = ⁅a, b⁆ := by
  have e : ⁅a, g⁆ = a * (g * a⁻¹ * g⁻¹) := by
    rw [commutatorElement_def]
    simp only [mul_assoc]
  have hc : SupportedIn (g * a⁻¹ * g⁻¹) (g '' W) := supportedIn_conj_image ha.inv_supportedIn
  have hsub : g '' W ⊆ Wᶜ := fun _ hy =>
    Set.mem_compl fun hyW => Set.disjoint_left.1 hW hyW hy
  have hbc : b * (g * a⁻¹ * g⁻¹) = (g * a⁻¹ * g⁻¹) * b :=
    hb.commute_of_compl (hc.mono hsub)
  rw [e]
  exact commutatorElement_mul_eq_of_commute hbc

/-- Commutator localisation inside a subgroup `H` of `X ≃ₜ X` (e.g. `topologicalFullGroup T`). -/
theorem commutator_commutator_eq_of_displaced_subgroup {H : Subgroup (X ≃ₜ X)} {a b g : H}
    {W : Set X} (ha : SupportedIn (a : X ≃ₜ X) W) (hb : SupportedIn (b : X ≃ₜ X) W)
    (hW : Disjoint W ((g : X ≃ₜ X) '' W)) : ⁅⁅a, g⁆, b⁆ = ⁅a, b⁆ := by
  apply Subtype.ext
  simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
  have h := commutator_commutator_eq_of_displaced ha hb hW
  simp only [commutatorElement_def] at h
  exact h

end CommLocalDisplaced

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.SupportedIn.mul_union
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.SupportedIn.inv_supportedIn
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.supportedIn_conj_image
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.supportedIn_commutator
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.commutatorElement_mul_eq_of_commute
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.commutator_commutator_eq_of_displaced
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.commutator_commutator_eq_of_displaced_subgroup
