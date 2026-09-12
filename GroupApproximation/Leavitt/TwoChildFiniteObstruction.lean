import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# A finite additive object cannot contain two split copies of itself

This is the exact dimension endpoint of the raw-compressor two-child packet.
If `S₀,S₁ : M ->+ M` have left inverses `T₀,T₁` and both cross composites
vanish, then `(x,y) |-> S₀ x + S₁ y` embeds `M × M` into `M`.  Finiteness
forces `M` to be trivial.
-/

namespace GroupApproximation

variable {M : Type*} [AddCommGroup M]

/-- The two split injections with vanishing cross terms combine to an
injection from two copies of the additive object into one. -/
theorem twoChild_pairSum_injective
    (S₀ S₁ T₀ T₁ : M →+ M)
    (h₀₀ : T₀.comp S₀ = AddMonoidHom.id M)
    (h₁₁ : T₁.comp S₁ = AddMonoidHom.id M)
    (h₀₁ : T₀.comp S₁ = 0)
    (h₁₀ : T₁.comp S₀ = 0) :
    Function.Injective (fun x : M × M ↦ S₀ x.1 + S₁ x.2) := by
  intro x y hxy
  apply Prod.ext
  · have h := congrArg T₀ hxy
    simpa [← AddMonoidHom.comp_apply, h₀₀, h₀₁] using h
  · have h := congrArg T₁ hxy
    simpa [← AddMonoidHom.comp_apply, h₁₁, h₁₀] using h

/-- **Two-child finite obstruction.**  A finite additive object admitting two
split self-embeddings with mutually vanishing cross composites is
subsingleton. -/
theorem finite_twoChild_subsingleton [Fintype M]
    (S₀ S₁ T₀ T₁ : M →+ M)
    (h₀₀ : T₀.comp S₀ = AddMonoidHom.id M)
    (h₁₁ : T₁.comp S₁ = AddMonoidHom.id M)
    (h₀₁ : T₀.comp S₁ = 0)
    (h₁₀ : T₁.comp S₀ = 0) :
    Subsingleton M := by
  let pairSum : M × M → M := fun x ↦ S₀ x.1 + S₁ x.2
  have hinj : Function.Injective pairSum :=
    twoChild_pairSum_injective S₀ S₁ T₀ T₁ h₀₀ h₁₁ h₀₁ h₁₀
  have hcard : Fintype.card (M × M) ≤ Fintype.card M :=
    Fintype.card_le_of_injective pairSum hinj
  have hsq : Fintype.card M * Fintype.card M ≤ Fintype.card M := by
    simpa using hcard
  have hpos : 0 < Fintype.card M := Fintype.card_pos_iff.mpr ⟨0⟩
  have hone : Fintype.card M ≤ 1 := by
    nlinarith
  exact ⟨Fintype.card_le_one_iff.mp hone⟩

end GroupApproximation
