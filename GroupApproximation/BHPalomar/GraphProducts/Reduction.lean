/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GroupApproximation.BHPalomar.GraphProducts.Embedding

/-!
# Retract amalgams of PBH groups are PBH, modulo two named inputs

The new mathematics, Steps 1–5 of `pbh-graph-product-closure-proof`, is proved without
inputs in `GroupApproximation.BHPalomar.GraphProducts.Embedding`. This file adds Step 0,
which uses two results from the literature. Both are stated here as named `Prop`s; neither is
assumed anywhere else.

* `EnvelopeInput`: a group admitting an action of type (A) embeds in a group `H` such that
  `Aut_H(H ∗ F₂)` satisfies PBH. This is BFFHZ (arXiv:2503.21882v2) Theorem C, (i) ⇒ (iv):
  the group is finitely presented, hence finitely generated, so it embeds in a finitely
  presented simple MIF group `H`. Then Theorem E with `n = 2` gives an action of type (A) of
  `Aut_H(H ∗ F₂)`.
* `ProductInput`: PBH is closed under direct products (Zaremsky, arXiv:2405.18354,
  Proposition 5.5, via the disjoint union action). This one is elementary.

`retractAmalgamClosure_of_inputs` gives `RetractAmalgamClosure` from these two. It is a
conditional theorem: its hypotheses are exactly the two inputs.
-/

namespace GroupApproximation.BHPalomar.GraphProducts

open Monoid

/-- **Literature input** (BFFHZ Theorem C (i) ⇒ (iv), then Theorem E at `n = 2`). -/
def EnvelopeInput : Prop :=
  ∀ (Γ S : Type) [Group Γ] [MulAction Γ S], IsTypeA Γ S →
    ∃ (H : Type) (_ : Group H) (e : Γ →* H), Function.Injective e ∧ SatisfiesPBH (relAut H 2)

/-- **Input** (Zaremsky, Proposition 5.5): PBH is closed under direct products. -/
def ProductInput : Prop :=
  ∀ (A B : Type) [Group A] [Group B], SatisfiesPBH A → SatisfiesPBH B → SatisfiesPBH (A × B)

/-- **Retract amalgams**: under the two inputs, `X *_C (C × K)` satisfies PBH whenever `X` and
`K` do and `C` is a retract of `X`. -/
theorem retractAmalgamClosure_of_inputs (hE : EnvelopeInput) (hP : ProductInput) :
    RetractAmalgamClosure := by
  intro X C K _ _ _ ι r hr hX hK
  obtain ⟨Γ, _, S, _, hA, f, hf⟩ := hP K X hK hX
  obtain ⟨H, _, e, he, hH⟩ := hE Γ S hA
  have hφ : Function.Injective ((e.comp f).comp (MonoidHom.inr K X)) := by
    intro a b hab
    simp only [MonoidHom.comp_apply] at hab
    exact congrArg Prod.snd (hf (he hab))
  have hψ : Function.Injective ((e.comp f).comp (MonoidHom.inl K X)) := by
    intro a b hab
    simp only [MonoidHom.comp_apply] at hab
    exact congrArg Prod.fst (hf (he hab))
  have comm : ∀ (c : C) (k : K),
      (e.comp f).comp (MonoidHom.inr K X) (ι c) * (e.comp f).comp (MonoidHom.inl K X) k =
        (e.comp f).comp (MonoidHom.inl K X) k * (e.comp f).comp (MonoidHom.inr K X) (ι c) := by
    intro c k
    simp only [MonoidHom.comp_apply, ← map_mul]
    congr 2
    ext <;> simp
  obtain ⟨g, hg⟩ := retractAmalgam_embeds_in_relAut ι r hr _ hφ _ hψ comm
  exact hH.of_injective g hg

end GroupApproximation.BHPalomar.GraphProducts
