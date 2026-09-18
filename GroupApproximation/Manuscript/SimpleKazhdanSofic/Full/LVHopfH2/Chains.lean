import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVHopfH2.Setup
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic.Abel

/-!
# Hopf formula versus `groupHomology.H2`: integral inhomogeneous chains (lane LVHopfH2)

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735 (Hopf formula; Brown II.5 Thm 5.3).
Low-degree integral inhomogeneous chains of `G` with trivial coefficients, written with `ℤ`-valued
finsupps (these agree with Mathlib's `groupHomology.d₂₁`, `groupHomology.d₃₂` for
`Rep.trivial ℤ G ℤ`; see `H2.lean`).

* `hopfChainD : ℤ[G²] → ℤ[G]`, `(g,h) ↦ h - gh + g`.
* `hopfChainD3 : ℤ[G³] → ℤ[G²]`, `(g,h,k) ↦ (h,k) - (gh,k) + (g,hk) - (g,h)`.
* `hopfChainPhi hf : ℤ[G²] → K`, `(g,h) ↦ σ g σ h σ(gh)⁻¹`, the factor set of `E → G`.
* `hopfChainPhi_d3`: `Φ` vanishes on 2-boundaries.
-/

namespace GroupApproximation.Full.LVHopf

section Chains

variable {G : Type} [Group G]

/-- Additive maps out of `β →₀ ℤ` agree once they agree on every `single a 1`. -/
theorem hopfChain_addHom_ext {β N : Type} [AddMonoid N] ⦃φ ψ : (β →₀ ℤ) →+ N⦄
    (H : ∀ a, φ (Finsupp.single a 1) = ψ (Finsupp.single a 1)) : φ = ψ :=
  Finsupp.addHom_ext' fun a => AddMonoidHom.ext_int (H a)

/-- The integral inhomogeneous boundary `ℤ[G²] → ℤ[G]`, `(g,h) ↦ h - gh + g`. -/
noncomputable def hopfChainD : (G × G →₀ ℤ) →+ (G →₀ ℤ) :=
  Finsupp.liftAddHom fun p =>
    Finsupp.singleAddHom p.2 - Finsupp.singleAddHom (p.1 * p.2) + Finsupp.singleAddHom p.1

theorem hopfChainD_single (g h : G) (n : ℤ) :
    hopfChainD (Finsupp.single (g, h) n) =
      Finsupp.single h n - Finsupp.single (g * h) n + Finsupp.single g n := by
  simp only [hopfChainD, Finsupp.liftAddHom_apply_single, AddMonoidHom.add_apply,
    AddMonoidHom.sub_apply, Finsupp.singleAddHom_apply]

/-- The integral inhomogeneous boundary `ℤ[G³] → ℤ[G²]`,
`(g,h,k) ↦ (h,k) - (gh,k) + (g,hk) - (g,h)`. -/
noncomputable def hopfChainD3 : (G × G × G →₀ ℤ) →+ (G × G →₀ ℤ) :=
  Finsupp.liftAddHom fun p =>
    Finsupp.singleAddHom (p.2.1, p.2.2) - Finsupp.singleAddHom (p.1 * p.2.1, p.2.2) +
      Finsupp.singleAddHom (p.1, p.2.1 * p.2.2) - Finsupp.singleAddHom (p.1, p.2.1)

theorem hopfChainD3_single (g h k : G) (n : ℤ) :
    hopfChainD3 (Finsupp.single (g, h, k) n) =
      Finsupp.single (h, k) n - Finsupp.single (g * h, k) n + Finsupp.single (g, h * k) n -
        Finsupp.single (g, h) n := by
  simp only [hopfChainD3, Finsupp.liftAddHom_apply_single, AddMonoidHom.add_apply,
    AddMonoidHom.sub_apply, Finsupp.singleAddHom_apply]

variable {α : Type} {f : FreeGroup α →* G}

/-- The factor set of the central extension `E → G`, extended additively to 2-chains:
`(g,h) ↦ σ g σ h σ(gh)⁻¹ ∈ K`. -/
noncomputable def hopfChainPhi (hf : Function.Surjective f) :
    (G × G →₀ ℤ) →+ Additive (HopfExtK f) :=
  Finsupp.liftAddHom fun p => zmultiplesHom (Additive (HopfExtK f)) (hopfExtRcK hf p.1 p.2)

theorem hopfChainPhi_single_one (hf : Function.Surjective f) (g h : G) :
    hopfChainPhi hf (Finsupp.single (g, h) 1) = hopfExtRcK hf g h := by
  simp only [hopfChainPhi, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, one_zsmul]

/-- `Φ ∘ ∂₃ = 0`: the factor set is a cocycle, so `Φ` kills 2-boundaries. -/
theorem hopfChainPhi_comp_d3 (hf : Function.Surjective f) :
    (hopfChainPhi hf).comp hopfChainD3 = 0 := by
  apply hopfChain_addHom_ext
  rintro ⟨g, h, k⟩
  rw [AddMonoidHom.comp_apply, hopfChainD3_single, map_sub, map_add, map_sub,
    hopfChainPhi_single_one hf h k, hopfChainPhi_single_one hf (g * h) k,
    hopfChainPhi_single_one hf g (h * k), hopfChainPhi_single_one hf g h,
    AddMonoidHom.zero_apply]
  have e : hopfExtRcK hf h k - hopfExtRcK hf (g * h) k + hopfExtRcK hf g (h * k) -
      hopfExtRcK hf g h =
        (hopfExtRcK hf h k + hopfExtRcK hf g (h * k)) -
          (hopfExtRcK hf g h + hopfExtRcK hf (g * h) k) := by
    abel
  rw [e, hopfExtRcK_cocycle hf g h k, sub_self]

theorem hopfChainPhi_d3 (hf : Function.Surjective f) (c : G × G × G →₀ ℤ) :
    hopfChainPhi hf (hopfChainD3 c) = 0 := by
  have h := DFunLike.congr_fun (hopfChainPhi_comp_d3 hf) c
  rw [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply] at h
  exact h

theorem hopfChainPhi_of_mem_range (hf : Function.Surjective f) {c : G × G →₀ ℤ}
    (hc : c ∈ (hopfChainD3 (G := G)).range) : hopfChainPhi hf c = 0 := by
  obtain ⟨b, rfl⟩ := AddMonoidHom.mem_range.mp hc
  exact hopfChainPhi_d3 hf b

end Chains

end GroupApproximation.Full.LVHopf
