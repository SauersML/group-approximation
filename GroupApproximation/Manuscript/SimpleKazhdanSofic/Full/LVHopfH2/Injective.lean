import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVHopfH2.TwistedExt

/-!
# Hopf formula versus `groupHomology.H2`: the kernel of `Φ` on cycles is `B₂` (lane LVHopfH2)

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735 (Hopf formula; Brown II.5 Thm 5.3).
Restricting the descended map `E → X = Q × G` (`hopfTwBar`) to `K` and taking the `Q`-coordinate
gives an additive map `τ : K → Q = C₂ ⧸ B₂`.  We compute `τ ∘ Φ = [·] + β ∘ ∂₂` for an explicit
`β : ℤ[G] → Q`, so a 2-cycle `c` with `Φ c = 0` has `[c] = 0`, that is, `c ∈ B₂`.

* `hopfTau f : Additive K →+ Q`.
* `hopfTau_comp_phi`: `τ ∘ Φ = [·] + β ∘ ∂₂`.
* `hopfChain_mem_range_of_phi_eq_zero`: `∂₂ c = 0` and `Φ c = 0` imply `c ∈ B₂`.
-/

namespace GroupApproximation.Full.LVHopf

section Injective

variable {G : Type} [Group G] {α : Type} {f : FreeGroup α →* G}

theorem hopfTwBar_g_of_mem_ker (z : HopfExtK f) : (hopfTwBar f (z : HopfExt f)).g = 1 :=
  (hopfTwBar_g f (z : HopfExt f)).trans (MonoidHom.mem_ker.mp z.2)

/-- On `K`, the `Q`-coordinate of `E → X` is additive, since `X`'s cocycle is normalized. -/
theorem hopfTwBar_a_mul_of_mem_ker (u v : HopfExtK f) :
    (hopfTwBar f ((u * v : HopfExtK f) : HopfExt f)).a =
      (hopfTwBar f (u : HopfExt f)).a + (hopfTwBar f (v : HopfExt f)).a := by
  show (hopfTwBar f ((u : HopfExt f) * (v : HopfExt f))).a =
    (hopfTwBar f (u : HopfExt f)).a + (hopfTwBar f (v : HopfExt f)).a
  rw [map_mul, hopfTw_mul_a, hopfTwBar_g_of_mem_ker u, hopfTwR_one_left, add_zero]

variable (f) in
/-- `τ : K → Q = C₂ ⧸ B₂`, the `Q`-coordinate of `E → X` restricted to `K` (l.733-735). -/
noncomputable def hopfTau : Additive (HopfExtK f) →+ HopfChainQuot G :=
  AddMonoidHom.mk' (fun z => (hopfTwBar f ((Additive.toMul z : HopfExtK f) : HopfExt f)).a)
    fun z w => hopfTwBar_a_mul_of_mem_ker (Additive.toMul z) (Additive.toMul w)

theorem hopfTau_apply (z : Additive (HopfExtK f)) :
    hopfTau f z = (hopfTwBar f ((Additive.toMul z : HopfExtK f) : HopfExt f)).a :=
  rfl

/-- `a g`: the `Q`-coordinate of the image of the section `σ g` in `X`. -/
noncomputable def hopfTwSecA (hf : Function.Surjective f) (g : G) : HopfChainQuot G :=
  (hopfTwBar f (hopfExtSec hf g)).a

theorem hopfExtRc_mul_sec (hf : Function.Surjective f) (g h : G) :
    hopfExtRc hf g h * hopfExtSec hf (g * h) = hopfExtSec hf g * hopfExtSec hf h :=
  inv_mul_cancel_right (hopfExtSec hf g * hopfExtSec hf h) (hopfExtSec hf (g * h))

/-- `τ (σ g σ h σ(gh)⁻¹) = a g + a h + R g h - a (g h)`. -/
theorem hopfTau_rc (hf : Function.Surjective f) (g h : G) :
    hopfTau f (hopfExtRcK hf g h) =
      hopfTwSecA hf g + hopfTwSecA hf h + hopfTwR g h - hopfTwSecA hf (g * h) := by
  have hy : (hopfTwBar f (hopfExtRc hf g h)).g = 1 :=
    (hopfTwBar_g f (hopfExtRc hf g h)).trans (MonoidHom.mem_ker.mp (hopfExtRc_mem hf g h))
  have e : (hopfTwBar f (hopfExtRc hf g h * hopfExtSec hf (g * h))).a =
      (hopfTwBar f (hopfExtSec hf g * hopfExtSec hf h)).a := by
    rw [hopfExtRc_mul_sec hf g h]
  rw [map_mul, map_mul, hopfTw_mul_a, hopfTw_mul_a, hy, hopfTwR_one_left, add_zero,
    hopfTwBar_g f (hopfExtSec hf g), hopfTwBar_g f (hopfExtSec hf h), hopfExtProj_sec hf g,
    hopfExtProj_sec hf h] at e
  exact eq_sub_of_add_eq e

/-- `β : ℤ[G] → Q`, `g ↦ a g - q 1 1`. -/
noncomputable def hopfBeta (hf : Function.Surjective f) : (G →₀ ℤ) →+ HopfChainQuot G :=
  Finsupp.liftAddHom fun g => zmultiplesHom (HopfChainQuot G) (hopfTwSecA hf g - hopfTwQ 1 1)

theorem hopfBeta_single_one (hf : Function.Surjective f) (g : G) :
    hopfBeta hf (Finsupp.single g 1) = hopfTwSecA hf g - hopfTwQ 1 1 := by
  simp only [hopfBeta, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, one_zsmul]

/-- `τ ∘ Φ = [·] + β ∘ ∂₂` (Hopf formula, l.733-735). -/
theorem hopfTau_comp_phi (hf : Function.Surjective f) :
    (hopfTau f).comp (hopfChainPhi hf) =
      QuotientAddGroup.mk' (hopfChainD3 (G := G)).range + (hopfBeta hf).comp hopfChainD := by
  apply hopfChain_addHom_ext
  rintro ⟨g, h⟩
  rw [AddMonoidHom.comp_apply, hopfChainPhi_single_one hf g h, hopfTau_rc hf g h, hopfTwR,
    AddMonoidHom.add_apply, AddMonoidHom.comp_apply, hopfChainD_single g h 1, map_add, map_sub,
    hopfBeta_single_one hf h, hopfBeta_single_one hf (g * h), hopfBeta_single_one hf g,
    ← hopfTwQ_def g h]
  abel

/-- A 2-cycle killed by `Φ` is a 2-boundary (Hopf formula, l.733-735). -/
theorem hopfChain_mem_range_of_phi_eq_zero (hf : Function.Surjective f) {c : G × G →₀ ℤ}
    (hc : hopfChainD c = 0) (hΦ : hopfChainPhi hf c = 0) :
    c ∈ (hopfChainD3 (G := G)).range := by
  have h := DFunLike.congr_fun (hopfTau_comp_phi hf) c
  rw [AddMonoidHom.comp_apply, hΦ, map_zero, AddMonoidHom.add_apply, AddMonoidHom.comp_apply, hc,
    map_zero, add_zero, QuotientAddGroup.mk'_apply, eq_comm, QuotientAddGroup.eq_zero_iff] at h
  exact h

end Injective

end GroupApproximation.Full.LVHopf
