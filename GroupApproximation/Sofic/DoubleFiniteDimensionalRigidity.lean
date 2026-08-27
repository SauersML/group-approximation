import GroupApproximation.Sofic.CoveringWitness
import GroupApproximation.Sofic.FreeLampRigidity
import Mathlib.LinearAlgebra.Prod

/-!
# The symmetric double of a compression pair has no faithful finite-dimensional
representation

This is the endpoint of the Kun--Thom/Shulman double construction that carries
**no literature input and no approximation hypothesis at all**.  Its only
hypotheses are the two group-theoretic words of the Kun--Thom pair:

> `Γ` is infranormal in `G`, and `Γ` is not normal in `G`.

Conclusion: for every field `k` and every finite-dimensional `k`-vector space
`V`, no homomorphism `G *_Γ G → GL(V)` is injective.

## The route

`Sofic/FreeLampRigidity` already proves, unconditionally, that every
finite-dimensional representation of the *free-lamp amalgam*
`G *_Γ (Γ × K)` kills the witness commutator, provided the compressors of `Γ`
generate `G`.  That is a statement about `H_K`, not about the double.

The bridge is `Sofic/SymmetricDoubleFlip`'s isomorphism
`H_{C₂} ≅ (G *_Γ G) ⋊ C₂`, an index-two extension.  A representation `π` of the
double therefore *induces* one of `H_{C₂}` on `V × V`: the double acts by
`π ⊕ (π ∘ flip)` and the flip acts by exchanging the two summands.  This file
builds that induced representation by hand (`freeLampTwin`) — the equivariance
it needs is exactly that the flip is an involution — applies the rigidity
theorem to it, and reads `π` back off the first summand.

Because the witness is a commutator whose lamp letters cancel, its image in the
semidirect product lies in the copy of the double, so what the rigidity theorem
kills is a genuine element of `G *_Γ G`; and it is nontrivial because the
isomorphism is injective and the witness is nontrivial.

No unitarity, no complex numbers, no trace, no ultraproduct: the argument runs
over an arbitrary field.
-/

namespace GroupApproximation

namespace DoubleFdRigidity

open SemidirectProduct

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-! ## The doubled representation -/

/-- The exchange of the two summands, as a linear automorphism of `V × V`. -/
def swapEquiv (k V : Type*) [Field k] [AddCommGroup V] [Module k V] :
    (V × V) ≃ₗ[k] (V × V) :=
  LinearEquiv.prodComm k V V

@[simp] theorem swapEquiv_apply (p : V × V) : swapEquiv k V p = p.swap := rfl

theorem swapEquiv_mul_self :
    (swapEquiv k V) * (swapEquiv k V) = 1 := by
  refine LinearEquiv.ext fun p ↦ ?_
  show swapEquiv k V (swapEquiv k V p) = p
  simp

theorem swapEquiv_inv : (swapEquiv k V)⁻¹ = swapEquiv k V :=
  inv_eq_of_mul_eq_one_left swapEquiv_mul_self

/-- The direct sum of a representation of the double with its flip twist. -/
def twin (G : Type) [Group G] (Γ : Subgroup G)
    (π : SymmetricDouble G Γ →* (V ≃ₗ[k] V)) :
    SymmetricDouble G Γ →* ((V × V) ≃ₗ[k] (V × V)) where
  toFun d := LinearEquiv.prodCongr (π d) (π (doubleSwap G Γ d))
  map_one' := by
    refine LinearEquiv.ext fun p ↦ ?_
    have h1 : doubleSwap G Γ 1 = 1 := map_one _
    show ((π 1) p.1, (π (doubleSwap G Γ 1)) p.2) = p
    simp [h1]
  map_mul' a b := by
    refine LinearEquiv.ext fun p ↦ ?_
    show ((π (a * b)) p.1, (π (doubleSwap G Γ (a * b))) p.2)
      = ((π a) ((π b) p.1), (π (doubleSwap G Γ a)) ((π (doubleSwap G Γ b)) p.2))
    simp [map_mul, LinearEquiv.mul_eq_trans]

@[simp] theorem twin_apply (G : Type) [Group G] (Γ : Subgroup G)
    (π : SymmetricDouble G Γ →* (V ≃ₗ[k] V)) (d : SymmetricDouble G Γ) :
    twin G Γ π d = LinearEquiv.prodCongr (π d) (π (doubleSwap G Γ d)) := rfl

/-- The order-two lamp acts by exchanging the two summands. -/
def twinFlip (k V : Type*) [Field k] [AddCommGroup V] [Module k V] :
    FlipC2 →* ((V × V) ≃ₗ[k] (V × V)) where
  toFun
    | .one => 1
    | .swap => swapEquiv k V
  map_one' := rfl
  map_mul' a b := by
    cases a <;> cases b <;> simp [swapEquiv_mul_self]

@[simp] theorem twinFlip_one : twinFlip k V FlipC2.one = 1 := rfl

@[simp] theorem twinFlip_swap : twinFlip k V FlipC2.swap = swapEquiv k V := rfl

/-- The exchange conjugates the doubled representation into its flip twist:
exactly the equivariance the semidirect product needs. -/
theorem twin_equivariant (G : Type) [Group G] (Γ : Subgroup G)
    (π : SymmetricDouble G Γ →* (V ≃ₗ[k] V)) (κ : FlipC2) :
    (twin G Γ π).comp (doubleFlipAction G Γ κ).toMonoidHom
      = (MulAut.conj (twinFlip k V κ)).toMonoidHom.comp (twin G Γ π) := by
  cases κ
  · refine MonoidHom.ext fun d ↦ ?_
    show twin G Γ π ((1 : MulAut (SymmetricDouble G Γ)) d)
      = MulAut.conj (1 : (V × V) ≃ₗ[k] (V × V)) (twin G Γ π d)
    simp
  · refine MonoidHom.ext fun d ↦ LinearEquiv.ext fun p ↦ ?_
    have hsq : doubleSwap G Γ (doubleSwap G Γ d) = d :=
      DFunLike.congr_fun (doubleSwapHom_sq G Γ) d
    show twin G Γ π (doubleSwap G Γ d) p
      = (swapEquiv k V * twin G Γ π d * (swapEquiv k V)⁻¹) p
    rw [swapEquiv_inv]
    simp only [twin_apply, hsq, LinearEquiv.mul_eq_trans,
      LinearEquiv.trans_apply, swapEquiv_apply, LinearEquiv.prodCongr_apply,
      Prod.fst_swap, Prod.snd_swap, Prod.swap_prod_mk]

/-- The representation of the free-lamp amalgam induced by a representation of
the double. -/
def freeLampTwin (G : Type) [Group G] (Γ : Subgroup G)
    (π : SymmetricDouble G Γ →* (V ≃ₗ[k] V)) :
    FreeLamp G Γ FlipC2 →* ((V × V) ≃ₗ[k] (V × V)) :=
  (SemidirectProduct.lift (twin G Γ π) (twinFlip k V)
    (twin_equivariant G Γ π)).comp (freeLampToFlip G Γ)

/-! ## The witness lands in the copy of the double -/

theorem rightHom_freeLampToFlip_lampWitness (G : Type) [Group G]
    (Γ : Subgroup G) (t γ : G) (κ : FlipC2) :
    SemidirectProduct.rightHom
        (freeLampToFlip G Γ (lampWitness G Γ FlipC2 t γ κ)) = 1 := by
  simp only [lampWitness, map_mul, map_inv, freeLampToFlip_inAmbient,
    freeLampToFlip_inLamp, SemidirectProduct.rightHom_inl,
    SemidirectProduct.rightHom_inr]
  group

/-- The double component of the witness. -/
def doubleComponent (G : Type) [Group G] (Γ : Subgroup G) (t γ : G)
    (κ : FlipC2) : SymmetricDouble G Γ :=
  (freeLampToFlip G Γ (lampWitness G Γ FlipC2 t γ κ)).left

theorem inl_doubleComponent (G : Type) [Group G] (Γ : Subgroup G) (t γ : G)
    (κ : FlipC2) :
    SemidirectProduct.inl (φ := doubleFlipAction G Γ)
        (doubleComponent G Γ t γ κ)
      = freeLampToFlip G Γ (lampWitness G Γ FlipC2 t γ κ) := by
  apply SemidirectProduct.ext
  · rfl
  · show (1 : FlipC2)
      = (freeLampToFlip G Γ (lampWitness G Γ FlipC2 t γ κ)).right
    exact (rightHom_freeLampToFlip_lampWitness G Γ t γ κ).symm

theorem doubleComponent_ne_one (G : Type) [Group G] (Γ : Subgroup G)
    {t γ : G} (hesc : t⁻¹ * γ * t ∉ Γ) {κ : FlipC2} (hκ : κ ≠ 1) :
    doubleComponent G Γ t γ κ ≠ 1 := by
  intro hcon
  refine lampWitness_ne_one G Γ FlipC2 hesc hκ ?_
  have h := inl_doubleComponent G Γ t γ κ
  rw [hcon, map_one] at h
  apply (freeLampMulEquivSymmetricDoubleFlip G Γ).injective
  rw [map_one]
  exact h.symm

/-! ## The endpoint -/

theorem eq_one_of_prodCongr_eq_one {e₁ e₂ : V ≃ₗ[k] V}
    (h : LinearEquiv.prodCongr e₁ e₂ = 1) : e₁ = 1 := by
  refine LinearEquiv.ext fun v ↦ ?_
  have hv := LinearEquiv.ext_iff.mp h (v, 0)
  have hfst := congrArg Prod.fst hv
  simpa using hfst

/-- **Every finite-dimensional representation of the double kills the
witness.**  The only hypothesis is that the compressors of `Γ` generate `G`. -/
theorem fdRep_kills_doubleComponent (G : Type) [Group G] (Γ : Subgroup G)
    (hinf : IsInfranormal Γ) {t γ : G} (hγ : γ ∈ Γ) [FiniteDimensional k V]
    (π : SymmetricDouble G Γ →* (V ≃ₗ[k] V)) :
    π (doubleComponent G Γ t γ FlipC2.swap) = 1 := by
  have hS : ∀ s ∈ ((compressionSubmonoid Γ : Set G)),
      ∀ δ ∈ Γ, s * δ * s⁻¹ ∈ Γ := by
    intro s hs δ hδ
    exact (mem_compressionSubmonoid.mp hs) δ hδ
  have hkill : freeLampTwin G Γ π (lampWitness G Γ FlipC2 t γ FlipC2.swap) = 1 :=
    freeLampRep_kills_witness G Γ FlipC2 ((compressionSubmonoid Γ : Set G)) hS
      hinf (freeLampTwin G Γ π) t γ hγ FlipC2.swap
  have hinlk : twin G Γ π (doubleComponent G Γ t γ FlipC2.swap) = 1 := by
    have h : (SemidirectProduct.lift (twin G Γ π) (twinFlip k V)
        (twin_equivariant G Γ π))
        (freeLampToFlip G Γ (lampWitness G Γ FlipC2 t γ FlipC2.swap)) = 1 :=
      hkill
    rw [← inl_doubleComponent, SemidirectProduct.lift_inl] at h
    exact h
  exact eq_one_of_prodCongr_eq_one hinlk

/-- **The unconditional endpoint.**  For an infranormal, non-normal pair
`Γ ≤ G`, the symmetric double `G *_Γ G` admits no injective homomorphism into
the automorphism group of a finite-dimensional vector space, over any field.

No literature input, no approximation hypothesis, and no restriction on the
field: the only hypotheses are the two group-theoretic words of the Kun--Thom
pair. -/
theorem symmetricDouble_no_faithful_fdRep (G : Type) [Group G] (Γ : Subgroup G)
    (hpair : IsCompressionPair Γ) [FiniteDimensional k V]
    (π : SymmetricDouble G Γ →* (V ≃ₗ[k] V)) : ¬ Function.Injective π := by
  intro hinj
  obtain ⟨t, γ, hγ, hesc⟩ := hpair.exists_escape
  have hπ : π (doubleComponent G Γ t γ FlipC2.swap) = 1 :=
    fdRep_kills_doubleComponent G Γ hpair.infranormal hγ π
  exact doubleComponent_ne_one G Γ hesc flipC2_swap_ne_one
    (hinj (by rw [hπ, map_one]))

end DoubleFdRigidity

end GroupApproximation
