import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.RelPresSurj
import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.RelPresElt
import GroupApproximation.Meta.AxiomGuard

/-!
# Tulenbaev's Prop 1.6: `St(A) ≅ St(B) ⋉ St(A, ker ρ)` (k2-poly, pieces F.2 and F.3)

Let `ι : B → A`, `ρ : A → B` be ring maps with `ρ ∘ ι = id`, and let `hX : VdK.Elements I A` be van
der Kallen's elements (F.1, lane k2-vdk). Then:
* `phiSD : St(A, ker ρ) ⋊ St(B) →* St(A)`, `(X_{v,w}, g) ↦ X(v, w) · ι(g)`, and
  `phiSD ∘ psi = id` (`phiSD_psi`); with `psi_surjective`, `psi` is an isomorphism
  (`stSplitEquiv`);
* `can_injective`: the presented relative group injects into `St(A)`;
* `range_can`: its image is `ker (ringMap ρ)`;
* **`relStEquivKer : St(A, ker ρ) ≃* ker (St(A) → St(B))`**, with `X_{v,w} ↦ X(v, w)`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace K2Found
namespace RelPres

open Matrix
open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigmanLinear.K2Found.VdK (conjPair stdPair Elements)

variable {I A B : Type*} [Fintype I] [DecidableEq I] [CommRing A] [CommRing B]
  (ι : B →+* A) (ρ : A →+* B) (hρ : ∀ b, ρ (ι b) = b) (hX : Elements I A)

/-- `φ : St(A, ker ρ) ⋊ St(B) →* St(A)`, `(n, g) ↦ can(n) · ι(g)`. -/
noncomputable def phiSD : SD I ι ρ →* SteinbergGroup I A :=
  SemidirectProduct.lift (can hX (RingHom.ker ρ)) (ringMap ι) fun g => by
    apply PresentedGroup.ext
    rintro ⟨p, hp⟩
    change can hX _ (actAut I A _ (elementaryGroupMap ι (projection g)) (X p hp)) =
      ringMap ι g * can hX _ (X p hp) * (ringMap ι g)⁻¹
    rw [actAut_X, can_X, can_X, elt_conj]
    exact elt_congr hX (by rw [projection_ringMap]) _ _

theorem phiSD_inl (n : RelSt I A (RingHom.ker ρ)) :
    phiSD ι ρ hX (SemidirectProduct.inl n) = can hX _ n :=
  SemidirectProduct.lift_inl _ _ _ _

#audit_axioms phiSD_inl

theorem phiSD_inr (g : SteinbergGroup I B) :
    phiSD ι ρ hX (SemidirectProduct.inr g) = ringMap ι g :=
  SemidirectProduct.lift_inr _ _ _ _

#audit_axioms phiSD_inr

theorem phiSD_psi (y : SteinbergGroup I A) : phiSD ι ρ hX (psi ι ρ hρ y) = y := by
  have h : (phiSD ι ρ hX).comp (psi ι ρ hρ) = MonoidHom.id _ := by
    apply PresentedGroup.ext
    rintro ⟨i, j, hij, a⟩
    change phiSD ι ρ hX (psi ι ρ hρ (x i j hij a)) = x i j hij a
    rw [psi_x]
    unfold psiX
    rw [map_mul, phiSD_inl, phiSD_inr, can_X, ringMap_x, hX.std i j hij (a - ι (ρ a)), x_mul,
      sub_add_cancel]
  exact DFunLike.congr_fun h y

#audit_axioms phiSD_psi

theorem psi_phiSD (z : SD I ι ρ) : psi ι ρ hρ (phiSD ι ρ hX z) = z := by
  obtain ⟨y, rfl⟩ := psi_surjective ι ρ hρ z
  rw [phiSD_psi]

#audit_axioms psi_phiSD

/-- **Tulenbaev's Prop 1.6**: `ψ : St(A) ≃* St(A, ker ρ) ⋊ St(B)`. -/
noncomputable def stSplitEquiv : SteinbergGroup I A ≃* SD I ι ρ :=
  MulEquiv.ofBijective (psi ι ρ hρ)
    ⟨Function.LeftInverse.injective (phiSD_psi ι ρ hρ hX), psi_surjective ι ρ hρ⟩

include hρ in
/-- The presented relative group injects into `St(A)`. -/
theorem can_injective : Function.Injective (can hX (RingHom.ker ρ) : RelSt I A _ → _) := by
  intro n n' h
  have h' : psi ι ρ hρ (phiSD ι ρ hX (SemidirectProduct.inl n)) =
      psi ι ρ hρ (phiSD ι ρ hX (SemidirectProduct.inl n')) := by
    rw [phiSD_inl, phiSD_inl, h]
  rw [psi_phiSD, psi_phiSD] at h'
  exact SemidirectProduct.inl_injective h'

#audit_axioms can_injective

theorem ringMap_eq_rightHom :
    ringMap (I := I) ρ = SemidirectProduct.rightHom.comp (psi ι ρ hρ) := by
  apply PresentedGroup.ext
  rintro ⟨i, j, hij, a⟩
  change ringMap ρ (x i j hij a) = SemidirectProduct.rightHom (psi ι ρ hρ (x i j hij a))
  rw [ringMap_x, psi_x]
  unfold psiX
  rw [map_mul, SemidirectProduct.rightHom_inl, SemidirectProduct.rightHom_inr, one_mul]

#audit_axioms ringMap_eq_rightHom

include hρ in
/-- The image of `St(A, ker ρ)` is `ker (St(A) → St(B))`. -/
theorem range_can :
    (can hX (RingHom.ker ρ) : RelSt I A _ →* _).range = (ringMap (I := I) ρ).ker := by
  ext y
  rw [MonoidHom.mem_range, MonoidHom.mem_ker, ringMap_eq_rightHom ι ρ hρ, MonoidHom.comp_apply]
  constructor
  · rintro ⟨n, rfl⟩
    rw [← phiSD_inl ι ρ hX, psi_phiSD, SemidirectProduct.rightHom_inl]
  · intro h
    have hm : psi ι ρ hρ y ∈ (SemidirectProduct.inl : _ →* SD I ι ρ).range := by
      rw [SemidirectProduct.range_inl_eq_ker_rightHom]
      exact MonoidHom.mem_ker.mpr h
    obtain ⟨n, hn⟩ := hm
    exact ⟨n, by rw [← phiSD_inl ι ρ hX, hn, phiSD_psi]⟩

#audit_axioms range_can

/-- **The presented relative group is the kernel** (Tulenbaev Def 1.5 + Prop 1.6, F.2/F.3):
`St(A, ker ρ) ≃* ker (ringMap ρ : St(A) → St(B))`, sending `X_{v,w}` to van der Kallen's
`X(v, w)`. -/
noncomputable def relStEquivKer : RelSt I A (RingHom.ker ρ) ≃* (ringMap (I := I) ρ).ker :=
  (MonoidHom.ofInjective (can_injective ι ρ hρ hX)).trans
    (MulEquiv.subgroupCongr (range_can ι ρ hρ hX))

theorem relStEquivKer_apply (n : RelSt I A (RingHom.ker ρ)) :
    (relStEquivKer ι ρ hρ hX n : SteinbergGroup I A) = can hX _ n :=
  rfl

#audit_axioms relStEquivKer_apply

theorem relStEquivKer_X (p : (I → A) × (I → A)) (hp : RMem (RingHom.ker ρ) p) :
    (relStEquivKer ι ρ hρ hX (X p hp) : SteinbergGroup I A) = hX.elt p hp.mem_U :=
  can_X hX _ p hp

#audit_axioms relStEquivKer_X

end RelPres
end K2Found
end BooneHigmanLinear
end GroupApproximation
