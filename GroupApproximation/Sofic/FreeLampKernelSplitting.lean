import GroupApproximation.Sofic.CommensurabilityInvariance
import GroupApproximation.Sofic.FreeLampReduction
import GroupApproximation.Sofic.IteratedDoubleAmalgam
import GroupApproximation.Sofic.SoficFiniteSemidirect
import Mathlib.GroupTheory.SemidirectProduct

/-!
# The Bass--Serre splitting of the free-lamp amalgam

The free-lamp amalgam `H_K = G *_Γ (Γ × K)` retracts onto the lamp group `K`:
kill the ambient factor, and read off the second coordinate of `Γ × K`.  The
covering description of the kernel is the identity

```text
ker (H_K → K)  ≅  ⋆_{Γ, k ∈ K} G,
```

the Bass--Serre covering with one central `Γ`-vertex and one `G`-vertex per
element of `K`; and `H_K` is the semidirect product of that kernel by `K`
acting on the vertex set by left translation.  This file proves that identity
in the strong form -- an explicit isomorphism with an explicit inverse
(`freeLampEquivSemidirect`) -- together with the two permanence consequences it
exists to supply.

## Why this is the load-bearing algebra

The Kun--Thom/Shulman double construction needs the free-lamp amalgam to be
operator-MF.  There is no reason for the amalgam itself to be visible to a
*symmetric* amalgamation theorem: it is an amalgam of `G` with `Γ × K`, and the
second factor is not a copy of the first.  The covering above is what repairs
that.  The kernel *is* an iterated amalgam of copies of one group over one
subgroup -- exactly the shape a symmetric amalgamation theorem accepts -- and
`K` is finite, so the ambient group inherits the property from the kernel by
induction of corona representations, `InducedCorona.isOperatorMF_of_finiteIndex_subgroup`,
already proved in this repository.

So `isOperatorMF_freeLamp_of_isOperatorMF_iterated` discharges everything
between "the iterated amalgam is MF" and "the free-lamp amalgam is MF".  The
same covering gives soficity in both directions.

Nothing here is conditional, and nothing here quantifies over sofic
approximations or over any analytic object.
-/

namespace GroupApproximation

open Monoid

/-! ## The retraction onto the lamp group -/

/-- The factor maps of the retraction: kill the ambient group, project the
lamp-augmented edge group onto its lamp coordinate. -/
def lampRetractionMaps (G : Type) [Group G] (Γ : Subgroup G) (K : Type)
    [Group K] : ∀ b, LampFactor G Γ K b →* K
  | true => (1 : G →* K)
  | false => MonoidHom.snd ↥Γ K

theorem lampRetractionMaps_comp (G : Type) [Group G] (Γ : Subgroup G)
    (K : Type) [Group K] :
    ∀ b, (lampRetractionMaps G Γ K b).comp (lampMap G Γ K b)
      = (1 : ↥Γ →* K) := by
  intro b
  cases b
  · ext γ
    rfl
  · ext γ
    rfl

/-- **The lamp retraction** `G *_Γ (Γ × K) → K`. -/
def lampRetraction (G : Type) [Group G] (Γ : Subgroup G) (K : Type) [Group K] :
    FreeLamp G Γ K →* K :=
  PushoutI.lift (lampRetractionMaps G Γ K) (1 : ↥Γ →* K)
    (lampRetractionMaps_comp G Γ K)

@[simp] theorem lampRetraction_inAmbient (G : Type) [Group G] (Γ : Subgroup G)
    (K : Type) [Group K] (g : G) :
    lampRetraction G Γ K (inAmbient G Γ K g) = 1 := by
  have h : lampRetraction G Γ K (inAmbient G Γ K g)
      = lampRetractionMaps G Γ K true g := PushoutI.lift_of _ _ _ _
  rw [h]
  rfl

@[simp] theorem lampRetraction_inLamp (G : Type) [Group G] (Γ : Subgroup G)
    (K : Type) [Group K] (k : K) :
    lampRetraction G Γ K (inLamp G Γ K k) = k := by
  have h : lampRetraction G Γ K (inLamp G Γ K k)
      = lampRetractionMaps G Γ K false ((1 : ↥Γ), k) :=
    PushoutI.lift_of _ _ _ _
  rw [h]
  rfl

theorem lampRetraction_surjective (G : Type) [Group G] (Γ : Subgroup G)
    (K : Type) [Group K] : Function.Surjective (lampRetraction G Γ K) :=
  fun k ↦ ⟨inLamp G Γ K k, lampRetraction_inLamp G Γ K k⟩

/-- The Bass--Serre covering kernel of the free-lamp amalgam. -/
abbrev lampKernel (G : Type) [Group G] (Γ : Subgroup G) (K : Type) [Group K] :
    Subgroup (FreeLamp G Γ K) := (lampRetraction G Γ K).ker

instance lampKernel_finiteIndex (G : Type) [Group G] (Γ : Subgroup G)
    (K : Type) [Group K] [Finite K] : (lampKernel G Γ K).FiniteIndex := by
  haveI : Finite (FreeLamp G Γ K ⧸ lampKernel G Γ K) :=
    Finite.of_injective ⇑(QuotientGroup.kerLift (lampRetraction G Γ K))
      (QuotientGroup.kerLift_injective _)
  exact Subgroup.finiteIndex_of_finite_quotient

/-! ## Two elementary identities in the amalgam -/

theorem freeLampBase_eq_inAmbient (G : Type) [Group G] (Γ : Subgroup G) (K : Type)
    [Group K] (γ : ↥Γ) :
    PushoutI.base (lampMap G Γ K) γ = inAmbient G Γ K (γ : G) :=
  (PushoutI.of_apply_eq_base (lampMap G Γ K) true γ).symm

/-- Every element of the lamp-augmented edge group factors as an ambient
element times a lamp element. -/
theorem freeLamp_of_false_apply (G : Type) [Group G] (Γ : Subgroup G) (K : Type)
    [Group K] (p : ↥Γ × K) :
    (PushoutI.of (φ := lampMap G Γ K) false p)
      = inAmbient G Γ K (p.1 : G) * inLamp G Γ K p.2 := by
  have h : ((p.1, (1 : K)) : ↥Γ × K) * (((1 : ↥Γ), p.2) : ↥Γ × K) = p := by
    simp
  calc PushoutI.of (φ := lampMap G Γ K) false p
      = PushoutI.of (φ := lampMap G Γ K) false
          (((p.1, (1 : K)) : ↥Γ × K) * (((1 : ↥Γ), p.2) : ↥Γ × K)) := by
        rw [h]
    _ = PushoutI.of (φ := lampMap G Γ K) false ((p.1, (1 : K)) : ↥Γ × K)
          * PushoutI.of (φ := lampMap G Γ K) false (((1 : ↥Γ), p.2) : ↥Γ × K) :=
        map_mul _ _ _
    _ = inAmbient G Γ K (p.1 : G) * inLamp G Γ K p.2 := by
        rw [← inLamp_apply, ← freeLampBase_eq_inAmbient]
        congr 1
        exact PushoutI.of_apply_eq_base (lampMap G Γ K) false p.1

/-! ## The `K`-indexed amalgam maps into the amalgam -/

/-- The `k`-th conjugate copy of the ambient group inside the free-lamp
amalgam. -/
def lampConj (G : Type) [Group G] (Γ : Subgroup G) (K : Type) [Group K]
    (k : K) : G →* FreeLamp G Γ K where
  toFun g := inLamp G Γ K k * inAmbient G Γ K g * (inLamp G Γ K k)⁻¹
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul]
    group

@[simp] theorem lampConj_apply (G : Type) [Group G] (Γ : Subgroup G) (K : Type)
    [Group K] (k : K) (g : G) :
    lampConj G Γ K k g
      = inLamp G Γ K k * inAmbient G Γ K g * (inLamp G Γ K k)⁻¹ := rfl

theorem lampConj_comp_subtype (G : Type) [Group G] (Γ : Subgroup G) (K : Type)
    [Group K] (k : K) :
    (lampConj G Γ K k).comp Γ.subtype = (inAmbient G Γ K).comp Γ.subtype := by
  ext γ
  show inLamp G Γ K k * inAmbient G Γ K (γ : G) * (inLamp G Γ K k)⁻¹
    = inAmbient G Γ K (γ : G)
  rw [(inLamp_commute_inAmbient G Γ K k γ.2).eq, mul_inv_cancel_right]

/-- **The covering map.**  The `K`-fold amalgam of copies of `G` over `Γ` maps
into the free-lamp amalgam by conjugating the `k`-th copy by the `k`-th
lamp. -/
def iteratedToFreeLamp (G : Type) [Group G] (Γ : Subgroup G) (K : Type)
    [Group K] : IteratedDouble G Γ K →* FreeLamp G Γ K :=
  PushoutI.lift (fun k ↦ lampConj G Γ K k)
    ((inAmbient G Γ K).comp Γ.subtype) (lampConj_comp_subtype G Γ K)

@[simp] theorem iteratedToFreeLamp_inIterated (G : Type) [Group G]
    (Γ : Subgroup G) (K : Type) [Group K] (k : K) (g : G) :
    iteratedToFreeLamp G Γ K (inIterated G Γ K k g)
      = inLamp G Γ K k * inAmbient G Γ K g * (inLamp G Γ K k)⁻¹ :=
  PushoutI.lift_of _ _ _ _

@[simp] theorem iteratedToFreeLamp_base (G : Type) [Group G] (Γ : Subgroup G)
    (K : Type) [Group K] (γ : ↥Γ) :
    iteratedToFreeLamp G Γ K (PushoutI.base (iteratedMap G Γ K) γ)
      = inAmbient G Γ K (γ : G) :=
  PushoutI.lift_base _ _ _ _

/-! ## The lamp group acts on the vertex set -/

/-- Left translation of the vertex set by a lamp element, as an automorphism of
the `K`-indexed amalgam. -/
def lampShift (G : Type) [Group G] (Γ : Subgroup G) (K : Type) [Group K]
    (k : K) : MulAut (IteratedDouble G Γ K) where
  toFun := iteratedRelabel G Γ (fun m : K ↦ k * m)
  invFun := iteratedRelabel G Γ (fun m : K ↦ k⁻¹ * m)
  left_inv := iteratedRelabel_leftInverse G Γ
    (f := fun m : K ↦ k * m) (g := fun m : K ↦ k⁻¹ * m) (fun m ↦ by simp)
  right_inv := iteratedRelabel_leftInverse G Γ
    (f := fun m : K ↦ k⁻¹ * m) (g := fun m : K ↦ k * m) (fun m ↦ by simp)
  map_mul' := (iteratedRelabel G Γ (fun m : K ↦ k * m)).map_mul

@[simp] theorem lampShift_inIterated (G : Type) [Group G] (Γ : Subgroup G)
    (K : Type) [Group K] (k j : K) (g : G) :
    lampShift G Γ K k (inIterated G Γ K j g) = inIterated G Γ K (k * j) g := by
  show iteratedRelabel G Γ (fun m : K ↦ k * m) (inIterated G Γ K j g) = _
  rw [iteratedRelabel_inIterated]

@[simp] theorem lampShift_base (G : Type) [Group G] (Γ : Subgroup G) (K : Type)
    [Group K] (k : K) (γ : ↥Γ) :
    lampShift G Γ K k (PushoutI.base (iteratedMap G Γ K) γ)
      = PushoutI.base (iteratedMap G Γ K) γ := by
  show iteratedRelabel G Γ (fun m : K ↦ k * m)
    (PushoutI.base (iteratedMap G Γ K) γ) = _
  rw [iteratedRelabel_base]

theorem lampShift_one (G : Type) [Group G] (Γ : Subgroup G) (K : Type)
    [Group K] : lampShift G Γ K (1 : K) = 1 := by
  refine iteratedDouble_mulAut_ext G Γ (fun j x ↦ ?_) (fun γ ↦ ?_)
  · show lampShift G Γ K (1 : K) (inIterated G Γ K j x) = inIterated G Γ K j x
    rw [lampShift_inIterated, one_mul]
  · show lampShift G Γ K (1 : K) (PushoutI.base (iteratedMap G Γ K) γ)
      = PushoutI.base (iteratedMap G Γ K) γ
    rw [lampShift_base]

theorem lampShift_mul (G : Type) [Group G] (Γ : Subgroup G) (K : Type)
    [Group K] (k₁ k₂ : K) :
    lampShift G Γ K (k₁ * k₂) = lampShift G Γ K k₁ * lampShift G Γ K k₂ := by
  refine iteratedDouble_mulAut_ext G Γ (fun j x ↦ ?_) (fun γ ↦ ?_)
  · show lampShift G Γ K (k₁ * k₂) (inIterated G Γ K j x)
      = lampShift G Γ K k₁ (lampShift G Γ K k₂ (inIterated G Γ K j x))
    simp only [lampShift_inIterated, mul_assoc]
  · show lampShift G Γ K (k₁ * k₂) (PushoutI.base (iteratedMap G Γ K) γ)
      = lampShift G Γ K k₁ (lampShift G Γ K k₂
          (PushoutI.base (iteratedMap G Γ K) γ))
    simp only [lampShift_base]

/-- The action of the lamp group on the vertex set of the covering. -/
def lampIndexAction (G : Type) [Group G] (Γ : Subgroup G) (K : Type)
    [Group K] : K →* MulAut (IteratedDouble G Γ K) where
  toFun := lampShift G Γ K
  map_one' := lampShift_one G Γ K
  map_mul' := lampShift_mul G Γ K

@[simp] theorem lampIndexAction_apply (G : Type) [Group G] (Γ : Subgroup G)
    (K : Type) [Group K] (k : K) :
    lampIndexAction G Γ K k = lampShift G Γ K k := rfl

/-- The covering map intertwines the vertex action with conjugation by the
lamp. -/
theorem iteratedToFreeLamp_equivariant (G : Type) [Group G] (Γ : Subgroup G)
    (K : Type) [Group K] (k : K) :
    (iteratedToFreeLamp G Γ K).comp (lampIndexAction G Γ K k).toMonoidHom
      = (MulAut.conj (inLamp G Γ K k)).toMonoidHom.comp
          (iteratedToFreeLamp G Γ K) := by
  refine iteratedDouble_hom_ext G Γ (fun j x ↦ ?_) (fun γ ↦ ?_)
  · show iteratedToFreeLamp G Γ K (lampShift G Γ K k (inIterated G Γ K j x))
      = inLamp G Γ K k * iteratedToFreeLamp G Γ K (inIterated G Γ K j x)
        * (inLamp G Γ K k)⁻¹
    rw [lampShift_inIterated, iteratedToFreeLamp_inIterated,
      iteratedToFreeLamp_inIterated]
    have hkj : inLamp G Γ K (k * j) = inLamp G Γ K k * inLamp G Γ K j :=
      map_mul _ _ _
    rw [hkj]
    group
  · show iteratedToFreeLamp G Γ K
        (lampShift G Γ K k (PushoutI.base (iteratedMap G Γ K) γ))
      = inLamp G Γ K k * iteratedToFreeLamp G Γ K
          (PushoutI.base (iteratedMap G Γ K) γ) * (inLamp G Γ K k)⁻¹
    rw [lampShift_base, iteratedToFreeLamp_base,
      (inLamp_commute_inAmbient G Γ K k γ.2).eq, mul_inv_cancel_right]

/-! ## The two directions of the splitting -/

/-- From the semidirect product to the amalgam. -/
def freeLampOfSemidirect (G : Type) [Group G] (Γ : Subgroup G) (K : Type)
    [Group K] :
    (IteratedDouble G Γ K) ⋊[lampIndexAction G Γ K] K →* FreeLamp G Γ K :=
  SemidirectProduct.lift (iteratedToFreeLamp G Γ K) (inLamp G Γ K)
    (iteratedToFreeLamp_equivariant G Γ K)

@[simp] theorem freeLampOfSemidirect_inl (G : Type) [Group G] (Γ : Subgroup G)
    (K : Type) [Group K] (x : IteratedDouble G Γ K) :
    freeLampOfSemidirect G Γ K (SemidirectProduct.inl x)
      = iteratedToFreeLamp G Γ K x :=
  SemidirectProduct.lift_inl _ _ _ _

@[simp] theorem freeLampOfSemidirect_inr (G : Type) [Group G] (Γ : Subgroup G)
    (K : Type) [Group K] (k : K) :
    freeLampOfSemidirect G Γ K (SemidirectProduct.inr k) = inLamp G Γ K k :=
  SemidirectProduct.lift_inr _ _ _ _

/-- The lamp-augmented edge group maps into the semidirect product: the
peripheral coordinate goes to the common `Γ`-vertex, the lamp coordinate to the
acting factor. -/
def lampFactorToSemidirect (G : Type) [Group G] (Γ : Subgroup G) (K : Type)
    [Group K] :
    ↥Γ × K →* (IteratedDouble G Γ K) ⋊[lampIndexAction G Γ K] K where
  toFun p := ⟨PushoutI.base (iteratedMap G Γ K) p.1, p.2⟩
  map_one' := by
    apply SemidirectProduct.ext
    · show PushoutI.base (iteratedMap G Γ K) (1 : ↥Γ) = 1
      exact map_one _
    · rfl
  map_mul' a b := by
    apply SemidirectProduct.ext
    · show PushoutI.base (iteratedMap G Γ K) (a.1 * b.1)
        = PushoutI.base (iteratedMap G Γ K) a.1
          * lampIndexAction G Γ K a.2 (PushoutI.base (iteratedMap G Γ K) b.1)
      rw [map_mul, lampIndexAction_apply, lampShift_base]
    · rfl

@[simp] theorem lampFactorToSemidirect_apply (G : Type) [Group G]
    (Γ : Subgroup G) (K : Type) [Group K] (p : ↥Γ × K) :
    lampFactorToSemidirect G Γ K p
      = ⟨PushoutI.base (iteratedMap G Γ K) p.1, p.2⟩ := rfl

/-- The factor maps of the inverse splitting. -/
def freeLampToSemidirectMaps (G : Type) [Group G] (Γ : Subgroup G) (K : Type)
    [Group K] : ∀ b,
      LampFactor G Γ K b →* (IteratedDouble G Γ K) ⋊[lampIndexAction G Γ K] K
  | true => (SemidirectProduct.inl).comp (inIterated G Γ K 1)
  | false => lampFactorToSemidirect G Γ K

set_option backward.isDefEq.respectTransparency false in
theorem freeLampToSemidirectMaps_comp (G : Type) [Group G] (Γ : Subgroup G)
    (K : Type) [Group K] :
    ∀ b, (freeLampToSemidirectMaps G Γ K b).comp (lampMap G Γ K b)
      = (SemidirectProduct.inl).comp
          (PushoutI.base (iteratedMap G Γ K)) := by
  intro b
  cases b
  · rfl
  · refine MonoidHom.ext fun γ ↦ ?_
    show SemidirectProduct.inl (φ := lampIndexAction G Γ K)
        (inIterated G Γ K 1 (γ : G))
      = SemidirectProduct.inl (φ := lampIndexAction G Γ K)
        (PushoutI.base (iteratedMap G Γ K) γ)
    rw [inIterated_coe_subgroup]

/-- From the amalgam to the semidirect product. -/
def freeLampToSemidirect (G : Type) [Group G] (Γ : Subgroup G) (K : Type)
    [Group K] :
    FreeLamp G Γ K →* (IteratedDouble G Γ K) ⋊[lampIndexAction G Γ K] K :=
  PushoutI.lift (freeLampToSemidirectMaps G Γ K)
    ((SemidirectProduct.inl).comp (PushoutI.base (iteratedMap G Γ K)))
    (freeLampToSemidirectMaps_comp G Γ K)

@[simp] theorem freeLampToSemidirect_inAmbient (G : Type) [Group G]
    (Γ : Subgroup G) (K : Type) [Group K] (g : G) :
    freeLampToSemidirect G Γ K (inAmbient G Γ K g)
      = SemidirectProduct.inl (inIterated G Γ K 1 g) :=
  PushoutI.lift_of _ _ _ _

@[simp] theorem freeLampToSemidirect_of_false (G : Type) [Group G]
    (Γ : Subgroup G) (K : Type) [Group K] (p : ↥Γ × K) :
    freeLampToSemidirect G Γ K (PushoutI.of (φ := lampMap G Γ K) false p)
      = ⟨PushoutI.base (iteratedMap G Γ K) p.1, p.2⟩ :=
  PushoutI.lift_of _ _ _ _

@[simp] theorem freeLampToSemidirect_inLamp (G : Type) [Group G]
    (Γ : Subgroup G) (K : Type) [Group K] (k : K) :
    freeLampToSemidirect G Γ K (inLamp G Γ K k) = SemidirectProduct.inr k := by
  rw [inLamp_apply, freeLampToSemidirect_of_false]
  apply SemidirectProduct.ext
  · show PushoutI.base (iteratedMap G Γ K) (1 : ↥Γ) = 1
    exact map_one _
  · rfl

theorem freeLampOfSemidirect_comp_toSemidirect (G : Type) [Group G]
    (Γ : Subgroup G) (K : Type) [Group K] :
    (freeLampOfSemidirect G Γ K).comp (freeLampToSemidirect G Γ K)
      = MonoidHom.id _ := by
  refine PushoutI.hom_ext_nonempty (fun b ↦ ?_)
  cases b
  · ext p
    show freeLampOfSemidirect G Γ K (freeLampToSemidirect G Γ K
        (PushoutI.of (φ := lampMap G Γ K) false p))
      = PushoutI.of (φ := lampMap G Γ K) false p
    rw [freeLampToSemidirect_of_false, SemidirectProduct.mk_eq_inl_mul_inr,
      map_mul, freeLampOfSemidirect_inl, freeLampOfSemidirect_inr,
      iteratedToFreeLamp_base, freeLamp_of_false_apply]
  · ext g
    show freeLampOfSemidirect G Γ K
        (freeLampToSemidirect G Γ K (inAmbient G Γ K g)) = inAmbient G Γ K g
    rw [freeLampToSemidirect_inAmbient, freeLampOfSemidirect_inl,
      iteratedToFreeLamp_inIterated]
    have h1 : inLamp G Γ K (1 : K) = 1 := map_one _
    rw [h1, one_mul, inv_one, mul_one]

theorem freeLampToSemidirect_comp_ofSemidirect (G : Type) [Group G]
    (Γ : Subgroup G) (K : Type) [Group K] :
    (freeLampToSemidirect G Γ K).comp (freeLampOfSemidirect G Γ K)
      = MonoidHom.id _ := by
  refine SemidirectProduct.hom_ext ?_ ?_
  · refine iteratedDouble_hom_ext G Γ (fun j x ↦ ?_) (fun γ ↦ ?_)
    · show freeLampToSemidirect G Γ K (freeLampOfSemidirect G Γ K
          (SemidirectProduct.inl (inIterated G Γ K j x)))
        = SemidirectProduct.inl (inIterated G Γ K j x)
      have haut := SemidirectProduct.inl_aut (φ := lampIndexAction G Γ K) j
        (inIterated G Γ K 1 x)
      rw [lampIndexAction_apply, lampShift_inIterated, mul_one] at haut
      rw [freeLampOfSemidirect_inl, iteratedToFreeLamp_inIterated, haut]
      simp only [map_mul, map_inv, freeLampToSemidirect_inLamp,
        freeLampToSemidirect_inAmbient]
    · show freeLampToSemidirect G Γ K (freeLampOfSemidirect G Γ K
          (SemidirectProduct.inl (PushoutI.base (iteratedMap G Γ K) γ)))
        = SemidirectProduct.inl (PushoutI.base (iteratedMap G Γ K) γ)
      rw [freeLampOfSemidirect_inl, iteratedToFreeLamp_base,
        freeLampToSemidirect_inAmbient, inIterated_coe_subgroup]
  · refine MonoidHom.ext fun k ↦ ?_
    show freeLampToSemidirect G Γ K (freeLampOfSemidirect G Γ K
        (SemidirectProduct.inr k)) = SemidirectProduct.inr k
    rw [freeLampOfSemidirect_inr, freeLampToSemidirect_inLamp]

/-- **The Bass--Serre splitting.**  The free-lamp amalgam is the semidirect
product of the `K`-fold amalgam of copies of `G` over `Γ` by the lamp group
acting on the vertex set by left translation. -/
def freeLampEquivSemidirect (G : Type) [Group G] (Γ : Subgroup G) (K : Type)
    [Group K] :
    FreeLamp G Γ K ≃* (IteratedDouble G Γ K) ⋊[lampIndexAction G Γ K] K where
  toFun := freeLampToSemidirect G Γ K
  invFun := freeLampOfSemidirect G Γ K
  left_inv x :=
    DFunLike.congr_fun (freeLampOfSemidirect_comp_toSemidirect G Γ K) x
  right_inv y :=
    DFunLike.congr_fun (freeLampToSemidirect_comp_ofSemidirect G Γ K) y
  map_mul' := (freeLampToSemidirect G Γ K).map_mul

/-! ## The kernel is the iterated amalgam -/

theorem freeLampToSemidirect_iteratedToFreeLamp (G : Type) [Group G]
    (Γ : Subgroup G) (K : Type) [Group K] (x : IteratedDouble G Γ K) :
    freeLampToSemidirect G Γ K (iteratedToFreeLamp G Γ K x)
      = SemidirectProduct.inl x := by
  have h := DFunLike.congr_fun (freeLampToSemidirect_comp_ofSemidirect G Γ K)
    (SemidirectProduct.inl x)
  rw [MonoidHom.comp_apply, freeLampOfSemidirect_inl] at h
  exact h

theorem iteratedToFreeLamp_injective (G : Type) [Group G] (Γ : Subgroup G)
    (K : Type) [Group K] :
    Function.Injective (iteratedToFreeLamp G Γ K) := by
  intro x y hxy
  have h : SemidirectProduct.inl (φ := lampIndexAction G Γ K) x
      = SemidirectProduct.inl y := by
    rw [← freeLampToSemidirect_iteratedToFreeLamp G Γ K x,
      ← freeLampToSemidirect_iteratedToFreeLamp G Γ K y, hxy]
  exact SemidirectProduct.inl_injective h

theorem lampRetraction_comp_iteratedToFreeLamp (G : Type) [Group G]
    (Γ : Subgroup G) (K : Type) [Group K] :
    (lampRetraction G Γ K).comp (iteratedToFreeLamp G Γ K)
      = (1 : IteratedDouble G Γ K →* K) := by
  refine iteratedDouble_hom_ext G Γ (fun j g ↦ ?_) (fun γ ↦ ?_)
  · show lampRetraction G Γ K
        (iteratedToFreeLamp G Γ K (inIterated G Γ K j g)) = 1
    rw [iteratedToFreeLamp_inIterated, map_mul, map_mul, map_inv,
      lampRetraction_inLamp, lampRetraction_inAmbient, mul_one, mul_inv_cancel]
  · show lampRetraction G Γ K (iteratedToFreeLamp G Γ K
        (PushoutI.base (iteratedMap G Γ K) γ)) = 1
    rw [iteratedToFreeLamp_base]
    exact lampRetraction_inAmbient G Γ K _

theorem lampRetraction_iteratedToFreeLamp (G : Type) [Group G] (Γ : Subgroup G)
    (K : Type) [Group K] (x : IteratedDouble G Γ K) :
    lampRetraction G Γ K (iteratedToFreeLamp G Γ K x) = 1 :=
  DFunLike.congr_fun (lampRetraction_comp_iteratedToFreeLamp G Γ K) x

theorem lampRetraction_comp_ofSemidirect (G : Type) [Group G] (Γ : Subgroup G)
    (K : Type) [Group K] :
    (lampRetraction G Γ K).comp (freeLampOfSemidirect G Γ K)
      = SemidirectProduct.rightHom := by
  refine SemidirectProduct.hom_ext ?_ ?_
  · refine MonoidHom.ext fun x ↦ ?_
    show lampRetraction G Γ K (freeLampOfSemidirect G Γ K
        (SemidirectProduct.inl (φ := lampIndexAction G Γ K) x))
      = SemidirectProduct.rightHom
          (SemidirectProduct.inl (φ := lampIndexAction G Γ K) x)
    rw [freeLampOfSemidirect_inl, lampRetraction_iteratedToFreeLamp,
      SemidirectProduct.rightHom_inl]
  · refine MonoidHom.ext fun k ↦ ?_
    show lampRetraction G Γ K (freeLampOfSemidirect G Γ K
        (SemidirectProduct.inr (φ := lampIndexAction G Γ K) k))
      = SemidirectProduct.rightHom
          (SemidirectProduct.inr (φ := lampIndexAction G Γ K) k)
    rw [freeLampOfSemidirect_inr, lampRetraction_inLamp,
      SemidirectProduct.rightHom_inr]

/-- **The covering identity.**  The kernel of the lamp retraction is exactly
the image of the `K`-fold amalgam:
`ker (G *_Γ (Γ × K) → K) = ⋆_{Γ, k ∈ K} G`. -/
theorem range_iteratedToFreeLamp (G : Type) [Group G] (Γ : Subgroup G)
    (K : Type) [Group K] :
    (iteratedToFreeLamp G Γ K).range = lampKernel G Γ K := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
    exact MonoidHom.mem_ker.mpr (lampRetraction_iteratedToFreeLamp G Γ K x)
  · intro x hx
    have hxker : lampRetraction G Γ K x = 1 := MonoidHom.mem_ker.mp hx
    have hxy : freeLampOfSemidirect G Γ K (freeLampToSemidirect G Γ K x) = x :=
      DFunLike.congr_fun (freeLampOfSemidirect_comp_toSemidirect G Γ K) x
    have hright : (freeLampToSemidirect G Γ K x).right = 1 := by
      have h := DFunLike.congr_fun (lampRetraction_comp_ofSemidirect G Γ K)
        (freeLampToSemidirect G Γ K x)
      rw [MonoidHom.comp_apply, hxy, hxker] at h
      exact h.symm
    have hsplit : SemidirectProduct.inl (φ := lampIndexAction G Γ K)
        (freeLampToSemidirect G Γ K x).left
        = freeLampToSemidirect G Γ K x := by
      apply SemidirectProduct.ext
      · rfl
      · show (1 : K) = (freeLampToSemidirect G Γ K x).right
        rw [hright]
    refine MonoidHom.mem_range.mpr ⟨(freeLampToSemidirect G Γ K x).left, ?_⟩
    calc iteratedToFreeLamp G Γ K (freeLampToSemidirect G Γ K x).left
        = freeLampOfSemidirect G Γ K (SemidirectProduct.inl
            (freeLampToSemidirect G Γ K x).left) :=
          (freeLampOfSemidirect_inl G Γ K _).symm
      _ = freeLampOfSemidirect G Γ K (freeLampToSemidirect G Γ K x) := by
          rw [hsplit]
      _ = x := hxy

/-- The kernel of the lamp retraction, as a group, *is* the `K`-fold
amalgam. -/
noncomputable def iteratedEquivLampKernel (G : Type) [Group G] (Γ : Subgroup G)
    (K : Type) [Group K] :
    IteratedDouble G Γ K ≃* ↥(lampKernel G Γ K) :=
  MulEquiv.ofBijective
    ((iteratedToFreeLamp G Γ K).codRestrict (lampKernel G Γ K)
      (fun x ↦ MonoidHom.mem_ker.mpr
        (lampRetraction_iteratedToFreeLamp G Γ K x)))
    ⟨fun x y hxy ↦
        iteratedToFreeLamp_injective G Γ K (Subtype.ext_iff.mp hxy),
      by
        rintro ⟨x, hx⟩
        have hmem : x ∈ (iteratedToFreeLamp G Γ K).range := by
          rw [range_iteratedToFreeLamp]
          exact hx
        obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hmem
        exact ⟨y, Subtype.ext hy⟩⟩

/-! ## The two permanence consequences -/

/-- **Operator-MF passes from the covering to the amalgam.**  This is the whole
non-literature half of the MF side of the Kun--Thom/Shulman construction: given
that the `|K|`-fold amalgam of copies of `G` over `Γ` is operator-MF -- which is
what a symmetric amalgamation theorem supplies -- the free-lamp amalgam is
operator-MF, by induction of corona representations over a subgroup of index
`|K|`. -/
theorem isOperatorMF_freeLamp_of_isOperatorMF_iterated (G : Type) [Group G]
    (Γ : Subgroup G) (K : Type) [Group K] [Finite K]
    (h : IsOperatorMF (IteratedDouble G Γ K)) : IsOperatorMF (FreeLamp G Γ K) :=
  InducedCorona.isOperatorMF_of_finiteIndex_subgroup (lampKernel G Γ K)
    (CommensurabilityInvariance.isOperatorMF_of_mulEquiv
      (iteratedEquivLampKernel G Γ K) h)

/-- Operator-MF descends from the amalgam to the covering, since the covering
embeds. -/
theorem isOperatorMF_iterated_of_isOperatorMF_freeLamp (G : Type) [Group G]
    (Γ : Subgroup G) (K : Type) [Group K]
    (h : IsOperatorMF (FreeLamp G Γ K)) : IsOperatorMF (IteratedDouble G Γ K) :=
  h.comap (iteratedToFreeLamp G Γ K) (iteratedToFreeLamp_injective G Γ K)

/-- Soficity passes from the covering to the amalgam. -/
theorem isSofic_freeLamp_of_isSofic_iterated (G : Type) [Group G]
    (Γ : Subgroup G) (K : Type) [Group K] [Finite K]
    (h : IsSofic (IteratedDouble G Γ K)) : IsSofic (FreeLamp G Γ K) :=
  (isSofic_mulEquiv_iff (freeLampEquivSemidirect G Γ K)).mpr
    (isSofic_semidirectProduct_of_finite (lampIndexAction G Γ K) h)

/-- Soficity descends from the amalgam to the covering. -/
theorem isSofic_iterated_of_isSofic_freeLamp (G : Type) [Group G]
    (Γ : Subgroup G) (K : Type) [Group K]
    (h : IsSofic (FreeLamp G Γ K)) : IsSofic (IteratedDouble G Γ K) :=
  isSofic_of_injective (iteratedToFreeLamp G Γ K)
    (iteratedToFreeLamp_injective G Γ K) h

/-- A nonsofic free-lamp amalgam forces its covering to be nonsofic. -/
theorem not_isSofic_iterated_of_not_isSofic_freeLamp (G : Type) [Group G]
    (Γ : Subgroup G) (K : Type) [Group K] [Finite K]
    (h : ¬ IsSofic (FreeLamp G Γ K)) : ¬ IsSofic (IteratedDouble G Γ K) :=
  fun hiter ↦ h (isSofic_freeLamp_of_isSofic_iterated G Γ K hiter)

end GroupApproximation
