import GroupApproximation.BooneHigman.Metabelian.ElemFPK2DilateStStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Pullback excision: the degenerate localizations

Lane `bh-met-90z`, first module.  Notation of `ElemFPK2DilateStRing`: `L = A_s`,
`λ : A → L`, `P = A ×_L L[X]` (`k2DilateSt_pullback s`) and `ι_0 : A[X] → P`,
`f ↦ (f(0), λ f)` (`k2DilateSt_toPullback s 0`).  The residual `k2DilateSt_PullbackDiesAt s`
asks: for `g ∈ K₂(N, A[X])` with `g(0) = 1` whose image over `L[X]` dies after padding, the
image `ι_0 g ∈ St(P)` dies after padding.  Here it is proved outright when the localization
degenerates.

* `s` nilpotent (in particular `s = 0`): `L = 0`, so `ι_0 = ι_0 ∘ C ∘ ev_0`
  (`k2PullExc_toPullback_zero_eq_of_subsingleton`), and `ι_0 g = ι_0(C(g(0))) = 1`.
  Only `g(0) = 1` is used.
* `s` a unit: `λ` is the isomorphism `IsLocalization.atUnit`, and
  `j : L[X] → P`, `h ↦ (λ⁻¹(h(0)), h)` satisfies `ι_0 = j ∘ λ`
  (`k2PullExc_toPullback_zero_eq_of_isUnit`).  So `ι_0 g = j(λ g)` dies with `λ g`.
* Infrastructure for the domain case: if `λ` is injective, then the second projection
  `P → L[X]` is injective (`k2PullExc_snd_injective`), i.e. `P` is the conductor subring
  `{h ∈ L[X] : h(0) ∈ λ(A)}` of `L[X]`.

Everything is ring theory plus functoriality of `St(N, -)`.  No citation is a hypothesis.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

section PullExcDegenerate

variable {A : Type*} [CommRing A]

/-- If `A_s = 0`, then `ι_0 = ι_0 ∘ C ∘ ev_0`: the first component of `ι_0 f` is `f(0)`, and
the second lives in the zero ring `L[X]`. -/
theorem k2PullExc_toPullback_zero_eq_of_subsingleton (s : A)
    [Subsingleton (Localization.Away s)] :
    k2DilateSt_toPullback s 0 =
      ((k2DilateSt_toPullback s 0).comp Polynomial.C).comp (Polynomial.evalRingHom 0) :=
  RingHom.ext fun f ↦ Subtype.ext (Prod.ext
    (by
      change f.eval 0 = (Polynomial.C ((Polynomial.evalRingHom (0 : A)) f)).eval 0
      rw [Polynomial.eval_C, Polynomial.coe_evalRingHom])
    (Subsingleton.elim _ _))

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullExc_toPullback_zero_eq_of_subsingleton

/-- **Trivial localization**: if `A_s = 0`, the pullback residual holds at `s`. -/
theorem k2PullExc_pullbackDiesAt_of_subsingleton (s : A) [Subsingleton (Localization.Away s)] :
    k2DilateSt_PullbackDiesAt s := by
  intro N _ g _ hev _
  rw [k2PullExc_toPullback_zero_eq_of_subsingleton s, ← SteinbergBasic.ringMap_ringMap, hev,
    map_one]
  exact cubeDiagDilate_stDies_one

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullExc_pullbackDiesAt_of_subsingleton

/-- The localization at a nilpotent element is the zero ring. -/
theorem k2PullExc_subsingleton_of_isNilpotent {s : A} (hs : IsNilpotent s) :
    Subsingleton (Localization.Away s) :=
  IsLocalization.subsingleton ((Submonoid.mem_powers_iff 0 s).2 hs)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullExc_subsingleton_of_isNilpotent

/-- **Nilpotent case**: the pullback residual holds at every nilpotent `s`. -/
theorem k2PullExc_pullbackDiesAt_of_isNilpotent {s : A} (hs : IsNilpotent s) :
    k2DilateSt_PullbackDiesAt s := by
  haveI := k2PullExc_subsingleton_of_isNilpotent hs
  exact k2PullExc_pullbackDiesAt_of_subsingleton s

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullExc_pullbackDiesAt_of_isNilpotent

/-- **Zero case**: the pullback residual holds at `s = 0`. -/
theorem k2PullExc_pullbackDiesAt_zero : k2DilateSt_PullbackDiesAt (0 : A) :=
  k2PullExc_pullbackDiesAt_of_isNilpotent IsNilpotent.zero

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullExc_pullbackDiesAt_zero

/-- At a unit `s`, the isomorphism `A ≅ A_s` of `IsLocalization.atUnit` is `λ`. -/
theorem k2PullExc_atUnit_apply {s : A} (hs : IsUnit s) (a : A) :
    IsLocalization.atUnit A (Localization.Away s) s hs a =
      algebraMap A (Localization.Away s) a :=
  (IsLocalization.atUnit A (Localization.Away s) s hs).commutes a

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullExc_atUnit_apply

/-- At a unit `s`, the section `j : L[X] → P`, `h ↦ (λ⁻¹(h(0)), h)`. -/
noncomputable def k2PullExc_unitSection {s : A} (hs : IsUnit s) :
    Polynomial (Localization.Away s) →+* k2DilateSt_pullback s :=
  (RingHom.prod
      ((IsLocalization.atUnit A (Localization.Away s) s hs).symm.toRingEquiv.toRingHom.comp
        (Polynomial.evalRingHom 0))
      (RingHom.id (Polynomial (Localization.Away s)))).codRestrict (k2DilateSt_pullback s)
    fun h ↦ by
      change algebraMap A (Localization.Away s)
          ((IsLocalization.atUnit A (Localization.Away s) s hs).symm (h.eval 0)) = h.eval 0
      rw [← k2PullExc_atUnit_apply hs, AlgEquiv.apply_symm_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullExc_unitSection

/-- At a unit `s`, `ι_0 = j ∘ λ`. -/
theorem k2PullExc_toPullback_zero_eq_of_isUnit {s : A} (hs : IsUnit s) :
    k2DilateSt_toPullback s 0 =
      (k2PullExc_unitSection hs).comp
        (Polynomial.mapRingHom (algebraMap A (Localization.Away s))) :=
  RingHom.ext fun f ↦ Subtype.ext (Prod.ext
    (by
      change f.eval 0 = (IsLocalization.atUnit A (Localization.Away s) s hs).symm
        ((f.map (algebraMap A (Localization.Away s))).eval 0)
      rw [Polynomial.eval_zero_map, ← k2PullExc_atUnit_apply hs, AlgEquiv.symm_apply_apply])
    (by
      change k2CubeDilate_scale (Localization.Away s) (k2DilateSt_inv s ^ 0)
          (f.map (algebraMap A (Localization.Away s))) =
        f.map (algebraMap A (Localization.Away s))
      rw [pow_zero, k2CubeDilate_scale_one, RingHom.id_apply]))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullExc_toPullback_zero_eq_of_isUnit

/-- **Unit case**: the pullback residual holds at every unit `s`. -/
theorem k2PullExc_pullbackDiesAt_of_isUnit {s : A} (hs : IsUnit s) :
    k2DilateSt_PullbackDiesAt s := by
  intro N _ g _ _ hloc
  rw [k2PullExc_toPullback_zero_eq_of_isUnit hs, ← SteinbergBasic.ringMap_ringMap]
  exact cubeDiagDilate_stDies_ringMap _ hloc

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullExc_pullbackDiesAt_of_isUnit

/-- **Domain-case infrastructure**: if `λ : A → A_s` is injective, the second projection
`P → A_s[X]` is injective, so `P` is the conductor subring `{h : h(0) ∈ λ(A)}`. -/
theorem k2PullExc_snd_injective {s : A}
    (hs : Function.Injective (algebraMap A (Localization.Away s))) :
    Function.Injective ((RingHom.snd A (Polynomial (Localization.Away s))).comp
      (k2DilateSt_pullback s).subtype) := by
  intro q₁ q₂ h
  have h₂ : (q₁ : A × Polynomial (Localization.Away s)).2 =
      (q₂ : A × Polynomial (Localization.Away s)).2 := h
  refine Subtype.ext (Prod.ext (hs ?_) h₂)
  rw [(k2DilateSt_mem_pullback s _).1 q₁.property, (k2DilateSt_mem_pullback s _).1 q₂.property,
    h₂]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullExc_snd_injective

end PullExcDegenerate

end GroupApproximation.BooneHigman.Metabelian.ElemFP
