import GroupApproximation.Analysis.AmenableExtensionAmenableTrace

/-!
# The semidirect-product-by-`ℤ` statement as an instance

`non_mf_groups_exist.tex`, Proposition `prop:locally-rf-by-z-trace`.  Before it
was generalized to arbitrary amenable quotients, the proposition was the
`⋊ ℤ` statement carried by
`Analysis.LocallyRFByIntFactorization.canonicalMaximalTrace_isAmenableTrace_of_locallyRFByInt`.
This module derives that statement from the general one, so the older module is
subsumed rather than merely coexisting with the new one.

Two steps, both bookkeeping:

* `isLocallyResiduallyFinite_of_mulEquiv` --- local residual finiteness is an
  isomorphism invariant.  A finitely generated subgroup of the target pulls
  back to a finitely generated subgroup of the source, and residual finiteness
  of the subgroups transfers by `Sofic.residuallyFinite_of_mulEquiv`.
* `ker_eq_range_kernelEmbedding` --- for `G ≃ N ⋊[α] ℤ` the kernel of the
  composite `G → ℤ` is exactly the copy of `N` inside `G`, so the general
  proposition applies with that kernel and the amenable quotient `ℤ`
  (`SoficByAmenablePermanence.isAmenable_int`).

The general statement is strictly stronger: it asks nothing about how the
extension splits, and nothing about the quotient beyond amenability.
-/

namespace GroupApproximation
namespace AmenableExtensionTrace

open Quasidiagonal
open LocallyRFByIntAmenableTrace SoficByAmenablePermanence

noncomputable section

/-! ### Local residual finiteness is an isomorphism invariant -/

theorem isLocallyResiduallyFinite_of_mulEquiv {X Y : Type} [Group X] [Group Y]
    (f : X ≃* Y) (hX : IsLocallyResiduallyFinite X) :
    IsLocallyResiduallyFinite Y := by
  classical
  intro H hH
  have hfg : (H.map f.symm.toMonoidHom).FG := by
    obtain ⟨S, hS⟩ := hH
    refine ⟨S.image f.symm.toMonoidHom, ?_⟩
    rw [Finset.coe_image, ← MonoidHom.map_closure, hS]
  haveI : Group.ResiduallyFinite ↥(H.map f.symm.toMonoidHom) :=
    hX (H.map f.symm.toMonoidHom) hfg
  have hcomp : f.toMonoidHom.comp f.symm.toMonoidHom = MonoidHom.id Y := by
    ext y
    simp
  have hmap : (H.map f.symm.toMonoidHom).map f.toMonoidHom = H := by
    rw [Subgroup.map_map, hcomp, Subgroup.map_id]
  exact residuallyFinite_of_mulEquiv
    (((Subgroup.equivMapOfInjective (H.map f.symm.toMonoidHom) f.toMonoidHom
      f.injective).trans (MulEquiv.subgroupCongr hmap)).symm)

/-! ### The `ℤ`-quotient form -/

/-- **The general proposition at an integer quotient.**  Compare
`SoficByAmenablePermanence.isSofic_of_isSofic_of_int_quotient`, the same shape
for soficity. -/
theorem canonicalMaximalTrace_isAmenableTrace_of_int_quotient
    (G : Type) [Group G] [Countable G] (M : Subgroup G) [M.Normal]
    (hM : IsLocallyResiduallyFinite ↥M) (h : G ⧸ M ≃* Multiplicative ℤ) :
    IsAmenableTrace (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a) :=
  manuscriptPrintedAmenableExtensionCanonicalTraceAmenable G M hM
    (isAmenable_of_mulEquiv h isAmenable_int)

/-! ### The semidirect-product form -/

/-- The composite `G → N ⋊ ℤ → ℤ`. -/
def levelHom {G N : Type} [Group G] [Group N]
    (α : Multiplicative ℤ →* MulAut N)
    (e : G ≃* (N ⋊[α] Multiplicative ℤ)) : G →* Multiplicative ℤ :=
  (SemidirectProduct.rightHom).comp e.toMonoidHom

theorem levelHom_surjective {G N : Type} [Group G] [Group N]
    (α : Multiplicative ℤ →* MulAut N)
    (e : G ≃* (N ⋊[α] Multiplicative ℤ)) :
    Function.Surjective (levelHom α e) :=
  SemidirectProduct.rightHom_surjective.comp e.surjective

/-- The kernel of the level homomorphism is the copy of `N` inside `G`. -/
theorem ker_eq_range_kernelEmbedding {G N : Type} [Group G] [Group N]
    (α : Multiplicative ℤ →* MulAut N)
    (e : G ≃* (N ⋊[α] Multiplicative ℤ)) :
    (kernelEmbedding α e).range = (levelHom α e).ker := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    show SemidirectProduct.rightHom (e (kernelEmbedding α e x)) = 1
    simp [kernelEmbedding]
  · intro hg
    have hg' : SemidirectProduct.rightHom (e g) = 1 := hg
    refine ⟨(e g).left, ?_⟩
    show e.symm (SemidirectProduct.inl (e g).left) = g
    have hstep : (SemidirectProduct.inl (e g).left :
        N ⋊[α] Multiplicative ℤ) = e g := by
      apply SemidirectProduct.ext
      · rfl
      · simpa using hg'.symm
    rw [hstep, e.symm_apply_apply]

/-- **The old `⋊ ℤ` proposition, as an instance of the general one.**  This is
the statement of
`LocallyRFByIntFactorization.canonicalMaximalTrace_isAmenableTrace_of_locallyRFByInt`,
derived from the amenable-extension form rather than from the cyclic-window
construction. -/
theorem canonicalMaximalTrace_isAmenableTrace_of_locallyRFByInt
    {G N : Type} [Group G] [Group N] [Countable G]
    (α : Multiplicative ℤ →* MulAut N)
    (e : G ≃* (N ⋊[α] Multiplicative ℤ))
    (hN : IsLocallyResiduallyFinite N) :
    IsAmenableTrace (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a) := by
  haveI hnormal : ((levelHom α e).ker).Normal := (levelHom α e).normal_ker
  have hequiv : N ≃* ↥((levelHom α e).ker) :=
    (MonoidHom.ofInjective (kernelEmbedding_injective α e)).trans
      (MulEquiv.subgroupCongr (ker_eq_range_kernelEmbedding α e))
  have hquot : (G ⧸ (levelHom α e).ker) ≃* Multiplicative ℤ :=
    QuotientGroup.quotientKerEquivOfSurjective (levelHom α e)
      (levelHom_surjective α e)
  exact canonicalMaximalTrace_isAmenableTrace_of_int_quotient G
    ((levelHom α e).ker)
    (isLocallyResiduallyFinite_of_mulEquiv hequiv hN) hquot

end

end AmenableExtensionTrace
end GroupApproximation
