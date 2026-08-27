import GroupApproximation.Sofic.NormMFResidualDetector

/-!
# The universal quotient detected by norm-matrix ultraproducts

The operator-norm MF residual is the common kernel, element by element, of
all homomorphisms from a group to operator-norm matrix ultraproducts.  This
file packages the corresponding universal quotient.

Every homomorphism to an operator-norm matrix ultraproduct factors uniquely
through `normMFQuotient G`.  More generally, the same is true for every
target whose norm-MF residual is trivial.  The quotient itself has trivial
norm-MF residual: every one of its nonidentity elements is detected by some
operator-norm matrix ultraproduct representation.  Consequently it is the
largest quotient of `G` with this pointwise detection property.

This file alone does **not** assert `IsWeakMF (normMFQuotient G)`: passing
from pointwise detection, potentially using a different ultraproduct for
every nonidentity element, to one simultaneous matrix model requires a
diagonal block-amplification construction.  That construction, and the
resulting standard cofinite-corona MF theorem, are supplied downstream in
`NormMFUniversalCorona`; no such result is assumed in the proofs here.
-/

namespace GroupApproximation

universe u v

variable {G : Type u} [Group G]

/-! ## Definition and the canonical map -/

/-- The universal quotient of `G` detected by operator-norm matrix
ultraproducts. -/
abbrev normMFQuotient (G : Type u) [Group G] :=
  G ⧸ normMFResidual G

/-- The canonical map to the norm-MF universal quotient. -/
def normMFQuotientMk (G : Type u) [Group G] : G →* normMFQuotient G :=
  QuotientGroup.mk' (normMFResidual G)

@[simp]
theorem normMFQuotientMk_apply (g : G) :
    normMFQuotientMk G g = QuotientGroup.mk g :=
  rfl

@[simp]
theorem normMFQuotientMk_ker :
    (normMFQuotientMk G).ker = normMFResidual G :=
  QuotientGroup.ker_mk' (normMFResidual G)

/-- The norm-MF residual lies in the kernel of every representation into an
operator-norm matrix ultraproduct. -/
theorem normMFResidual_le_ultraproduct_ker
    {I : Type} (U : Ultrafilter I) (X : I → FiniteModel)
    (rho : G →* UniversalWeakMF U X) :
    normMFResidual G ≤ rho.ker := by
  intro g hg
  exact MonoidHom.mem_ker.mpr
    (map_eq_one_of_mem_normMFResidual U X rho hg)

/-! ## Universal factorization into matrix ultraproducts -/

/-- The canonical factor of an operator-norm matrix-ultraproduct
representation through the norm-MF quotient. -/
def normMFQuotientLift
    {I : Type} (U : Ultrafilter I) (X : I → FiniteModel)
    (rho : G →* UniversalWeakMF U X) :
    normMFQuotient G →* UniversalWeakMF U X :=
  QuotientGroup.lift (normMFResidual G) rho
    (normMFResidual_le_ultraproduct_ker U X rho)

@[simp]
theorem normMFQuotientLift_mk
    {I : Type} (U : Ultrafilter I) (X : I → FiniteModel)
    (rho : G →* UniversalWeakMF U X) (g : G) :
    normMFQuotientLift U X rho (normMFQuotientMk G g) = rho g :=
  rfl

@[simp]
theorem normMFQuotientLift_comp_mk
    {I : Type} (U : Ultrafilter I) (X : I → FiniteModel)
    (rho : G →* UniversalWeakMF U X) :
    (normMFQuotientLift U X rho).comp (normMFQuotientMk G) = rho :=
  rfl

/-- Homomorphisms out of the norm-MF quotient are determined by their
composites with its canonical quotient map. -/
theorem normMFQuotient_hom_ext {H : Type v} [Group H]
    {f k : normMFQuotient G →* H}
    (h : f.comp (normMFQuotientMk G) =
      k.comp (normMFQuotientMk G)) :
    f = k := by
  apply MonoidHom.ext
  intro q
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective
    (normMFResidual G) q
  rw [← hg]
  exact DFunLike.congr_fun h g

/-- Universal mapping property for operator-norm matrix ultraproducts:
every representation factors uniquely through the norm-MF quotient. -/
theorem existsUnique_normMFQuotient_factorization
    {I : Type} (U : Ultrafilter I) (X : I → FiniteModel)
    (rho : G →* UniversalWeakMF U X) :
    ∃! rhoBar : normMFQuotient G →* UniversalWeakMF U X,
      rhoBar.comp (normMFQuotientMk G) = rho := by
  refine ⟨normMFQuotientLift U X rho,
    normMFQuotientLift_comp_mk U X rho, ?_⟩
  intro k hk
  exact normMFQuotient_hom_ext
    (hk.trans (normMFQuotientLift_comp_mk U X rho).symm)

/-! ## Pointwise detection and triviality of the quotient residual -/

/-- Every nonidentity element of the universal quotient survives in some
operator-norm matrix ultraproduct.  The target is allowed to depend on the
element; this is the exact content of quotienting by the common kernel. -/
theorem exists_ultraproduct_detector_of_ne_one
    {q : normMFQuotient G} (hq : q ≠ 1) :
    ∃ (I : Type) (U : Ultrafilter I) (X : I → FiniteModel)
      (rho : normMFQuotient G →* UniversalWeakMF U X),
      rho q ≠ 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    (normMFResidual G) q
  have hg : g ∉ normMFResidual G := by
    intro hg
    apply hq
    exact (QuotientGroup.eq_one_iff g).2 hg
  rw [mem_normMFResidual_iff] at hg
  unfold NormMFInvisible at hg
  push Not at hg
  obtain ⟨I, U, X, rho, hrho⟩ := hg
  refine ⟨I, U, X, normMFQuotientLift U X rho, ?_⟩
  change normMFQuotientLift U X rho (normMFQuotientMk G g) ≠ 1
  rw [normMFQuotientLift_mk]
  exact hrho

/-- The universal quotient is residually detected by norm-matrix
ultraproducts: its norm-MF residual is trivial. -/
theorem normMFResidual_normMFQuotient_eq_bot :
    normMFResidual (normMFQuotient G) = ⊥ := by
  apply Subgroup.eq_bot_iff_forall (normMFResidual (normMFQuotient G)) |>.2
  intro q hq
  by_contra hne
  obtain ⟨I, U, X, rho, hrho⟩ :=
    exists_ultraproduct_detector_of_ne_one hne
  exact hrho (map_eq_one_of_mem_normMFResidual U X rho hq)

/-! ## Universal factorization into every residually detected group -/

/-- Any homomorphism into a group with trivial norm-MF residual kills the
source residual. -/
theorem normMFResidual_le_ker_of_target_residual_eq_bot
    {H : Type v} [Group H] (f : G →* H)
    (hH : normMFResidual H = ⊥) :
    normMFResidual G ≤ f.ker := by
  intro g hg
  have hfg : f g ∈ normMFResidual H :=
    mem_normMFResidual_iff.mpr
      ((mem_normMFResidual_iff.mp hg).map f)
  rw [hH] at hfg
  exact MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp hfg)

/-- The factor through the norm-MF quotient of a homomorphism into any
group with trivial norm-MF residual. -/
def normMFQuotientLiftToResidualFree
    {H : Type v} [Group H] (f : G →* H)
    (hH : normMFResidual H = ⊥) :
    normMFQuotient G →* H :=
  QuotientGroup.lift (normMFResidual G) f
    (normMFResidual_le_ker_of_target_residual_eq_bot f hH)

@[simp]
theorem normMFQuotientLiftToResidualFree_mk
    {H : Type v} [Group H] (f : G →* H)
    (hH : normMFResidual H = ⊥) (g : G) :
    normMFQuotientLiftToResidualFree f hH (normMFQuotientMk G g) = f g :=
  rfl

/-- Universal mapping property among groups with trivial norm-MF residual. -/
theorem existsUnique_normMFQuotient_factorization_of_residual_eq_bot
    {H : Type v} [Group H] (f : G →* H)
    (hH : normMFResidual H = ⊥) :
    ∃! fBar : normMFQuotient G →* H,
      fBar.comp (normMFQuotientMk G) = f := by
  refine ⟨normMFQuotientLiftToResidualFree f hH,
    QuotientGroup.lift_comp_mk' (normMFResidual G) f
      (normMFResidual_le_ker_of_target_residual_eq_bot f hH), ?_⟩
  intro k hk
  exact normMFQuotient_hom_ext
    (hk.trans (QuotientGroup.lift_comp_mk' (normMFResidual G) f
      (normMFResidual_le_ker_of_target_residual_eq_bot f hH)).symm)

/-! ## Largest residually detected quotient -/

/-- If `G/N` has trivial norm-MF residual, then the norm-MF residual of `G`
is contained in `N`.  Thus `normMFQuotient G` maps canonically onto every
quotient of `G` having the pointwise ultraproduct-detection property. -/
theorem normMFResidual_le_of_quotient_residual_eq_bot
    (N : Subgroup G) [N.Normal]
    (hN : normMFResidual (G ⧸ N) = ⊥) :
    normMFResidual G ≤ N := by
  have hker := normMFResidual_le_ker_of_target_residual_eq_bot
    (QuotientGroup.mk' N) hN
  simpa using hker

/-- The canonical map from the norm-MF universal quotient to any quotient
with trivial norm-MF residual. -/
def normMFQuotientToResidualFreeQuotient
    (N : Subgroup G) [N.Normal]
    (hN : normMFResidual (G ⧸ N) = ⊥) :
    normMFQuotient G →* G ⧸ N :=
  normMFQuotientLiftToResidualFree (QuotientGroup.mk' N) hN

@[simp]
theorem normMFQuotientToResidualFreeQuotient_mk
    (N : Subgroup G) [N.Normal]
    (hN : normMFResidual (G ⧸ N) = ⊥) (g : G) :
    normMFQuotientToResidualFreeQuotient N hN
        (normMFQuotientMk G g) = QuotientGroup.mk' N g :=
  rfl

/-- The canonical map to a residually detected quotient is surjective. -/
theorem normMFQuotientToResidualFreeQuotient_surjective
    (N : Subgroup G) [N.Normal]
    (hN : normMFResidual (G ⧸ N) = ⊥) :
    Function.Surjective (normMFQuotientToResidualFreeQuotient N hN) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
  exact ⟨normMFQuotientMk G g, rfl⟩

end GroupApproximation
