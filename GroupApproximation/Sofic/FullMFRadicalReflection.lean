import GroupApproximation.Sofic.FullMFRadicalExactness
import GroupApproximation.Sofic.UniversalVisibleQuotient

/-!
# The core-free reflection of a group

Quotienting by the intrinsic full-MF core is universal among homomorphisms to
groups with trivial intrinsic core.  The construction is functorial: every
group homomorphism induces a homomorphism between the corresponding core-free
quotients, and these induced maps preserve identities and composition.
-/

namespace GroupApproximation

universe u v w

variable {G : Type u} [Group G]

/-- The canonical core-free quotient of a group. -/
abbrev fullMFRadicalCoreQuotient (G : Type u) [Group G] :=
  G ⧸ fullMFRadicalCore G

/-- The quotient map to the core-free quotient. -/
def fullMFRadicalCoreQuotientMk (G : Type u) [Group G] :
    G →* fullMFRadicalCoreQuotient G :=
  QuotientGroup.mk' (fullMFRadicalCore G)

@[simp]
theorem fullMFRadicalCoreQuotientMk_apply (g : G) :
    fullMFRadicalCoreQuotientMk G g = QuotientGroup.mk g :=
  rfl

/-- Every homomorphism induces a homomorphism between the core-free
quotients. -/
def fullMFRadicalCoreQuotientMap
    {H : Type v} [Group H] (f : G →* H) :
    fullMFRadicalCoreQuotient G →* fullMFRadicalCoreQuotient H :=
  QuotientGroup.lift (fullMFRadicalCore G)
    ((fullMFRadicalCoreQuotientMk H).comp f) (by
      intro x hx
      rw [MonoidHom.mem_ker]
      apply (QuotientGroup.eq_one_iff (f x)).mpr
      exact map_fullMFRadicalCore_le f
        (Subgroup.mem_map_of_mem f hx))

@[simp]
theorem fullMFRadicalCoreQuotientMap_mk
    {H : Type v} [Group H] (f : G →* H) (g : G) :
    fullMFRadicalCoreQuotientMap f (fullMFRadicalCoreQuotientMk G g) =
      fullMFRadicalCoreQuotientMk H (f g) :=
  rfl

/-- The quotient construction preserves identity homomorphisms. -/
theorem fullMFRadicalCoreQuotientMap_id :
    fullMFRadicalCoreQuotientMap (MonoidHom.id G) =
      MonoidHom.id (fullMFRadicalCoreQuotient G) := by
  apply comp_mk'_injective (fullMFRadicalCore G)
  ext g
  rfl

/-- The quotient construction preserves composition. -/
theorem fullMFRadicalCoreQuotientMap_comp
    {H : Type v} [Group H] {K : Type w} [Group K]
    (g : H →* K) (f : G →* H) :
    fullMFRadicalCoreQuotientMap (g.comp f) =
      (fullMFRadicalCoreQuotientMap g).comp
        (fullMFRadicalCoreQuotientMap f) := by
  apply comp_mk'_injective (fullMFRadicalCore G)
  ext x
  rfl

/-- The canonical quotient is core-free. -/
theorem fullMFRadicalCoreQuotient_core_eq_bot :
    fullMFRadicalCore (fullMFRadicalCoreQuotient G) = ⊥ :=
  fullMFRadicalCore_quotient_eq_bot

/-- Precomposition with the core quotient is a bijection on homomorphisms to
every core-free group. -/
theorem fullMFRadicalCoreQuotient_hom_bijective
    {H : Type v} [Group H] (hH : fullMFRadicalCore H = ⊥) :
    Function.Bijective
      (fun F : fullMFRadicalCoreQuotient G →* H =>
        F.comp (fullMFRadicalCoreQuotientMk G)) :=
  comp_mk'_bijective (fullMFRadicalCore G)
    (fun f => fullMFRadicalCore_le_ker_of_target_eq_bot f hH)

/-- Every homomorphism to a core-free group factors uniquely through the
canonical core-free quotient. -/
theorem existsUnique_fullMFRadicalCoreQuotient_factorization
    {H : Type v} [Group H] (f : G →* H)
    (hH : fullMFRadicalCore H = ⊥) :
    ∃! fBar : fullMFRadicalCoreQuotient G →* H,
      fBar.comp (fullMFRadicalCoreQuotientMk G) = f := by
  have hbij := fullMFRadicalCoreQuotient_hom_bijective (G := G) hH
  obtain ⟨fBar, hfBar⟩ := hbij.2 f
  refine ⟨fBar, hfBar, ?_⟩
  intro k hk
  exact hbij.1 (hk.trans hfBar.symm)

end GroupApproximation
