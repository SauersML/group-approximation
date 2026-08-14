import GroupApproximation.Domination.PresentationRadical
import GroupApproximation.Sofic.NormMFCoronaRadical
import GroupApproximation.Sofic.NormMFResidualFunctorial

/-!
# Separating the MF, hyperlinear, and sofic radicals

This file records the semantic kernel logic used by the literal non-MF
example.  A homomorphism into a hyperlinear target which detects `x` proves
that `x` is not in the hyperlinear radical.  If `x` is nevertheless invisible
to every norm-matrix-corona representation, the MF radical is not contained in
the hyperlinear radical.

The theorem is deliberately independent of the analytic construction of the
detecting representation.  The finite coset-tower/CAR dilation supplying that
representation for the printed group is paper-level operator algebra.
-/

namespace GroupApproximation

universe u

variable {G H : Type u} [Group G] [Group H]

/-- The elements killed by every homomorphism to a hyperlinear group form the
hyperlinear residual. -/
def hyperlinearResidual (G : Type u) [Group G] : Subgroup G where
  carrier := {x | HyperlinearInvisible x}
  one_mem' := by
    intro H _ _ rho
    exact map_one rho
  mul_mem' := by
    intro x y hx hy H _ hH rho
    rw [map_mul, hx H inferInstance hH rho, hy H inferInstance hH rho, one_mul]
  inv_mem' := by
    intro x hx H _ hH rho
    rw [map_inv, hx H inferInstance hH rho, inv_one]

@[simp] theorem mem_hyperlinearResidual_iff {x : G} :
    x ∈ hyperlinearResidual G ↔ HyperlinearInvisible x :=
  Iff.rfl

/-- Every hyperlinear-invisible element is sofic-invisible because every
sofic group is hyperlinear. -/
theorem hyperlinearResidual_le_soficResidual :
    hyperlinearResidual G ≤ soficResidual G := by
  intro x hx
  exact soficInvisible_of_hyperlinearInvisible hx

/-- Hyperlinear invisibility is portable along arbitrary homomorphisms. -/
theorem HyperlinearInvisible.map {x : G} (hx : HyperlinearInvisible x)
    (f : G →* H) : HyperlinearInvisible (f x) := by
  intro K _ hK rho
  exact hx K inferInstance hK (rho.comp f)

/-- Functoriality of the hyperlinear residual. -/
theorem hyperlinearResidual_map_le (f : G →* H) :
    (hyperlinearResidual G).map f ≤ hyperlinearResidual H := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact HyperlinearInvisible.map hx f

/-- One detecting homomorphism into a hyperlinear group excludes the marked
element from the hyperlinear residual. -/
theorem not_hyperlinearInvisible_of_hyperlinear_detector
    {x : G} (hH : IsHyperlinear H) (rho : G →* H) (hdetect : rho x ≠ 1) :
    ¬ HyperlinearInvisible x := by
  intro hx
  exact hdetect (hx H inferInstance hH rho)

/-- Radical form of `not_hyperlinearInvisible_of_hyperlinear_detector`. -/
theorem not_mem_hyperlinearResidual_of_hyperlinear_detector
    {x : G} (hH : IsHyperlinear H) (rho : G →* H) (hdetect : rho x ≠ 1) :
    x ∉ hyperlinearResidual G :=
  not_hyperlinearInvisible_of_hyperlinear_detector hH rho hdetect

/-- A hyperlinear detector which is faithful on a mapped subgroup makes the
hyperlinear residual meet that subgroup trivially.  This is the semantic
kernel step in the balanced radical-implantation construction: the operator
algebra supplies `rho`, while this theorem records that every nonidentity
element of the implanted finite group is detected simultaneously. -/
theorem comap_hyperlinearResidual_eq_bot_of_detector_injective
    {A : Type u} [Group A]
    (i : A →* G) (hH : IsHyperlinear H) (rho : G →* H)
    (hinj : Function.Injective (rho.comp i)) :
    (hyperlinearResidual G).comap i = ⊥ := by
  apply le_antisymm
  · intro a ha
    apply Subgroup.mem_bot.mpr
    apply hinj
    change rho (i a) = rho (i 1)
    rw [map_one, map_one]
    exact ha H inferInstance hH rho
  · exact bot_le

/-- A hyperlinear group has trivial hyperlinear residual: its identity
homomorphism is already a hyperlinear detector for every nonidentity element. -/
theorem hyperlinearResidual_eq_bot_of_isHyperlinear (hG : IsHyperlinear G) :
    hyperlinearResidual G = ⊥ := by
  apply le_antisymm
  · intro x hx
    have hkilled : (MonoidHom.id G) x = 1 := hx G inferInstance hG (MonoidHom.id G)
    exact Subgroup.mem_bot.mpr hkilled
  · exact bot_le

/-- **Nonhyperlinearity endpoint.**  One nonidentity element killed by every
homomorphism to every hyperlinear group proves that the source group is not
hyperlinear. -/
theorem not_isHyperlinear_of_hyperlinearInvisible
    {x : G} (hx : HyperlinearInvisible x) (hne : x ≠ 1) :
    ¬ IsHyperlinear G := by
  intro hG
  exact hne (hx G inferInstance hG (MonoidHom.id G))

/-- Radical form of `not_isHyperlinear_of_hyperlinearInvisible`. -/
theorem not_isHyperlinear_of_mem_hyperlinearResidual
    {x : G} (hx : x ∈ hyperlinearResidual G) (hne : x ≠ 1) :
    ¬ IsHyperlinear G :=
  not_isHyperlinear_of_hyperlinearInvisible hx hne

/-- A nontrivial hyperlinear residual is itself a certificate of
nonhyperlinearity. -/
theorem not_isHyperlinear_of_hyperlinearResidual_ne_bot
    (hres : hyperlinearResidual G ≠ ⊥) : ¬ IsHyperlinear G := by
  intro hG
  exact hres (hyperlinearResidual_eq_bot_of_isHyperlinear hG)

/-- One detecting homomorphism into a sofic group excludes the marked
element from the sofic residual. -/
theorem not_soficInvisible_of_sofic_detector
    {x : G} (hH : IsSofic H) (rho : G →* H) (hdetect : rho x ≠ 1) :
    ¬ SoficInvisible x := by
  intro hx
  exact hdetect (hx H inferInstance hH rho)

/-- Exact MF-versus-hyperlinear radical separation from one marked detector. -/
theorem coronaMFInvisible_and_not_hyperlinearInvisible_of_detector
    {x : G} (hmf : CoronaMFInvisible x) (hH : IsHyperlinear H)
    (rho : G →* H) (hdetect : rho x ≠ 1) :
    CoronaMFInvisible x ∧ ¬ HyperlinearInvisible x :=
  ⟨hmf, not_hyperlinearInvisible_of_hyperlinear_detector hH rho hdetect⟩

/-- A sofic detector of an MF-invisible element separates the MF radical
from both the hyperlinear and sofic radicals. -/
theorem coronaMFInvisible_not_hyperlinearInvisible_not_soficInvisible_of_detector
    {x : G} (hmf : CoronaMFInvisible x) (hH : IsSofic H)
    (rho : G →* H) (hdetect : rho x ≠ 1) :
    CoronaMFInvisible x ∧ ¬ HyperlinearInvisible x ∧ ¬ SoficInvisible x := by
  refine ⟨hmf, ?_, not_soficInvisible_of_sofic_detector hH rho hdetect⟩
  exact not_hyperlinearInvisible_of_hyperlinear_detector
    (isHyperlinear_of_isSofic hH) rho hdetect

/-- A sofic detector of an MF-invisible element has a range which is sofic
but not operator MF. -/
theorem sofic_range_not_isOperatorMF_of_coronaMFInvisible
    [Countable G] {x : G} (hmf : CoronaMFInvisible x) (hH : IsSofic H)
    (rho : G →* H) (hdetect : rho x ≠ 1) :
    IsSofic rho.range ∧ ¬ IsOperatorMF rho.range := by
  letI : Countable rho.range :=
    Function.Surjective.countable rho.rangeRestrict_surjective
  constructor
  · exact isSofic_of_injective rho.range.subtype Subtype.val_injective hH
  · intro hMF
    have hbot : coronaMFResidual rho.range = ⊥ :=
      (isOperatorMF_iff_coronaMFResidual_eq_bot).mp hMF
    have himage : CoronaMFInvisible (rho.rangeRestrict x) := by
      intro X hX sigma
      exact hmf X hX (sigma.comp rho.rangeRestrict)
    have hmem : rho.rangeRestrict x ∈ coronaMFResidual rho.range := himage
    rw [hbot] at hmem
    have hone : rho.rangeRestrict x = 1 := Subgroup.mem_bot.mp hmem
    apply hdetect
    simpa using congrArg Subtype.val hone

/-- A countable simple target containing the injective image of a nontrivial
MF-invisible element has full norm-MF residual.  The manuscript combines this
formal kernel statement with the Elek--Szabó theorem embedding every countable
sofic group in a countable simple sofic group. -/
theorem simple_envelope_full_normMFResidual_of_coronaMFInvisible
    [Countable H] [IsSimpleGroup H]
    {x : G} (hmf : CoronaMFInvisible x) (hne : x ≠ 1)
    (rho : G →* H) (hinj : Function.Injective rho) :
    normMFResidual H = ⊤ := by
  have himage : CoronaMFInvisible (rho x) := by
    intro X hX sigma
    exact hmf X hX (sigma.comp rho)
  apply normMFResidual_eq_top_of_simple
  · exact himage.toNormMFInvisible
  · intro hrho
    apply hne
    exact hinj (by simpa using hrho)

/-- If an MF-radical element has a hyperlinear detector, the MF radical is
not contained in the hyperlinear radical. -/
theorem not_coronaMFResidual_le_hyperlinearResidual_of_detector
    {x : G} (hmf : x ∈ coronaMFResidual G) (hH : IsHyperlinear H)
    (rho : G →* H) (hdetect : rho x ≠ 1) :
    ¬ coronaMFResidual G ≤ hyperlinearResidual G := by
  intro hle
  exact not_mem_hyperlinearResidual_of_hyperlinear_detector hH rho hdetect
    (hle hmf)

/-- **Radical-collision criterion.**  A sofic-residual element detected by
one hyperlinear representation witnesses that the sofic residual is not
contained in the hyperlinear residual.  The detecting range is the
hyperlinear nonsofic group supplied by
`hyperlinear_range_and_failureOfSoficity_of_soficInvisible`. -/
theorem not_soficResidual_le_hyperlinearResidual_of_detector
    {x : G} (hsofic : x ∈ soficResidual G) (hH : IsHyperlinear H)
    (rho : G →* H) (hdetect : rho x ≠ 1) :
    ¬ soficResidual G ≤ hyperlinearResidual G := by
  intro hle
  exact not_mem_hyperlinearResidual_of_hyperlinear_detector hH rho hdetect
    (hle hsofic)

end GroupApproximation
