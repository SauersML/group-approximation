import GroupApproximation.Algebra.PermutationalWreathAmenable
import GroupApproximation.Algebra.FiniteResidual
import GroupApproximation.Sofic.LocallyFiniteMF

/-!
# The invisible radical is intrinsically tame

**Corollary 54.2A** of the dossier.  The approximation-invisible radical of a
finite-lamp compression wreath product sits inside the lamp base, and every
subgroup of the lamp base is as tame as an infinite group gets: locally finite,
amenable, residually finite, and operator-MF.

The point is diagnostic.  One might expect the subgroup that no matrix corona
can see to be intrinsically pathological.  It is the opposite: finite models
for it are abundant, and all five of its own residuals vanish.  What fails is
*extending* those models along the compressed Kazhdan action to models of the
ambient group, which is why the finite-index radical formula of Section 49 is
sharp and cannot be relaxed to arbitrary — even normal, amenable, residually
finite — subgroups.

Everything here is stated for an arbitrary subgroup of `Lamp K X`, so it
applies to the telescope kernel without knowing anything about it beyond where
it lives.
-/

namespace GroupApproximation

universe u v

variable {K : Type u} [Group K] {X : Type v}

/-! ## A locally finite group has finite finitely generated subgroups -/

/-- The closure of a finite set in a locally finite group is finite.  This is
the form `Amenability.isAmenable_of_locallyFinite` consumes. -/
theorem closure_finite_of_isLocallyFiniteGroup {G : Type*} [Group G]
    (hG : IsLocallyFiniteGroup G) (S : Finset G) :
    (Subgroup.closure (S : Set G) : Set G).Finite := by
  obtain ⟨H, hHfin, hSH⟩ := hG S
  have hle : Subgroup.closure (S : Set G) ≤ H := by
    rw [Subgroup.closure_le]
    intro g hg
    exact hSH g hg
  exact Set.Finite.subset (Set.toFinite (H : Set G)) hle

/-- A locally finite group is amenable. -/
theorem isAmenable_of_isLocallyFiniteGroup {G : Type*} [Group G]
    (hG : IsLocallyFiniteGroup G) : Amenability.IsAmenable G :=
  Amenability.isAmenable_of_locallyFinite
    (closure_finite_of_isLocallyFiniteGroup hG)

/-! ## The lamp group and all of its subgroups -/

/-- Over a finite lamp the configuration group is locally finite. -/
theorem lamp_isLocallyFiniteGroup [Finite K] :
    IsLocallyFiniteGroup (Lamp K X) := by
  intro s
  refine ⟨Subgroup.closure (s : Set (Lamp K X)), ?_, ?_⟩
  · have hfin := lamp_closure_finite (K := K) (X := X) s
    exact hfin.to_subtype
  · intro g hg
    exact Subgroup.subset_closure hg

/-- Every subgroup of the lamp group is locally finite. -/
theorem lampSub_isLocallyFiniteGroup [Finite K] (R : Subgroup (Lamp K X)) :
    IsLocallyFiniteGroup R :=
  lamp_isLocallyFiniteGroup.comap R.subtype R.subtype_injective

/-- Every subgroup of the lamp group is amenable. -/
theorem lampSub_isAmenable [Finite K] (R : Subgroup (Lamp K X)) :
    Amenability.IsAmenable R :=
  isAmenable_of_isLocallyFiniteGroup (lampSub_isLocallyFiniteGroup R)

/-- Every subgroup of the lamp group is residually finite. -/
theorem lampSub_isResiduallyFinite [Finite K] (R : Subgroup (Lamp K X)) :
    IsResiduallyFinite R :=
  (lamp_isResiduallyFinite (K := K) (X := X)).subgroup R

/-- Every countable subgroup of the lamp group is operator-MF.  In particular
the radical that the ambient group's corona representations cannot see is
itself perfectly visible to them, once it is considered on its own. -/
theorem lampSub_isOperatorMF [Finite K] (R : Subgroup (Lamp K X))
    [Countable R] : IsOperatorMF R :=
  isOperatorMF_of_locallyFinite (lampSub_isLocallyFiniteGroup R)

/-- **Corollary 54.2A**, packaged: the tameness of an arbitrary subgroup of the
lamp base.  Read against `corona-finite-index-radical-heredity`, this is the
sharpness statement: the ambient residual of the wreath product equals this
subgroup, while all of its own residuals are trivial. -/
theorem lampSub_tame [Finite K] (R : Subgroup (Lamp K X)) [Countable R] :
    IsLocallyFiniteGroup R ∧ Amenability.IsAmenable R ∧
      IsResiduallyFinite R ∧ IsOperatorMF R :=
  ⟨lampSub_isLocallyFiniteGroup R, lampSub_isAmenable R,
    lampSub_isResiduallyFinite R, lampSub_isOperatorMF R⟩

end GroupApproximation
