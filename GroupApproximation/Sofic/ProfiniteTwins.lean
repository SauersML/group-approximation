import GroupApproximation.Algebra.VisibleQuotient
import GroupApproximation.Sofic.FiniteDimensionalResidual
import GroupApproximation.Sofic.AscendingHNNTelescopeRadical

/-!
# Profinite twins: the same finite quotients, opposite MF status

**Section 48** of the ascending-HNN dossier.  Collapsing a subgroup of the
finite residual changes nothing a finite group can see.  Precomposition with
the quotient map

    ((G ⧸ N) →* F)  →  (G →* F)

is injective because the quotient map is onto, and surjective for finite `F`
because a homomorphism to a finite group has finite-index kernel and therefore
kills the finite residual.  So `G` and `G ⧸ N` have *the same* finite
quotients -- not merely isomorphic profinite completions but a canonical
bijection of finite representations, and by `Algebra/VisibleQuotient` the same
finite-index subgroup lattice with the same indices.

That makes them profinite twins, and when the collapse is exactly what an MF
model cannot see, the twins have opposite MF status: `profinite_twins`.

`wreath_twins` is the concrete instance.  The first-stage radical of the
ascending-HNN wreath product sits inside the MF radical, hence inside the
finite residual, and it is nontrivial when the self-embedding is proper.  The
middle group is unconditionally not MF.  So as soon as the first-stage quotient
is MF, that quotient and the wreath product are profinite twins on opposite
sides of the MF line, separated by a nontrivial normal subgroup.
-/

namespace GroupApproximation
namespace ProfiniteTwins

open VisibleQuotient

universe u v

variable {G : Type u} [Group G] {N : Subgroup G} [N.Normal]

/-- Precomposition with the quotient map: every representation of the quotient
is a representation of the group. -/
def precomp (N : Subgroup G) [N.Normal] (F : Type v) [Group F] :
    ((G ⧸ N) →* F) → (G →* F) :=
  fun f => f.comp (QuotientGroup.mk' N)

/-- Distinct representations of the quotient stay distinct: the quotient map is
onto. -/
theorem precomp_injective (F : Type v) [Group F] :
    Function.Injective (precomp N F) := by
  intro f₁ f₂ h
  refine MonoidHom.ext fun q => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
  exact DFunLike.congr_fun h g

/-- **Every finite representation of the group comes from the quotient**, as
soon as the collapsed subgroup is invisible to finite targets. -/
theorem precomp_surjective (hN : N ≤ finiteResidual G) (F : Type v) [Group F]
    [Finite F] : Function.Surjective (precomp N F) := by
  intro f
  obtain ⟨F', hF', -⟩ := existsUnique_factor (N := N) f
    (fun x hx => finiteResidual_le_ker_of_finite f (hN hx))
  exact ⟨F', hF'⟩

theorem precomp_bijective (hN : N ≤ finiteResidual G) (F : Type v) [Group F]
    [Finite F] : Function.Bijective (precomp N F) :=
  ⟨precomp_injective F, precomp_surjective hN F⟩

/-- The finite representations of the group and of the quotient correspond. -/
noncomputable def finiteHomEquiv (hN : N ≤ finiteResidual G) (F : Type v)
    [Group F] [Finite F] : ((G ⧸ N) →* F) ≃ (G →* F) :=
  Equiv.ofBijective _ (precomp_bijective hN F)

/-- **Section 48.**  A group and its quotient by an invisible normal subgroup
have the same finite quotients; when the quotient is MF and the group is not,
they are profinite twins on opposite sides of the MF line. -/
theorem profinite_twins (hN : N ≤ finiteResidual G)
    (hMF : IsOperatorMF (G ⧸ N)) (hnot : ¬ IsOperatorMF G) :
    (∀ (F : Type v) [Group F] [Finite F], Function.Bijective (precomp N F)) ∧
      IsOperatorMF (G ⧸ N) ∧ ¬ IsOperatorMF G :=
  ⟨fun F => precomp_bijective hN F, hMF, hnot⟩

/-! ## The concrete twins of the ascending-HNN construction -/

section Wreath

open MarkedCompression MappingTelescope

variable {Γ₀ : Type} [Group Γ₀] (β : Γ₀ →* Γ₀) (hβ : Function.Injective β)
variable {K₀ : Type} [Group K₀] [DecidableEq (Cosets β hβ)]

include hβ in
/-- The first-stage radical is invisible to finite targets: it lies in the MF
radical, and the MF radical lies in the finite residual. -/
theorem stageRadical_le_finiteResidual [Countable (WreathV (K := K₀) β hβ)]
    (hΓ : HasKazhdanPropertyT.{0, 0} Γ₀) {k : K₀} (hk2 : k * k = 1) :
    stageRadical β hβ k ≤ finiteResidual (WreathV (K := K₀) β hβ) :=
  le_trans (stageRadical_le_actualCoronaMFResidual β hβ hΓ hk2)
    actualCoronaMFResidual_le_finiteResidual

include hβ in
/-- **The concrete profinite twins.**  The ascending-HNN wreath product and its
first-stage quotient have the same finite quotients, are separated by a
nontrivial normal subgroup, and lie on opposite sides of the MF line -- the
quotient by hypothesis, the wreath product unconditionally. -/
theorem wreath_twins [Countable (WreathV (K := K₀) β hβ)]
    (hΓ : HasKazhdanPropertyT.{0, 0} Γ₀) {k : K₀} (hk₀ : k ≠ 1)
    (hk2 : k * k = 1) {a₀ : Γ₀} (ha₀ : a₀ ∉ Set.range β)
    (hMF : IsOperatorMF (WreathV (K := K₀) β hβ ⧸ stageRadical β hβ k)) :
    (∀ (F : Type) [Group F] [Finite F],
        Function.Bijective (precomp (stageRadical β hβ k) F)) ∧
      IsOperatorMF (WreathV (K := K₀) β hβ ⧸ stageRadical β hβ k) ∧
      ¬ IsOperatorMF (WreathV (K := K₀) β hβ) ∧
      stageRadical β hβ k ≠ ⊥ := by
  have hnot : ¬ IsOperatorMF (WreathV (K := K₀) β hβ) := by
    intro h
    exact not_isCDEOperatorMF_wreath β hβ hΓ hk₀ hk2 ha₀
      ((isCDEOperatorMF_iff_isOperatorMF _).mpr h)
  obtain ⟨hbij, hq, hn⟩ :=
    profinite_twins (stageRadical_le_finiteResidual β hβ hΓ hk2) hMF hnot
  exact ⟨hbij, hq, hn, stageRadical_ne_bot β hβ hk₀ ha₀⟩

end Wreath

end ProfiniteTwins
end GroupApproximation
