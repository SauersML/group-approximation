import GroupApproximation.Sofic.NormMFCoronaRadical

/-!
# Exact computation and factorization for the MF radical

These are the formal quotient consequences needed once a concrete normal
subgroup has been shown to lie in the norm-MF residual.  They are independent
of the mechanism producing that containment.

* Every standard cofinite-corona representation factors uniquely through the
  quotient by a normal subgroup contained in the residual.
* If that quotient is operator-MF, the subgroup is exactly the residual.

Thus an obstruction theorem for an intrinsic defect subgroup can be upgraded
without further analysis from elementwise invisibility to an explicit largest
MF quotient.
-/

namespace GroupApproximation

universe u

variable {G : Type u} [Group G]

/-- Every representation in a standard cofinite norm-matrix corona factors
uniquely through a normal subgroup contained in the MF radical. -/
theorem existsUnique_quotient_factorization_to_normMatrixCorona
    (N : Subgroup G) [N.Normal] (hN : N ≤ coronaMFResidual G)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n))
    (rho : G →* NormMatrixCoronaUnitary X) :
    ∃! rhoBar : (G ⧸ N) →* NormMatrixCoronaUnitary X,
      rhoBar.comp (QuotientGroup.mk' N) = rho := by
  have hker : N ≤ rho.ker := by
    intro x hx
    exact hN hx X hX rho
  let rhoBar : (G ⧸ N) →* NormMatrixCoronaUnitary X :=
    QuotientGroup.lift N rho hker
  have hcomp : rhoBar.comp (QuotientGroup.mk' N) = rho :=
    QuotientGroup.lift_comp_mk' N rho hker
  refine ⟨rhoBar, hcomp, ?_⟩
  intro f hf
  apply MonoidHom.ext
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
  exact DFunLike.congr_fun (hf.trans hcomp.symm) g

/-- If the quotient by `N` is operator-MF, every MF-invisible element already
belongs to `N`. -/
theorem normMFResidual_le_of_quotient_isOperatorMF [Countable G]
    (N : Subgroup G) [N.Normal] (hquot : IsOperatorMF (G ⧸ N)) :
    normMFResidual G ≤ N := by
  intro x hx
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hqx : q x ∈ normMFResidual (G ⧸ N) :=
    map_normMFResidual_le q ⟨x, hx, rfl⟩
  haveI : Countable (G ⧸ N) :=
    Function.Surjective.countable (QuotientGroup.mk'_surjective N)
  rw [normMFResidual_eq_bot_of_isOperatorMF hquot] at hqx
  exact (QuotientGroup.eq_one_iff x).mp (Subgroup.mem_bot.mp hqx)

/-- **Exact MF radical criterion.**  A normal subgroup contained in the
MF radical is the entire radical as soon as its quotient is operator-MF. -/
theorem normMFResidual_eq_of_le_and_quotient_isOperatorMF [Countable G]
    (N : Subgroup G) [N.Normal] (hN : N ≤ normMFResidual G)
    (hquot : IsOperatorMF (G ⧸ N)) :
    normMFResidual G = N :=
  le_antisymm (normMFResidual_le_of_quotient_isOperatorMF N hquot) hN

/-- Corona-language version of the exact-radical criterion. -/
theorem coronaMFResidual_eq_of_le_and_quotient_isOperatorMF [Countable G]
    (N : Subgroup G) [N.Normal] (hN : N ≤ coronaMFResidual G)
    (hquot : IsOperatorMF (G ⧸ N)) :
    coronaMFResidual G = N := by
  rw [coronaMFResidual_eq_normMFResidual] at hN ⊢
  exact normMFResidual_eq_of_le_and_quotient_isOperatorMF N hN hquot

end GroupApproximation
