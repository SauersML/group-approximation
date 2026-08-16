import GroupApproximation.Sofic.InducedCoronaMF
import GroupApproximation.Sofic.NormMFCoronaRadical
import GroupApproximation.Algebra.FiniteResidual
import GroupApproximation.Sofic.OperatorMFPositiveControls

/-!
# Theorem 49.5: a nontrivial MF radical kills every finite-index subgroup

Section 49 proves that operator-MF is inherited in both directions across a
finite-index inclusion.  Theorem 49.5 turns the downward half into a rigidity
statement: once the MF radical of `G` is nontrivial, *no* finite-index subgroup
of `G` is MF either, so the failure cannot be repaired by passing to a subgroup
of finite index -- and, with Corollary 49.6, not by passing to any commensurable
group.

The mechanism needs nothing about the concrete family.  A nontrivial invisible
element `x` lies in every finite-index subgroup `H`, and induction from `H` to
`G` (`corona_invisible_of_finiteIndex`) carries its invisibility *down*, so no
corona representation of `H` separates it from the identity.  A faithful one
would.

Two presentations of the corona are in play and they are different Lean types:
`IsOperatorMF` and `corona_invisible_of_finiteIndex` use
`NormMatrixCoronaUnitary`, the quotient of the product of unitary groups by the
null-cofinite subgroup, and so does `coronaMFResidual`; the C*-algebra
presentation `unitary (NormMatrixCStarCorona _)` behind `actualCoronaMFResidual`
is isomorphic to it but not equal.  Everything here is stated in the first
presentation, which is the one `IsOperatorMF` is defined in.

That the invisible element lies in the finite residual is the chain of Theorem
41.3, `Res_MF ≤ Rad_fd ≤ Res_fin`; it is carried here as a hypothesis rather
than re-derived, because the repository proves that chain for the C*-presentation
of the radical.

`forall_finiteIndex_not_isOperatorMF` is the statement in the form Corollary
49.6 consumes: it discharges the hypothesis "the MF radical survives every
finite-index passage", which `Sofic/CommensurabilityInvariance` carries
undischarged.
-/

namespace GroupApproximation

namespace InducedCorona

universe u

variable {G : Type u} [Group G]

/-- **Theorem 49.5, elementwise.**  A nontrivial element invisible to every
corona representation of `G`, and lying in the finite residual, stays nontrivial
and invisible inside every finite-index subgroup, so that subgroup is not
operator-MF. -/
theorem not_isOperatorMF_of_mem_coronaMFResidual
    {x : G} (hx1 : x ≠ 1) (hMF : x ∈ coronaMFResidual G)
    (hfin : x ∈ finiteResidual G)
    (H : Subgroup G) [H.FiniteIndex] : ¬ IsOperatorMF H := by
  intro hH
  obtain ⟨X, hX, Θ, hΘ⟩ := hH
  have hxH : x ∈ H := mem_finiteResidual_iff.mp hfin H inferInstance
  have hone : Θ ⟨x, hxH⟩ = 1 :=
    corona_invisible_of_finiteIndex H hxH
      (mem_coronaMFResidual_iff.mp hMF) X hX Θ
  have hxone : (⟨x, hxH⟩ : H) = 1 := hΘ (by rw [hone, map_one])
  exact hx1 (by simpa using congrArg Subtype.val hxone)

/-- **Theorem 49.5.**  If the MF radical of `G` is nontrivial -- and sits inside
the finite residual, which is the chain of Theorem 41.3 -- then no finite-index
subgroup of `G` is operator-MF.  The failure is hereditary all the way down the
finite-index lattice. -/
theorem forall_finiteIndex_not_isOperatorMF
    (hle : coronaMFResidual G ≤ finiteResidual G)
    (h : coronaMFResidual G ≠ ⊥)
    (H : Subgroup G) [H.FiniteIndex] : ¬ IsOperatorMF H := by
  obtain ⟨⟨x, hx⟩, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
  exact not_isOperatorMF_of_mem_coronaMFResidual
    (fun hcon => hne (Subtype.ext hcon)) hx (hle hx) H

/-- The same conclusion for `G` itself, which is the `H = ⊤` case. -/
theorem not_isOperatorMF_of_coronaMFResidual_ne_bot
    (hle : coronaMFResidual G ≤ finiteResidual G)
    (h : coronaMFResidual G ≠ ⊥) : ¬ IsOperatorMF G := by
  intro hG
  exact forall_finiteIndex_not_isOperatorMF hle h ⊤
    (IsOperatorMF.comap hG (⊤ : Subgroup G).subtype Subtype.val_injective)

end InducedCorona

end GroupApproximation
