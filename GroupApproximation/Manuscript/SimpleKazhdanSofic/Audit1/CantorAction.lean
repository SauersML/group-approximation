import GroupApproximation.Manuscript.SimpleKazhdanSofic.MainFromGeneral
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterAction
import Mathlib.Topology.Metrizable.CompletelyMetrizable
import GroupApproximation.Meta.AxiomGuard

/-!
# The subshift of `thm:main` is a Cantor set with a topologically free action

`simple_kazhdan_sofic_group.tex` (HEAD 1eefb3bb), section "Proof of Theorem 1", l.359–362:

> Let $\Z$ act on $X$ by powers of $T$, where $(Tx)_t=x_{t+1}$, and write $u=u_1$, so
> $ufu^{-1}=f\circ T^{-1}$. Minimality and infiniteness imply that $X$ has no isolated points and
> $T$ has no periodic points, so $X$ is a Cantor set and the action is topologically free.

Here `X = S.carrier` for an infinite minimal subshift `S : Subshift A ℤ` over a finite discrete
alphabet `A` (the setting of `thm:main`), `T = subshiftHomeo S`, and `R = R S`.

A Cantor set is, as throughout the corpus (`GeneralTheorem`, `GeneralRing/Statement`), a nonempty
compact metrizable totally disconnected perfect space: these are the instances under which
`thm:general` is stated.

Proof route.
* `(Tx)_t = x_{t+1}`: definitional, `shift 1 x = fun t => x (1 + t)`.
* The action by powers of `T` is `shiftMulAction` (`ofAdd j • x = T^j x`, definitional), and
  `u = u_1 = single (ofAdd 1) 1` is `Pestov91.CrossedProduct.unit` (definitional).
* `ufu^{-1} = f ∘ T^{-1}`: `ClopenCrossedProduct.unit_mul_coeff_mul_inv`.
* No isolated points: `perfectSpace_carrier` (an isolated point with dense orbits would make the
  compact space discrete, hence finite).
* No periodic points: `zpow_apply_ne_self` with the dense orbits `minimalSubshift_dense_orbits`.
* Cantor set: nonempty from infiniteness; compact (`compactSpace_carrier`); metrizable, as a
  subspace of the countable product `ℤ → A` of discrete, hence completely metrizable, spaces;
  totally disconnected as a subspace of a product of discrete spaces; perfect as above.
* Topologically free: `isTopologicallyFree_shift`, which is `IsTopologicallyFreeAction`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace Audit1

open SymbolicDynamics.FullShift
open Multiplicative (ofAdd toAdd)

variable {A : Type} [TopologicalSpace A] [DiscreteTopology A] [Finite A]

/-- **Tex l.359–362.** For an infinite minimal subshift `X = S.carrier` with shift `T`:
`(Tx)_t = x_{t+1}`; `ℤ` acts by powers of `T`; `u = u_1` and `ufu⁻¹ = f ∘ T⁻¹` in
`R = LC(X, F₂) ⋊_T ℤ`; `X` has no isolated points; `T` has no periodic points; `X` is a Cantor set
(nonempty, compact, metrizable, totally disconnected, perfect); and the action is topologically
free. -/
theorem manuscriptSentence_cantorSetTopologicallyFree (S : Subshift A ℤ)
    (hinf : Infinite S.carrier) (hmin : IsMinimal S) :
    (∀ (x : S.carrier) (t : ℤ),
      ((subshiftHomeo S x : S.carrier) : ℤ → A) t = (x : ℤ → A) (t + 1)) ∧
    (∀ (j : ℤ) (x : S.carrier), (ofAdd j : Multiplicative ℤ) • x = (subshiftHomeo S ^ j) x) ∧
    ((ClopenCrossedProduct.unit (subshiftHomeo S) (ZMod 2) : R S) =
      SkewMonoidAlgebra.single (ofAdd (1 : ℤ)) 1) ∧
    (∀ f : LocallyConstant S.carrier (ZMod 2),
      (ClopenCrossedProduct.unit (subshiftHomeo S) (ZMod 2) : R S) *
          ClopenCrossedProduct.coeff (subshiftHomeo S) (ZMod 2) f *
          ↑(ClopenCrossedProduct.unit (subshiftHomeo S) (ZMod 2))⁻¹ =
        ClopenCrossedProduct.coeff (subshiftHomeo S) (ZMod 2)
          (LocallyConstant.comap ⟨⇑(subshiftHomeo S).symm, (subshiftHomeo S).symm.continuous⟩ f)) ∧
    PerfectSpace S.carrier ∧
    (∀ j : ℤ, j ≠ 0 → ∀ y : S.carrier, (subshiftHomeo S ^ j) y ≠ y) ∧
    (Nonempty S.carrier ∧ CompactSpace S.carrier ∧ TopologicalSpace.MetrizableSpace S.carrier ∧
      TotallyDisconnectedSpace S.carrier ∧ PerfectSpace S.carrier) ∧
    IsTopologicallyFreeAction (Multiplicative ℤ) S.carrier := by
  haveI := hinf
  have hmet : TopologicalSpace.MetrizableSpace S.carrier := by
    haveI : TopologicalSpace.IsCompletelyMetrizableSpace (ℤ → A) :=
      TopologicalSpace.IsCompletelyMetrizableSpace.pi_countable
    exact TopologicalSpace.MetrizableSpace.subtype S.carrier
  have hperf : PerfectSpace S.carrier := perfectSpace_carrier S hinf hmin
  refine ⟨fun x t => ?_, fun j x => rfl, rfl,
    fun f => ClopenCrossedProduct.unit_mul_coeff_mul_inv (subshiftHomeo S) (ZMod 2) f, hperf,
    fun j hj y => zpow_apply_ne_self (subshiftHomeo S)
      (fun z => minimalSubshift_dense_orbits S hmin z) hj y,
    ⟨Infinite.nonempty _, compactSpace_carrier S, hmet, inferInstance, hperf⟩,
    isTopologicallyFree_shift S hinf hmin⟩
  show (x : ℤ → A) (1 + t) = (x : ℤ → A) (t + 1)
  exact congrArg (x : ℤ → A) (add_comm 1 t)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.Audit1.manuscriptSentence_cantorSetTopologicallyFree

end Audit1
end SimpleKazhdanSofic
end GroupApproximation
