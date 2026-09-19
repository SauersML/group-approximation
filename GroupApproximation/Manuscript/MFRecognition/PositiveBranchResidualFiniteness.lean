import GroupApproximation.GroupTheory.HNNFiniteQuotientCriterion
import GroupApproximation.Manuscript.MFRecognition.PositiveBranchFiniteQuotients

/-!
# Residual finiteness of the synchronized twisted edge

The finite quotients used in tensor synchronization already contain the
group-theoretic datum needed by the finite-quotient HNN criterion.  This file
extracts that datum without any operator-algebraic permanence theorem.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace PositiveBranchResidualFiniteness

noncomputable section

open Recognition
open GroupApproximation.HNNFiniteQuotientCriterion
open GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationCore

variable {Gamma Q G₀ P₀ B₀ : Type}
variable [Group Gamma] [Group Q] [Group G₀] [Group P₀] [Group B₀]

/-- Add an arbitrary finite quotient of `Gamma` to a synchronized quotient.
This can only shrink the kernel on the edge, so it preserves the one-sided
kernel condition supplied by `ropeLambda`. -/
def synchronizedBaseQuotient
    (lambda : Gamma →* G₀) (p : Gamma →* P₀) (beta : Q →* B₀) :
    Gamma × Q →* (G₀ × P₀) × B₀ :=
  (((lambda.prod p).comp (MonoidHom.fst Gamma Q)).prod
    (beta.comp (MonoidHom.snd Gamma Q)))

@[simp] theorem synchronizedBaseQuotient_apply
    (lambda : Gamma →* G₀) (p : Gamma →* P₀) (beta : Q →* B₀)
    (g : Gamma × Q) :
    synchronizedBaseQuotient lambda p beta g =
      ((lambda g.1, p g.1), beta g.2) := rfl

/-- The source and graph edge maps have the same kernel in every synchronized
quotient.  The extra `p` coordinate is deliberately arbitrary. -/
theorem synchronized_edge_ker_eq
    (S : Subgroup Gamma) (tau : S →* Q)
    (lambda : Gamma →* G₀) (p : Gamma →* P₀) (beta : Q →* B₀)
    (hker : (lambda.comp S.subtype).ker ≤ (beta.comp tau).ker) :
    ((synchronizedBaseQuotient lambda p beta).comp
        (edgeSource S Q)).ker =
      ((synchronizedBaseQuotient lambda p beta).comp
        (edgeTarget S tau)).ker := by
  ext s
  simp only [MonoidHom.mem_ker]
  constructor
  · intro hs
    have hlambda : lambda (s : Gamma) = 1 := by
      exact congrArg (fun z : (G₀ × P₀) × B₀ => z.1.1) hs
    have hp : p (s : Gamma) = 1 := by
      exact congrArg (fun z : (G₀ × P₀) × B₀ => z.1.2) hs
    have hbeta : beta (tau s) = 1 := by
      have hsKer : s ∈ (lambda.comp S.subtype).ker := by
        exact MonoidHom.mem_ker.mpr hlambda
      exact MonoidHom.mem_ker.mp (hker hsKer)
    exact Prod.ext (Prod.ext hlambda hp) hbeta
  · intro hs
    have hlambda : lambda (s : Gamma) = 1 := by
      exact congrArg (fun z : (G₀ × P₀) × B₀ => z.1.1) hs
    have hp : p (s : Gamma) = 1 := by
      exact congrArg (fun z : (G₀ × P₀) × B₀ => z.1.2) hs
    exact Prod.ext (Prod.ext hlambda hp) (map_one beta)

/-- The quotient edge isomorphism induced by the equal-kernel theorem. -/
def synchronizedEdgeEquiv
    (S : Subgroup Gamma) (tau : S →* Q)
    (lambda : Gamma →* G₀) (p : Gamma →* P₀) (beta : Q →* B₀)
    (hker : (lambda.comp S.subtype).ker ≤ (beta.comp tau).ker) :
    (edgeSubgroupSource S Q).map (synchronizedBaseQuotient lambda p beta) ≃*
      (edgeSubgroupTarget S tau).map
        (synchronizedBaseQuotient lambda p beta) := by
  let ell := synchronizedBaseQuotient lambda p beta
  let f := ell.comp (edgeSource S Q)
  let g := ell.comp (edgeTarget S tau)
  have hf : f.range = (edgeSubgroupSource S Q).map ell := by
    exact MonoidHom.range_comp ell (edgeSource S Q)
  have hg : g.range = (edgeSubgroupTarget S tau).map ell := by
    exact MonoidHom.range_comp ell (edgeTarget S tau)
  exact (MulEquiv.subgroupCongr hf).symm.trans
    ((rangeMulEquivOfKerEq f g
      (synchronized_edge_ker_eq S tau lambda p beta hker)).trans
        (MulEquiv.subgroupCongr hg))

/-- On an actual edge element, the quotient equivalence has the expected
value. -/
@[simp] theorem synchronizedEdgeEquiv_apply
    (S : Subgroup Gamma) (tau : S →* Q)
    (lambda : Gamma →* G₀) (p : Gamma →* P₀) (beta : Q →* B₀)
    (hker : (lambda.comp S.subtype).ker ≤ (beta.comp tau).ker)
    (s : S) :
    ((synchronizedEdgeEquiv S tau lambda p beta hker
      ⟨synchronizedBaseQuotient lambda p beta (edgeSource S Q s),
        ⟨edgeSource S Q s, ⟨s, rfl⟩, rfl⟩⟩ :
        (edgeSubgroupTarget S tau).map
          (synchronizedBaseQuotient lambda p beta)) :
      (G₀ × P₀) × B₀) =
        synchronizedBaseQuotient lambda p beta (edgeTarget S tau s) := by
  have hres :
      rangeMulEquivOfKerEq
          ((synchronizedBaseQuotient lambda p beta).comp (edgeSource S Q))
          ((synchronizedBaseQuotient lambda p beta).comp (edgeTarget S tau))
          (synchronized_edge_ker_eq S tau lambda p beta hker)
          (((synchronizedBaseQuotient lambda p beta).comp
            (edgeSource S Q)).rangeRestrict s) =
        ((synchronizedBaseQuotient lambda p beta).comp
          (edgeTarget S tau)).rangeRestrict s :=
    rangeMulEquivOfKerEq_rangeRestrict _ _ _ s
  exact congrArg Subtype.val hres

end

end PositiveBranchResidualFiniteness
end MFRecognition
end Manuscript
end GroupApproximation
