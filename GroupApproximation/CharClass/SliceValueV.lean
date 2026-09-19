import GroupApproximation.CharClass.ParityEvenVSlice
import GroupApproximation.CharClass.SliceVGenerator
import GroupApproximation.CharClass.SliceRoots
import GroupApproximation.CharClass.SliceHomogeneous
import GroupApproximation.CharClass.SliceReindex

/-!
# The value of the Chern classes of `V`

The composition.  Every ingredient is on origin and nothing new is proved here.

The split relation gives a vanishing product on the projectivisation; the
factorisation turns it into the elementary symmetric functions of the roots;
homogeneity carries those past the degreewise component that `chernOf` takes;
`cc-projective`'s two identifications evaluate the roots, zero on the three
constant lines and one generator per block; and reciprocal Vieta with the block
product recognises the result as the slice polynomial's coefficient.

The roots are taken as the Euler classes of the flat family at its *unrestricted*
trace proof, so that the agreement hypothesis of `splitRelation_V` is `rfl`.  That
is only possible because the flat family reads its index modulo the rank and so
consists of genuine lines at every index.

## Main declarations

* `vRootE` — the roots, as Euler classes.
* `vSliceValue_sliceGen` — **the value.**
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.CharClass.Bundle
open GroupApproximation.CharClass.LH
open GroupApproximation.CharClass.LHCast

noncomputable section

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-- Equal bundles have equal Euler classes; the trace proofs are irrelevant. -/
theorem lineEulerOf_congr {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]
    [DecidableEq ι] {L L' : Bundle X ι} (h : L = L')
    (hL : ∀ x, (L x).trace = 1) (hL' : ∀ x, (L' x).trace = 1) :
    lineEulerOf L hL = lineEulerOf L' hL' := by
  subst h
  rfl

/-- The roots of `V`, as the Euler classes of the flat family. -/
def vRootE (dd : Fin ℓ → ℕ) (l : ℕ) : Hmod2 (TopCat.of (baseY dd)) 2 :=
  lineEulerOf (vLineFlatBundle dd l) (fun y => trace_vLineFlatBundle dd l y)

/-- At an index coming from the block type, the root is the block's Euler class. -/
theorem vRootE_equiv (dd : Fin ℓ → ℕ) (k : Fin 3 ⊕ HBlk dd) :
    vRootE dd ((vIndexEquiv dd k : Fin (lixRank dd)) : ℕ)
      = lineEulerOf (vLineYBundle k) (fun y => trace_vLineY k y) := by
  refine lineEulerOf_congr ?_ _ _
  refine congrArg vLineYBundle ?_
  have hlt : ((vIndexEquiv dd k : Fin (lixRank dd)) : ℕ) < lixRank dd :=
    (vIndexEquiv dd k).isLt
  have h : (⟨((vIndexEquiv dd k : Fin (lixRank dd)) : ℕ) % lixRank dd,
      Nat.mod_lt _ (lixRank_pos dd)⟩ : Fin (lixRank dd)) = vIndexEquiv dd k :=
    Fin.ext (Nat.mod_eq_of_lt hlt)
  rw [h]
  exact (vIndexEquiv dd).symm_apply_apply k

/-- **The value of the Chern classes of `V`.** -/
theorem vSliceValue_sliceGen (dd : Fin ℓ → ℕ) (hdd : ∀ j, 0 < dd j)
    [CompactSpace (baseY dd)] [Nonempty (baseY dd)] :
    VSliceValue dd (sliceGen dd hdd) := by
  intro q
  set D := lerayHirschData_of_graded
    (lerayHirschGraded_compact (vBundleY dd) (lixRank dd)
      (rank_vBundleY_lixRank dd) (lixRank_pos dd)) with hD
  -- the split relation, at the Euler-class roots
  have hrel : D.SplitRelation (lixRank dd) (vRootE dd) :=
    splitRelation_V dd (vRootE dd) (fun _ _ => rfl)
  -- the factorisation
  have hsplit := D.splitPoly_of_splitRelation D (𝟙 _) (𝟙 _) (by simp) (by simp)
    (lixRank dd) rfl rfl (vRootE dd) hrel
  -- the Chern class is the elementary symmetric function of the roots
  have hchern : D.chern q
      = esymmOn (Finset.range (lixRank dd))
          (fun l => TotalH.of (TopCat.of (baseY dd)) 2 (vRootE dd l)) q := by
    have h := chern_split_of_splitPoly D (𝟙 _) (lixRank dd) rfl (vRootE dd) hsplit q
    rwa [ThomChern.totalMap_id] at h
  -- the slice polynomial's coefficient is the same symmetric function
  have hcoeff : (sliceClass (Finset.univ : Finset (Fin ℓ)) (sliceGen dd hdd) dd).coeff q
      = esymmOn (Finset.range (lixRank dd))
          (fun l => TotalH.of (TopCat.of (baseY dd)) 2 (vRootE dd l)) q := by
    rw [← coeff_prod_one_add_C_mul_X,
      prod_range_of_equiv (lixRank dd) (vIndexEquiv dd)
        (fun k => 1 + Polynomial.C (TotalH.of (TopCat.of (baseY dd)) 2
          (lineEulerOf (vLineYBundle k) (fun y => trace_vLineY k y))) * Polynomial.X)
        (fun l => 1 + Polynomial.C (TotalH.of (TopCat.of (baseY dd)) 2
          (vRootE dd l)) * Polynomial.X)
        (fun k => by rw [vRootE_equiv]),
      prod_blocks_eq_sliceClass dd (sliceGen dd hdd) _
        (fun i => by rw [lineEulerOf_vLineY_inl dd i, map_zero])
        (fun b => sliceGen_eq_root dd hdd b)]
  -- assemble
  show TotalH.of (TopCat.of (baseY dd)) (2 * q)
      (TotalH.component (TopCat.of (baseY dd)) (2 * q) (D.chern q)) = _
  rw [hchern, hcoeff, of_component_esymmOn]

end

end CharClass
end GroupApproximation
