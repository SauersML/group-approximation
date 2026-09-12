import GroupApproximation.CharClass.SliceGenOfLines
import GroupApproximation.CharClass.SliceGenOfBlocks
import GroupApproximation.CharClass.SliceValueV
import GroupApproximation.Meta.AxiomGuard

/-!
# The value of the mod-2 Chern classes of `V = 𝟏^{n+1} ⊕ H`, at sphere rank `n`

Lane `lx-integrator` of the STW Problem LIX strongest-theorem swarm: the `slice` leaf of
`Gen.WuStepDData` at `KGen.lixN n dd = S¹ × S^{2n+1} × ∏ⱼ ℂP^{dⱼ}`, stated about `V` alone.

`SliceValueV.vSliceValue_sliceGen` computes the classes of `V = 𝟏³ ⊕ H` over the projective
base.  Nothing in that computation sees the size of the trivial summand except the index type
of its lines, so this file runs the same composition over `lx-sliceK`'s rank-`n` lines
(`SliceGenOfLines`) and block product (`SliceGenOfBlocks`):

1. the split relation for the flat family of lines;
2. the factorisation, giving the elementary symmetric functions of the roots;
3. the roots: zero on the `n + 1` constant lines, the pulled-back generator of the `j`-th
   projective factor on every one of the `dⱼ` lines over that factor;
4. reciprocal Vieta and the block product, recognising the slice polynomial's coefficient;
5. homogeneity, carrying the symmetric function past the degreewise component `chernOf` takes.

At stage `0` of the tower `dd` is the empty family, `hdd` is vacuous, the base is a point and the
slice polynomial is `1`; the composition is uniform and needs no case split.

## Main declarations

* `Gen.splitRelation_V` — the split relation for `V` at rank `n`.
* `Gen.lineEulerOf_vLineYBundle_inl`, `Gen.lineEulerOf_vLineYBundle_inr` — the roots.
* `Gen.vRootE`, `Gen.vRootE_equiv` — the roots as Euler classes of the flat family.
* `Gen.VSliceValue` — **the value statement for `V`, at rank `n`**.
* `Gen.vSliceValue_sliceGen` — **the value**, at `LH.sliceGen`.
-/

set_option autoImplicit false

noncomputable section

namespace GroupApproximation
namespace CharClass
namespace Gen

open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.CharClass.Bundle
open GroupApproximation.CharClass.LH
open GroupApproximation.CharClass.LHCast

set_option linter.unusedSectionVars false

variable {ℓ : ℕ}

/-! ## 1. The split relation -/

/-- **The split relation for `V = 𝟏^{n+1} ⊕ H`.**  The roots are a parameter agreeing with the
Euler classes of the flat family of lines on the range. -/
theorem splitRelation_V (n : ℕ) (dd : Fin ℓ → ℕ)
    (root : ℕ → Hmod2 (TopCat.of (baseY dd)) 2)
    (hroot : ∀ l, ∀ hl : l < KGen.lixRank n dd,
      root l = lineEulerOf (vLineFlatBundle n dd l) (trace_vLineFlatBundle_lt n dd l hl)) :
    LerayHirschData.SplitRelation
      (lerayHirschData_of_graded
        (lerayHirschGraded_compact (vBundleY n dd) (KGen.lixRank n dd)
          (rank_vBundleY n dd) (kgenLixRank_pos n dd)))
      (KGen.lixRank n dd) root :=
  splitRelation_of_sum_lt (vBundleY n dd) (KGen.lixRank n dd) (kgenLixRank_pos n dd)
    (rank_vBundleY n dd) (vLineFlatBundle n dd) (trace_vLineFlatBundle_lt n dd)
    (sum_vLineFlatBundle n dd) root hroot

/-! ## 2. The roots -/

/-- **The constant summands contribute a root of zero.**  Their line does not depend on the
base point at all. -/
theorem lineEulerOf_vLineYBundle_inl (n : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (n + 1)) :
    lineEulerOf (vLineYBundle n (Sum.inl i : Fin (n + 1) ⊕ HBlk dd))
        (trace_vLineYBundle n (Sum.inl i)) = 0 :=
  lineEulerOf_const _ _ (fun _ _ => rfl)

/-- **A block line contributes the generator of its factor.**  The line in block `β` is the
tautological line of `ℂP^{dd β.1}` pushed into the block (`vLineYBundle_inr_eq`), and the three
`lineEulerOf` facts evaluate it. -/
theorem lineEulerOf_vLineYBundle_inr (n : ℕ) {dd : Fin ℓ → ℕ} (β : HBlk dd)
    (hd : 1 ≤ dd β.1) :
    lineEulerOf (vLineYBundle n (Sum.inr β)) (trace_vLineYBundle n (Sum.inr β))
      = pull (cmap (LH.evalFactor dd β.1)) 2 (cpGen (dd β.1) hd) := by
  refine (LH.lineEulerOf_congr (vLineYBundle_inr_eq n β) _
    (CPn.trace_pushforward_one (blockEmb n β) (blockEmb_injective n β) (LH.cpTautY dd β.1)
      (LH.trace_cpTautY dd β.1))).trans ?_
  refine (LH.lineEulerOf_pushforward (blockEmb n β) (blockEmb_injective n β)
    (LH.cpTautY dd β.1) (LH.trace_cpTautY dd β.1)).trans ?_
  refine (LH.lineEulerOf_comap (LH.evalFactor dd β.1) (cpTaut (dd β.1))
    (trace_cpTaut (dd β.1))).trans ?_
  exact congrArg (pull (cmap (LH.evalFactor dd β.1)) 2) (LH.lineEulerOf_cpTaut (dd β.1) hd)

/-- **Every block line over the factor `j` has `LH.sliceGen dd hdd j` as its class**, so the
slice polynomial sees that generator with multiplicity `dd j`. -/
theorem sliceGen_eq_rootN (n : ℕ) (dd : Fin ℓ → ℕ) (hdd : ∀ j, 0 < dd j) (β : HBlk dd) :
    TotalH.of (KnTwo.YTop (baseY dd)) 2
        (lineEulerOf (vLineYBundle n (Sum.inr β)) (trace_vLineYBundle n (Sum.inr β)))
      = LH.sliceGen dd hdd β.1 :=
  congrArg (TotalH.of (KnTwo.YTop (baseY dd)) 2) (lineEulerOf_vLineYBundle_inr n β (hdd β.1))

/-- The roots of `V`, as the Euler classes of the flat family. -/
def vRootE (n : ℕ) (dd : Fin ℓ → ℕ) (l : ℕ) : Hmod2 (TopCat.of (baseY dd)) 2 :=
  lineEulerOf (vLineFlatBundle n dd l) (fun y => trace_vLineFlatBundle n dd l y)

/-- At an index coming from the block type, the root is the block line's Euler class. -/
theorem vRootE_equiv (n : ℕ) (dd : Fin ℓ → ℕ) (k : Fin (n + 1) ⊕ HBlk dd) :
    vRootE n dd ((vIndexEquiv n dd k : Fin (KGen.lixRank n dd)) : ℕ)
      = lineEulerOf (vLineYBundle n k) (trace_vLineYBundle n k) := by
  refine LH.lineEulerOf_congr ?_ _ _
  refine congrArg (vLineYBundle n) ?_
  have hlt : ((vIndexEquiv n dd k : Fin (KGen.lixRank n dd)) : ℕ) < KGen.lixRank n dd :=
    (vIndexEquiv n dd k).isLt
  have h : (⟨((vIndexEquiv n dd k : Fin (KGen.lixRank n dd)) : ℕ) % KGen.lixRank n dd,
      Nat.mod_lt _ (kgenLixRank_pos n dd)⟩ : Fin (KGen.lixRank n dd)) = vIndexEquiv n dd k :=
    Fin.ext (Nat.mod_eq_of_lt hlt)
  rw [h]
  exact (vIndexEquiv n dd).symm_apply_apply k

/-! ## 3. The value -/

/-- **The value of the mod-2 Chern classes of `V = 𝟏^{n+1} ⊕ H` on the projective base.**
Mentions no mapping torus and no clutching map.  At `n = 2` it is `CharClass.VSliceValue` up to
the spelling of the rank and of its positivity proof. -/
def VSliceValue (n : ℕ) (dd : Fin ℓ → ℕ) (gen : Fin ℓ → TotalH (KnTwo.YTop (baseY dd))) :
    Prop :=
  ∀ q : ℕ, TotalH.of (KnTwo.YTop (baseY dd)) (2 * q)
      (LH.chernOf (vBundleY n dd) (KGen.lixRank n dd) (rank_vBundleY n dd)
        (kgenLixRank_pos n dd) q)
    = (sliceClass (Finset.univ : Finset (Fin ℓ)) gen dd).coeff q

/-- **The value of the Chern classes of `V`, at sphere rank `n`.** -/
theorem vSliceValue_sliceGen (n : ℕ) (dd : Fin ℓ → ℕ) (hdd : ∀ j, 0 < dd j) :
    VSliceValue n dd (LH.sliceGen dd hdd) := by
  intro q
  set D := lerayHirschData_of_graded
    (lerayHirschGraded_compact (vBundleY n dd) (KGen.lixRank n dd)
      (rank_vBundleY n dd) (kgenLixRank_pos n dd)) with hD
  -- the split relation, at the Euler-class roots
  have hrel : D.SplitRelation (KGen.lixRank n dd) (vRootE n dd) :=
    splitRelation_V n dd (vRootE n dd) (fun _ _ => rfl)
  -- the factorisation
  have hsplit := D.splitPoly_of_splitRelation D (𝟙 _) (𝟙 _) (by simp) (by simp)
    (KGen.lixRank n dd) rfl rfl (vRootE n dd) hrel
  -- the Chern class is the elementary symmetric function of the roots
  have hchern : D.chern q
      = esymmOn (Finset.range (KGen.lixRank n dd))
          (fun l => TotalH.of (TopCat.of (baseY dd)) 2 (vRootE n dd l)) q := by
    have h := chern_split_of_splitPoly D (𝟙 _) (KGen.lixRank n dd) rfl (vRootE n dd) hsplit q
    rwa [ThomChern.totalMap_id] at h
  -- the slice polynomial's coefficient is the same symmetric function
  have hcoeff : (sliceClass (Finset.univ : Finset (Fin ℓ)) (LH.sliceGen dd hdd) dd).coeff q
      = esymmOn (Finset.range (KGen.lixRank n dd))
          (fun l => TotalH.of (TopCat.of (baseY dd)) 2 (vRootE n dd l)) q := by
    rw [← coeff_prod_one_add_C_mul_X,
      prod_range_of_equiv (KGen.lixRank n dd) (vIndexEquiv n dd)
        (fun k => 1 + Polynomial.C (TotalH.of (TopCat.of (baseY dd)) 2
          (lineEulerOf (vLineYBundle n k) (trace_vLineYBundle n k))) * Polynomial.X)
        (fun l => 1 + Polynomial.C (TotalH.of (TopCat.of (baseY dd)) 2
          (vRootE n dd l)) * Polynomial.X)
        (fun k => by rw [vRootE_equiv]),
      prod_blocks_eq_sliceClass n dd (LH.sliceGen dd hdd) _
        (fun i => by rw [lineEulerOf_vLineYBundle_inl n dd i, map_zero])
        (fun b => sliceGen_eq_rootN n dd hdd b)]
  -- assemble
  show TotalH.of (TopCat.of (baseY dd)) (2 * q)
      (TotalH.component (TopCat.of (baseY dd)) (2 * q) (D.chern q)) = _
  rw [hchern, hcoeff, of_component_esymmOn]

end Gen

/-! Audited on every build. -/

#audit_axioms Gen.splitRelation_V
#audit_axioms Gen.vSliceValue_sliceGen

end CharClass
end GroupApproximation
