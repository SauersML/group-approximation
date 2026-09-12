import GroupApproximation.CharClass.SteenrodFourfoldBEdgeCases

/-!
# Composite `B` as a natural transformation

The chain-map identity is now read against the source complex itself.  The source
differential has two halves, and `B` sends each to what the identity produces: the
`(1 + t)` half to the value plus its block swap, the boundary half to the sum over
the faces.  Which halves are present depends on where the generator sits, and the
three positions are exactly the three cases already proved.

The packaging then mirrors `cc-cartan`'s `compACx` and `compA` line for line, so
that the comparison consumes the two composites the same way.

## Main results

* `compBOfW`, `compBOfS` — the value of `B` on each half of the differential.
* `tensorD_compB` — **the chain-map condition** against `wDiff`.
* `compBCx`, `compBNat` — **the second composite**, on one space and as a natural
  transformation `src singularBoundary ⟶ four`.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial SimplexCategory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-! ## The block swap is the action of the generator -/

theorem four_groupRingGen_smul (X : TopCat.{0}) (k : ℕ)
    (y : TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2) :
    (groupRingGen : GroupRingZ2) • y = tenSwap (pairFreeCx X) k y :=
  moduleOfInvolution_smul (tenSwap (pairFreeCx X) k) (tenSwap_mul_self (pairFreeCx X) k) y

theorem four_one_add_gen_smul (X : TopCat.{0}) (k : ℕ)
    (y : TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2) :
    ((1 : GroupRingZ2) + groupRingGen) • y = y + tenSwap (pairFreeCx X) k y := by
  rw [add_smul, one_smul, four_groupRingGen_smul]

/-! ## The value of `B` on each half of the source differential -/

/-- On the `(1 + t)` half: the value one resolution step down, plus its block
swap.  Absent exactly when the resolution index is already `0`. -/
def compBOfW (X : TopCat.{0}) (k : ℕ) :
    ∀ n : Fin (k + 2), singularSimplices X n.val →
      (TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2) :=
  Fin.lastCases
    (motive := fun n : Fin (k + 2) => singularSimplices X n.val →
      (TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2))
    (fun _ => 0)
    (fun j σ => compBGen X k (k - j.val) σ
      + tenSwap (pairFreeCx X) k (compBGen X k (k - j.val) σ))

theorem compBOfW_last (X : TopCat.{0}) (k : ℕ)
    (σ : singularSimplices X (Fin.last (k + 1)).val) :
    compBOfW X k (Fin.last (k + 1)) σ = 0 := by
  rw [compBOfW, Fin.lastCases_last]

theorem compBOfW_castSucc (X : TopCat.{0}) (k : ℕ) (j : Fin (k + 1))
    (σ : singularSimplices X (Fin.castSucc j).val) :
    compBOfW X k (Fin.castSucc j) σ
      = compBGen X k (k - j.val) σ
        + tenSwap (pairFreeCx X) k (compBGen X k (k - j.val) σ) := by
  rw [compBOfW, Fin.lastCases_castSucc]

/-- On the boundary half: the sum of the values at the faces.  Absent exactly in
simplex degree `0`. -/
def compBOfS (X : TopCat.{0}) (k : ℕ) :
    ∀ n : Fin (k + 2), singularSimplices X n.val →
      (TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2) :=
  Fin.cases
    (motive := fun n : Fin (k + 2) => singularSimplices X n.val →
      (TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2))
    (fun _ => 0)
    (fun m σ => ∑ jj : Fin (m.val + 2),
      compBGen X k (k - m.val) (faceSimplex X m.val jj σ))

theorem compBOfS_zero (X : TopCat.{0}) (k : ℕ)
    (σ : singularSimplices X (0 : Fin (k + 2)).val) : compBOfS X k 0 σ = 0 := by
  rw [compBOfS, Fin.cases_zero]

theorem compBOfS_succ (X : TopCat.{0}) (k : ℕ) (m : Fin (k + 1))
    (σ : singularSimplices X (Fin.succ m).val) :
    compBOfS X k (Fin.succ m) σ
      = ∑ jj : Fin (m.val + 2),
          compBGen X k (k - m.val) (faceSimplex X m.val jj σ) := by
  rw [compBOfS, Fin.cases_succ]

/-! ## The `(1 + t)` half at a point -/

/-- On a point the block swap fixes `B`, so the `(1 + t)` half vanishes.  In
positive total degree both terms vanish separately; in degree `0` neither does,
and it is the symmetry of the diagonal of a point that saves the identity. -/
theorem innerSwapFour_compBPreGen_pt (X : TopCat.{0}) (σ : singularSimplices X 0) :
    innerSwapFour X 0 (compBPreGen X 0 0 σ) = compBPreGen X 0 0 σ := by
  have hlc : Finsupp.linearCombination (ZMod 2) (compBPre X 0 0 0 0)
      (Finsupp.single (⟨⟨(0, 0), rfl⟩, (σ, σ)⟩ : PairIdx X 0) 1)
      = compBPre X 0 0 0 0 (⟨⟨(0, 0), rfl⟩, (σ, σ)⟩ : PairIdx X 0) := by
    simp
  have hval : compBPreGen X 0 0 σ
      = padFour X 0 0 0 (phiAtDeg X 0 0 σ) ((groupRingGen ^ 0) • phiAtDeg X 0 0 σ) := by
    rw [compBPreGen_eq, Finset.sum_range_one, phiZero_degree_zero]
    exact hlc
  rw [hval, tenHom_swapHom_padFour, swapEnd_phiAtDeg_degree_zero, swapEnd_smul_pow,
    smul_succ_phiAtDeg_pt]

theorem compBGen_add_tenSwap_pt (X : TopCat.{0}) (k : ℕ) (σ : singularSimplices X 0) :
    compBGen X k k σ + tenSwap (pairFreeCx X) k (compBGen X k k σ) = 0 := by
  cases k with
  | zero =>
      have hsym : tenSwap (pairFreeCx X) 0 (compBGen X 0 0 σ) = compBGen X 0 0 σ := by
        rw [compBGen_eq_midSwap, ← midSwap_innerSwap, innerSwapFour_compBPreGen_pt]
      rw [hsym]
      exact add_self_zmod2 _
  | succ k' =>
      rw [compBGen_pt_eq_zero X (k' + 1) (k' + 1) σ (Nat.succ_pos k'), map_zero, add_zero]

/-! ## The chain-map condition on a generator -/

/-- **The chain-map condition on one generator** `e_{k+1-n} ⊗ σ` of the source.
The three cases are the three positions the generator can occupy: simplex degree
`0`, resolution index `0`, and everything else. -/
theorem tensorD_compBGen_gen (X : TopCat.{0}) (k : ℕ) (n : Fin (k + 2))
    (σ : singularSimplices X n.val) :
    tensorD (pairFreeCx X) (pairFreeCx X) k (compBGen X (k + 1) (k + 1 - n.val) σ)
      = compBOfW X k n σ + compBOfS X k n σ := by
  revert σ
  induction n using Fin.cases with
  | zero =>
      intro σ
      have hW : compBOfW X k (0 : Fin (k + 2)) σ
          = compBGen X k (k - (0 : Fin (k + 1)).val) σ
            + tenSwap (pairFreeCx X) k (compBGen X k (k - (0 : Fin (k + 1)).val) σ) :=
        compBOfW_castSucc X k 0 σ
      have hS : compBOfS X k (0 : Fin (k + 2)) σ = 0 := compBOfS_zero X k σ
      have hzero : compBGen X (k + 1) (k + 1 - (0 : Fin (k + 2)).val) σ = 0 :=
        compBGen_pt_eq_zero X (k + 1) (k + 1 - (0 : Fin (k + 2)).val) σ
          (by
            have hv : ((0 : Fin (k + 2)) : ℕ) = 0 := rfl
            omega)
      rw [hW, hS, add_zero, hzero, map_zero]
      exact (compBGen_add_tenSwap_pt X k σ).symm
  | succ m =>
      induction m using Fin.lastCases with
      | last =>
          intro σ
          have hW : compBOfW X k (Fin.succ (Fin.last k)) σ = 0 := compBOfW_last X k σ
          have hS : compBOfS X k (Fin.succ (Fin.last k)) σ
              = ∑ jj : Fin ((Fin.last k).val + 2),
                  compBGen X k (k - (Fin.last k).val)
                    (faceSimplex X (Fin.last k).val jj σ) :=
            compBOfS_succ X k (Fin.last k) σ
          have hidx : compBGen X (k + 1) (k + 1 - (Fin.succ (Fin.last k)).val) σ
              = compBGen X (k + 1) 0 σ :=
            congrArg (fun i => compBGen X (k + 1) i σ)
              (show k + 1 - (Fin.succ (Fin.last k)).val = 0 by
                have hv : (Fin.succ (Fin.last k)).val = k + 1 := rfl
                omega)
          have hsub : k - (Fin.last k).val = 0 := Nat.sub_self k
          rw [hidx, hW, hS, zero_add, hsub]
          exact tensorD_compBGen_zero X k k σ
      | cast j =>
          intro σ
          have hjk : j.val < k := j.isLt
          have hv1 : (Fin.succ (Fin.castSucc j)).val = j.val + 1 := rfl
          have hv2 : (Fin.succ j).val = j.val + 1 := rfl
          have hv3 : (Fin.castSucc j).val = j.val := rfl
          have hW : compBOfW X k (Fin.succ (Fin.castSucc j)) σ
              = compBGen X k (k - (Fin.succ j).val) σ
                + tenSwap (pairFreeCx X) k (compBGen X k (k - (Fin.succ j).val) σ) :=
            compBOfW_castSucc X k (Fin.succ j) σ
          have hS : compBOfS X k (Fin.succ (Fin.castSucc j)) σ
              = ∑ jj : Fin ((Fin.castSucc j).val + 2),
                  compBGen X k (k - (Fin.castSucc j).val)
                    (faceSimplex X (Fin.castSucc j).val jj σ) :=
            compBOfS_succ X k (Fin.castSucc j) σ
          have hidx : compBGen X (k + 1) (k + 1 - (Fin.succ (Fin.castSucc j)).val) σ
              = compBGen X (k + 1) ((k - (Fin.succ j).val) + 1) σ :=
            congrArg (fun i => compBGen X (k + 1) i σ)
              (show k + 1 - (Fin.succ (Fin.castSucc j)).val
                  = (k - (Fin.succ j).val) + 1 by rw [hv1, hv2]; omega)
          have hidx2 : k - (Fin.castSucc j).val = (k - (Fin.succ j).val) + 1 := by
            rw [hv2, hv3]; omega
          rw [hidx, hW, hS, hidx2]
          exact tensorD_compBGen_chain X k (k - (Fin.succ j).val) j.val σ

/-! ## The chain-map condition against the source complex -/

theorem compB_wDiffW (X : TopCat.{0}) (k : ℕ) (n : Fin (k + 2))
    (φ : stdSimplexTop n.val ⟶ X) :
    compB X k (wDiffW X k n φ) = compBOfW X k n ((simplexEquiv X n.val).symm φ) := by
  revert φ
  induction n using Fin.lastCases with
  | last =>
      intro φ
      rw [wDiffW_last, compBOfW_last]
      exact map_zero (compB X k)
  | cast j =>
      intro φ
      rw [wDiffW_castSucc, compBOfW_castSucc, map_smul, compB_single, one_smul,
        four_one_add_gen_smul]
      rfl

theorem compB_wDiffS (X : TopCat.{0}) (k : ℕ) (n : Fin (k + 2))
    (φ : stdSimplexTop n.val ⟶ X) :
    compB X k (wDiffS singularBoundary X k n φ)
      = compBOfS X k n ((simplexEquiv X n.val).symm φ) := by
  revert φ
  induction n using Fin.cases with
  | zero =>
      intro φ
      rw [wDiffS_zero, compBOfS_zero]
      exact map_zero (compB X k)
  | succ m =>
      intro φ
      have hbd : singularBoundary.bd X m.val (Finsupp.single φ (1 : GroupRingZ2))
          = ∑ i : Fin (m.val + 2),
              Finsupp.single
                (simplexEquiv X m.val
                  (faceSimplex X m.val i ((simplexEquiv X (m.val + 1)).symm φ)))
                (1 : GroupRingZ2) := by
        rw [singularBoundary_bd, bdHom_apply, Finsupp.mapDomain_single, bdU_single,
          mapDomain_finset_sum]
        exact Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_single
      rw [wDiffS_succ, compBOfS_succ, hbd, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, compB_single]
      exact one_smul _ _

theorem compB_wDiffGen (X : TopCat.{0}) (k : ℕ) (n : Fin (k + 2))
    (φ : stdSimplexTop n.val ⟶ X) :
    compB X k (wDiffGen singularBoundary X k n φ)
      = compBOfW X k n ((simplexEquiv X n.val).symm φ)
        + compBOfS X k n ((simplexEquiv X n.val).symm φ) := by
  rw [wDiffGen, map_add, compB_wDiffW, compB_wDiffS]

theorem tensorD_compB_single (X : TopCat.{0}) (k : ℕ)
    (b : Σ n : Fin (k + 2), stdSimplexTop n.val ⟶ X) :
    tensorD (pairFreeCx X) (pairFreeCx X) k (compB X (k + 1) (Finsupp.single b 1))
      = compB X k (wDiff singularBoundary X k (Finsupp.single b 1)) := by
  rw [compB_single, one_smul, wDiff_single, compB_wDiffGen]
  exact tensorD_compBGen_gen X k b.1 ((simplexEquiv X b.1.val).symm b.2)

/-- **Composite `B` is a chain map.**  `∂ ∘ B = B ∘ d`, with `d` the differential
of `W ⊗ S(X)` and `∂` that of the fourfold. -/
theorem tensorD_compB (X : TopCat.{0}) (k : ℕ) (y : WTensorSMod X (k + 1)) :
    tensorD (pairFreeCx X) (pairFreeCx X) k (compB X (k + 1) y)
      = compB X k (wDiff singularBoundary X k y) := by
  classical
  refine Finsupp.induction_linear y ?_ ?_ ?_
  · simp
  · intro u v hu hv
    rw [map_add, map_add, hu, hv, map_add]
    exact (map_add (compB X k) _ _).symm
  · intro b c
    have hs : (Finsupp.single b c : WTensorSMod X (k + 1))
        = c • Finsupp.single b (1 : GroupRingZ2) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hs, map_smul, fourD_smul, map_smul, map_smul]
    exact congrArg (fun z => c • z) (tensorD_compB_single X k b)

/-! ## The composite -/

/-- The second composite on one space, as a map of complexes. -/
noncomputable def compBCx (X : TopCat.{0}) :
    srcComplex singularBoundary X ⟶ fourCx X where
  f k := ModuleCat.ofHom (compB X k)
  comm' := by
    rintro i j (rfl : j + 1 = i)
    rw [srcComplex_d, fourCx_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    show tensorD (pairFreeCx X) (pairFreeCx X) j (compB X (j + 1) y)
      = compB X j (wDiff singularBoundary X j y)
    exact tensorD_compB X j y

/-- **The second composite of the Cartan comparison**, as a natural
transformation. -/
noncomputable def compBNat : src singularBoundary ⟶ four where
  app X := compBCx X
  naturality {X Y} f := by
    refine HomologicalComplex.hom_ext _ _ fun k => ?_
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    show compB Y k (Finsupp.lmapDomain GroupRingZ2 GroupRingZ2 (srcMapIdx f k) y)
      = tenHom (pairHom f) (pairHom f) k (compB X k y)
    exact (compB_naturality f k y).symm

end

end Steenrod
end CharClass
end GroupApproximation
