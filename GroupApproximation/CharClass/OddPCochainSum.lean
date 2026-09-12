import GroupApproximation.CharClass.OddPCochain

/-!
# The simplicial half of the differential of `W ⊗ C(X)`, generator by generator

`oddDiffS_succ_eq_sum` writes the simplicial half of the differential on a generator
`e_{k−m} ⊗ σ` (simplex degree `m + 1`) as the signed sum of the generators on the faces of `σ`:

  `(−1)^{k−m} Σ_i (−1)^i · (e_{k−m} ⊗ ∂_i σ)`.

`OddPCochain.lean` evaluates this half only through the diagonal (`oddEvalHom_oddDiffS_succ`).  The
element-level form is what a consumer needs when the half is multiplied by a group-ring scalar
before evaluation, as in the additivity of the reduced powers.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

/-- **The simplicial half on a generator, as a sum of generators.** -/
theorem oddDiffS_succ_eq_sum (p : ℕ) {X : TopCat.{0}} (k : ℕ) (m : Fin (k + 1))
    (σ : singularSimplices X (m.val + 1)) :
    oddDiffS p (oddSingularBoundary p) X k (Fin.succ m) (simplexEquiv X (m.val + 1) σ)
      = ∑ i : Fin (m.val + 2), ((-1 : GroupRingZMod p) ^ (k - m.val) * (-1) ^ (i : ℕ)) •
          Finsupp.single (⟨m, simplexEquiv X m.val (faceSimplex X m.val i σ)⟩ : WSIndex k X) 1 := by
  rw [oddDiffS_succ]
  -- The relabelling of simplices, on the singular chains of the face degree.
  let L : ((singFreeR (GroupRingZMod p)).obj X).X m.val →+ OddWTensor p k X :=
    (Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p)
        (fun τ : stdSimplexTop m.val ⟶ X => (⟨m, τ⟩ : WSIndex k X))).toAddMonoidHom.comp
      (Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p)
        (simplexEquiv X m.val)).toAddMonoidHom
  have hd := congrArg L (singFreeR_d_single (GroupRingZMod p) X m.val σ)
  rw [map_sum] at hd
  have hsingle : Finsupp.mapDomain (simplexEquiv X (m.val + 1)).symm
      (Finsupp.single (simplexEquiv X (m.val + 1) σ) (1 : GroupRingZMod p))
        = Finsupp.single σ 1 := by
    rw [Finsupp.mapDomain_single, Equiv.symm_apply_apply]
  have hb : Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p)
        (fun τ : stdSimplexTop m.val ⟶ X => (⟨m, τ⟩ : WSIndex k X))
        ((oddSingularBoundary p).bd X m.val
          (Finsupp.single (simplexEquiv X (m.val + 1) σ) (1 : GroupRingZMod p)))
      = ∑ i : Fin (m.val + 2), (-1 : GroupRingZMod p) ^ (i : ℕ) •
          Finsupp.single (⟨m, simplexEquiv X m.val (faceSimplex X m.val i σ)⟩ : WSIndex k X) 1 := by
    refine Eq.trans ?_ (hd.trans (Finset.sum_congr rfl fun i _ => ?_))
    · exact congrArg
        (fun c => L ((((singFreeR (GroupRingZMod p)).obj X).d (m.val + 1) m.val).hom c)) hsingle
    · rw [map_zsmul, ← Int.cast_smul_eq_zsmul (GroupRingZMod p), Int.cast_pow, Int.cast_neg,
        Int.cast_one]
      congr 1
      show Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p)
          (fun τ : stdSimplexTop m.val ⟶ X => (⟨m, τ⟩ : WSIndex k X))
          (Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p) (simplexEquiv X m.val)
            (Finsupp.single (faceSimplex X m.val i σ) 1)) = _
      rw [Finsupp.lmapDomain_apply (simplexEquiv X m.val), Finsupp.mapDomain_single,
        Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rw [hb, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]

#audit_axioms oddDiffS_succ_eq_sum

end

end GroupApproximation.CharClass
