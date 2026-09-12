import GroupApproximation.CharClass.OddPCompB
import GroupApproximation.CharClass.OddPCochain
import GroupApproximation.CharClass.CupOneComm

/-!
# The Cartan comparison at odd `p`, evaluated

The two composites `compA` and `compB` (`OddPCompA.lean`, `OddPCompB.lean`) are natural
`F_p[ℤ/p]`-linear chain maps `W ⊗ C(X) → C(X)^{⊗2p}` that agree in degree `0`.  The source is free
on the standard simplices and the target is acyclic on them, so the acyclic-models theorem gives a
natural equivariant chain homotopy between them (`compHomotopy`).

This file evaluates that homotopy against the functional `u ⊗ v ⊗ u ⊗ v ⊗ ⋯` of two cocycles.

* Boundaries of the target die, because every slot of the functional is a cocycle.
* The resolution half of the source differential dies.  The group ring acts on the target through
  `T²`, the functional is invariant under `T²`, so an element `λ` of the group ring acts as its
  augmentation, and both `grS` and `grNorm` have augmentation `0` in `F_p`.
* The simplicial half is the coboundary of the homotopy's evaluation.

So, at a generator of simplex degree `m + 1`, the two composites evaluate to values differing by
`(−1)^{W-index}` times a coboundary.  At simplex degree `0` they are equal.  Stated at a variable
simplex degree, this gives equal classes with no degree cast anywhere.  The first composite's
cochain is `D_i(u ⌣ v)` (`cartanCochainA_eq_oddD`).

## Main results

* `compHomotopy` — **the natural homotopy between the two composites.**
* `tupEval_cartanFun_galAlgHomP` — the group ring acts on the evaluation through its augmentation.
* `cartanCochainA_succ_eq`, `cartanCochainA_zero_eq` — the comparison at cochain level.
* `cocycleClassK_cartanCochainA` — **the comparison at class level.**
* `cartanCochainA_eq_oddD` — the first composite's cochain is `D_i(u ⌣ v)`.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

variable (p : ℕ) [NeZero p] [Fact p.Prime]

/-! ## 1. The two composites are naturally homotopic -/

/-- **The two composites agree in degree `0`**: both send `e_0 ⊗ x` to `x^{⊗2p}`. -/
theorem compA_f_zero_eq_compB (X : TopCat.{0}) : ((compA p).app X).f 0 = ((compB p).app X).f 0 := by
  letI := tupModule p X (2 * p) 0 2 (dvd_two_mul_self p)
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext'
  intro q
  apply LinearMap.ext_ring
  obtain ⟨n, x⟩ := q
  obtain rfl : n = 0 := Fin.fin_one_eq_zero n
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [compA_zero, compB_zero]

/-- **The natural equivariant chain homotopy between the two composites.** -/
def compHomotopy :
    NaturalHomotopy (oddSrc p (oddSingularBoundary p)) (oddTgt p (2 * p) 2 (dvd_two_mul_self p))
      (compA p) (compB p) :=
  acyclicModelsHomotopy (oddSrcFree p (oddSingularBoundary p))
    (oddTgt_acyclicOnModels p (2 * p) 2 (dvd_two_mul_self p)) (compA p) (compB p)
    (compA_f_zero_eq_compB p)

/-! ## 2. The evaluating functional -/

variable {X : TopCat.{0}} (q q' : ℕ) (u : singularCochainGroup (ZMod p) X q)
  (v : singularCochainGroup (ZMod p) X q')

/-- **The evaluating functional** `u ⊗ v ⊗ u ⊗ v ⊗ ⋯` on `2p` slots. -/
def cartanFun : Fin (2 * p) → ∀ n : ℕ, singularCochainGroup (ZMod p) X n :=
  tupInterleave p (fun _ => Pi.single q u) (fun _ => Pi.single q' v)

omit [Fact p.Prime] in
theorem cartanFun_apply (j : Fin (2 * p)) :
    cartanFun p q q' u v j = if j.val % 2 = 0 then Pi.single q u else Pi.single q' v := by
  unfold cartanFun tupInterleave
  split_ifs <;> rfl

omit [Fact p.Prime] in
/-- Every slot of the functional is a cocycle. -/
theorem gCoboundary_cartanFun (hu : cochainCoboundary (ZMod p) X q u = 0)
    (hv : cochainCoboundary (ZMod p) X q' v = 0) (j : Fin (2 * p)) :
    gCoboundary (ZMod p) X (cartanFun p q q' u v j) = 0 := by
  rw [cartanFun_apply]
  split_ifs
  · exact gCoboundary_piSingle_eq_zero (ZMod p) u hu
  · exact gCoboundary_piSingle_eq_zero (ZMod p) v hv

omit [NeZero p] [Fact p.Prime] in
/-- The slot degrees of the functional sum to `m (q + q')` over `2m` slots. -/
theorem sum_range_parity (m : ℕ) :
    ∑ j ∈ Finset.range (2 * m), (if j % 2 = 0 then q else q') = m * (q + q') := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      if_pos (by omega : (2 * m) % 2 = 0), if_neg (by omega : ¬ (2 * m + 1) % 2 = 0)]
    ring

omit [Fact p.Prime] in
/-- Rotating by one slot flips the parity of the slot index, on an even number of slots. -/
theorem finRotate_val_mod_two (j : Fin (2 * p)) :
    ((finRotate (2 * p) j : Fin (2 * p)) : ℕ) % 2 = (j.val + 1) % 2 := by
  rw [finRotate_val_eq, Nat.mod_mod_of_dvd _ (dvd_mul_right 2 p)]

omit [Fact p.Prime] in
/-- The functional is invariant under the rotation by two slots. -/
theorem cartanFun_finRotate_sq (j : Fin (2 * p)) :
    cartanFun p q q' u v (finRotate (2 * p) (finRotate (2 * p) j)) = cartanFun p q q' u v j := by
  have h : ((finRotate (2 * p) (finRotate (2 * p) j) : Fin (2 * p)) : ℕ) % 2 = j.val % 2 := by
    rw [finRotate_val_mod_two, Nat.add_mod, finRotate_val_mod_two]
    omega
  rw [cartanFun_apply, cartanFun_apply, h]

omit [Fact p.Prime] in
/-- **The functional does not see the rotation by two slots**, at odd `p`.  The product is
reindexed by the rotation, and on its support the Koszul exponents of the two single rotations sum
to `q (p(q+q') − q) + q' (p(q+q') − q')`, which is even. -/
theorem tupEval_cartanFun_tupT_sq (hp : Odd p) (k : ℕ) (z : tupMod (ZMod p) X (2 * p) k) :
    tupEval (ZMod p) X (2 * p) k (cartanFun p q q' u v) ((tupT (ZMod p) X (2 * p) k ^ 2) z)
      = tupEval (ZMod p) X (2 * p) k (cartanFun p q q' u v) z := by
  have hL : (tupEval (ZMod p) X (2 * p) k (cartanFun p q q' u v)).comp
      (tupT (ZMod p) X (2 * p) k ^ 2) = tupEval (ZMod p) X (2 * p) k (cartanFun p q q' u v) := by
    apply Finsupp.lhom_ext'
    intro t
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, pow_two, Module.End.mul_apply]
    rw [tupT_single, map_smul, tupT_single, map_smul, map_smul, tupEval_single, tupEval_single,
      smul_eq_mul, smul_eq_mul]
    -- reindex the product by the rotation by two
    have hprod : ∏ j, tagEvalG (ZMod p) (cartanFun p q q' u v j)
        ((tupRotIdx X (tupRotIdx X t)).1 j) = ∏ j, tagEvalG (ZMod p) (cartanFun p q q' u v j) (t.1 j) := by
      have hre := Equiv.prod_comp (finRotate (2 * p) * finRotate (2 * p))
        (fun j => tagEvalG (ZMod p) (cartanFun p q q' u v j) (t.1 j))
      refine Eq.trans ?_ hre
      refine Finset.prod_congr rfl fun j _ => ?_
      show tagEvalG (ZMod p) (cartanFun p q q' u v j) (t.1 (finRotate (2 * p) (finRotate (2 * p) j)))
        = tagEvalG (ZMod p) (cartanFun p q q' u v (finRotate (2 * p) (finRotate (2 * p) j)))
            (t.1 (finRotate (2 * p) (finRotate (2 * p) j)))
      rw [cartanFun_finRotate_sq]
    rw [hprod]
    by_cases hP : ∏ j, tagEvalG (ZMod p) (cartanFun p q q' u v j) (t.1 j) = 0
    · rw [hP, mul_zero, mul_zero]
    · -- on the support every slot has the degree of its functional
      have hdeg : ∀ j : Fin (2 * p), (t.1 j).1 = if j.val % 2 = 0 then q else q' := by
        intro j
        by_contra hj
        refine hP (Finset.prod_eq_zero (Finset.mem_univ j) ?_)
        refine tagEvalG_of_eq_zero (ZMod p) _ (t.1 j) ?_
        rw [cartanFun_apply]
        split_ifs with h
        · rw [if_pos h] at hj
          exact Pi.single_eq_of_ne hj u
        · rw [if_neg h] at hj
          exact Pi.single_eq_of_ne hj v
      obtain ⟨m, hm⟩ := hp
      have hp0 : 0 < 2 * p := by omega
      have htot : ∑ j : Fin (2 * p), (t.1 j).1 = p * (q + q') := by
        rw [Finset.sum_congr rfl fun j _ => hdeg j,
          Fin.sum_univ_eq_sum_range (fun j => if j % 2 = 0 then q else q') (2 * p),
          sum_range_parity]
      have hd0 : tupDeg t.1 0 = q := by
        rw [show (0 : ℕ) = (⟨0, hp0⟩ : Fin (2 * p)).val from rfl, tupDeg_val, hdeg]
        simp
      have hd1 : tupDeg (tupRot t.1) 0 = q' := by
        rw [show (0 : ℕ) = (⟨0, hp0⟩ : Fin (2 * p)).val from rfl, tupDeg_val, tupRot_apply, hdeg,
          finRotate_val_mod_two]
        simp
      have htot' : ∑ j : Fin (2 * p), (tupRot t.1 j).1 = p * (q + q') := by
        rw [tupTot_tupRot, htot]
      have e1 : p * (q + q') - q = 2 * m * q + p * q' := Nat.sub_eq_of_eq_add (by rw [hm]; ring)
      have e2 : p * (q + q') - q' = 2 * m * q' + p * q := Nat.sub_eq_of_eq_add (by rw [hm]; ring)
      have hev : Even (rotExp X t.1 + rotExp X (tupRotIdx X t).1) := by
        show Even (tupDeg t.1 0 * (∑ j : Fin (2 * p), (t.1 j).1 - tupDeg t.1 0)
          + tupDeg (tupRot t.1) 0 * (∑ j : Fin (2 * p), (tupRot t.1 j).1 - tupDeg (tupRot t.1) 0))
        rw [hd0, hd1, htot, htot', e1, e2, hm]
        exact ⟨m * q * q + m * q' * q' + (2 * m + 1) * q * q', by ring⟩
      rw [← mul_assoc, ← pow_add, hev.neg_one_pow, one_mul]
  exact LinearMap.congr_fun hL z

omit [Fact p.Prime] in
/-- **The group ring acts on the evaluation through its augmentation**, the generator acting on the
`2p`-fold power through `T²`. -/
theorem tupEval_cartanFun_galAlgHomP (hp : Odd p) (k : ℕ) (c : GroupRingZMod p)
    (z : tupMod (ZMod p) X (2 * p) k) :
    tupEval (ZMod p) X (2 * p) k (cartanFun p q q' u v)
        (galAlgHomP (tupT (ZMod p) X (2 * p) k ^ 2)
          (tupT_pow_pow p X (2 * p) k 2 (dvd_two_mul_self p)) c z)
      = grAug p c * tupEval (ZMod p) X (2 * p) k (cartanFun p q q' u v) z := by
  induction c using MonoidAlgebra.induction_on with
  | hM g =>
    have hV : galAlgHomP (tupT (ZMod p) X (2 * p) k ^ 2)
        (tupT_pow_pow p X (2 * p) k 2 (dvd_two_mul_self p))
          (MonoidAlgebra.of (ZMod p) (Multiplicative (ZMod p)) g)
        = galEndP (tupT (ZMod p) X (2 * p) k ^ 2)
            (tupT_pow_pow p X (2 * p) k 2 (dvd_two_mul_self p)) g := by
      unfold galAlgHomP
      exact MonoidAlgebra.lift_of _ _
    rw [hV, grAug_of, one_mul]
    show tupEval (ZMod p) X (2 * p) k (cartanFun p q q' u v)
        (((tupT (ZMod p) X (2 * p) k ^ 2) ^ (Multiplicative.toAdd g).val) z) = _
    generalize (Multiplicative.toAdd g).val = n
    induction n generalizing z with
    | zero => rw [pow_zero, Module.End.one_apply]
    | succ n ih => rw [pow_succ', Module.End.mul_apply, tupEval_cartanFun_tupT_sq p q q' u v hp, ih]
  | hadd c₁ c₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂, add_mul]
  | hsmul a c h => simp only [map_smul, LinearMap.smul_apply, h, smul_eq_mul, mul_assoc]

omit [Fact p.Prime] in
theorem grAug_altCoeff (i : ℕ) : grAug p (altCoeff (grS p) (grNorm p) i) = 0 := by
  unfold altCoeff
  split_ifs
  · exact grAug_grS p
  · exact grAug_grNorm p

/-! ## 3. The homotopy, evaluated on a generator -/

/-- **The homotopy identity, evaluated**: boundaries of the target die against cocycles. -/
theorem tupEval_compA_sub_compB (hp : Odd p) (hu : cochainCoboundary (ZMod p) X q u = 0)
    (hv : cochainCoboundary (ZMod p) X q' v = 0) (k : ℕ) (x : OddWTensor p (k + 1) X) :
    tupEval (ZMod p) X (2 * p) (k + 1) (cartanFun p q q' u v) ((((compA p).app X).f (k + 1)).hom x)
      - tupEval (ZMod p) X (2 * p) (k + 1) (cartanFun p q q' u v)
          ((((compB p).app X).f (k + 1)).hom x)
      = tupEval (ZMod p) X (2 * p) (k + 1) (cartanFun p q q' u v)
          (((compHomotopy p).s k X).hom (oddDiff p (oddSingularBoundary p) X k x)) := by
  have h := congrArg (fun g => ModuleCat.Hom.hom g x) ((compHomotopy p).comm_succ k X)
  have hd1 : ((oddSrc p (oddSingularBoundary p)).obj X).d (k + 1) k
      = ModuleCat.ofHom (oddDiff p (oddSingularBoundary p) X k) :=
    oddSrc_obj_d p (oddSingularBoundary p) X k
  have hd2 : ((oddTgt p (2 * p) 2 (dvd_two_mul_self p)).obj X).d (k + 2) (k + 1)
      = tupDHom p X (2 * p) (k + 1) 2 (dvd_two_mul_self p) :=
    oddTgt_obj_d p (2 * p) 2 (dvd_two_mul_self p) X (k + 1)
  simp only [hd1, hd2, ModuleCat.hom_sub, ModuleCat.hom_add, ModuleCat.hom_comp,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    tupDHom_hom_apply] at h
  rw [← map_sub, h, map_add,
    tupEval_tupD_eq_zero (ZMod p) _ (gCoboundary_cartanFun p q q' u v hu hv) (k + 1), add_zero]

/-- The resolution half of the source differential dies in the evaluation. -/
theorem tupEval_homotopy_oddDiffW (hp : Odd p) (k : ℕ) (N : Fin (k + 2))
    (τ : stdSimplexTop N.val ⟶ X) :
    tupEval (ZMod p) X (2 * p) (k + 1) (cartanFun p q q' u v)
      (((compHomotopy p).s k X).hom (oddDiffW p X k N τ)) = 0 := by
  revert τ
  induction N using Fin.lastCases with
  | last =>
    intro τ
    rw [oddDiffW_last, map_zero, map_zero]
  | cast m =>
    intro τ
    letI := tupModule p X (2 * p) (k + 1) 2 (dvd_two_mul_self p)
    rw [oddDiffW_castSucc, map_smul]
    show tupEval (ZMod p) X (2 * p) (k + 1) (cartanFun p q q' u v)
        (galAlgHomP (tupT (ZMod p) X (2 * p) (k + 1) ^ 2)
          (tupT_pow_pow p X (2 * p) (k + 1) 2 (dvd_two_mul_self p))
          (altCoeff (grS p) (grNorm p) (k - m.val))
          (((compHomotopy p).s k X).hom (Finsupp.single (⟨m, τ⟩ : WSIndex k X) 1))) = 0
    rw [tupEval_cartanFun_galAlgHomP p q q' u v hp, grAug_altCoeff p, zero_mul]

/-- The simplicial half of the source differential, evaluated: an alternating sum over faces. -/
theorem tupEval_homotopy_oddDiffS_succ (hp : Odd p) (k : ℕ) (m : Fin (k + 1))
    (σ : singularSimplices X (m.val + 1)) :
    tupEval (ZMod p) X (2 * p) (k + 1) (cartanFun p q q' u v)
        (((compHomotopy p).s k X).hom
          (oddDiffS p (oddSingularBoundary p) X k (Fin.succ m) (simplexEquiv X (m.val + 1) σ)))
      = (-1 : ZMod p) ^ (k - m.val) * ∑ f : Fin (m.val + 2), (-1 : ZMod p) ^ (f : ℕ) *
          tupEval (ZMod p) X (2 * p) (k + 1) (cartanFun p q q' u v)
            (((compHomotopy p).s k X).hom
              (Finsupp.single (⟨m, simplexEquiv X m.val (faceSimplex X m.val f σ)⟩ : WSIndex k X)
                1)) := by
  rw [oddDiffS_succ_eq_sum, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  letI := tupModule p X (2 * p) (k + 1) 2 (dvd_two_mul_self p)
  rw [map_smul]
  show tupEval (ZMod p) X (2 * p) (k + 1) (cartanFun p q q' u v)
      (galAlgHomP (tupT (ZMod p) X (2 * p) (k + 1) ^ 2)
        (tupT_pow_pow p X (2 * p) (k + 1) 2 (dvd_two_mul_self p))
        ((-1 : GroupRingZMod p) ^ (k - m.val) * (-1) ^ (f : ℕ))
        (((compHomotopy p).s k X).hom
          (Finsupp.single (⟨m, simplexEquiv X m.val (faceSimplex X m.val f σ)⟩ : WSIndex k X) 1)))
    = _
  rw [tupEval_cartanFun_galAlgHomP p q q' u v hp, map_mul, map_pow, map_pow, map_neg, map_one,
    mul_assoc]

/-! ## 4. At a variable simplex degree -/

/-- The first composite on the generator of simplex degree `N` in total degree `K`, evaluated. -/
def cartanEvalA (K N : ℕ) (hN : N < K + 1) (σ : singularSimplices X N) : ZMod p :=
  tupEval (ZMod p) X (2 * p) K (cartanFun p q q' u v)
    ((((compA p).app X).f K).hom
      (Finsupp.single (⟨⟨N, hN⟩, simplexEquiv X N σ⟩ : WSIndex K X) (1 : GroupRingZMod p)))

/-- The second composite on the generator of simplex degree `N` in total degree `K`, evaluated. -/
def cartanEvalB (K N : ℕ) (hN : N < K + 1) (σ : singularSimplices X N) : ZMod p :=
  tupEval (ZMod p) X (2 * p) K (cartanFun p q q' u v)
    ((((compB p).app X).f K).hom
      (Finsupp.single (⟨⟨N, hN⟩, simplexEquiv X N σ⟩ : WSIndex K X) (1 : GroupRingZMod p)))

/-- The homotopy on the generator of simplex degree `m` in total degree `k`, evaluated. -/
def cartanEvalH (k m : ℕ) (hm : m < k + 1) (σ : singularSimplices X m) : ZMod p :=
  tupEval (ZMod p) X (2 * p) (k + 1) (cartanFun p q q' u v)
    (((compHomotopy p).s k X).hom
      (Finsupp.single (⟨⟨m, hm⟩, simplexEquiv X m σ⟩ : WSIndex k X) (1 : GroupRingZMod p)))

/-- At simplex degree `0` the two composites evaluate to the same value. -/
theorem cartanEvalA_zero (hp : Odd p) (hu : cochainCoboundary (ZMod p) X q u = 0)
    (hv : cochainCoboundary (ZMod p) X q' v = 0) (k : ℕ) (σ : singularSimplices X 0) :
    cartanEvalA p q q' u v (k + 1) 0 (Nat.succ_pos _) σ
      = cartanEvalB p q q' u v (k + 1) 0 (Nat.succ_pos _) σ := by
  rw [← sub_eq_zero]
  unfold cartanEvalA cartanEvalB
  rw [tupEval_compA_sub_compB p q q' u v hp hu hv, oddDiff_single, oddDiffGen, map_add, map_add,
    tupEval_homotopy_oddDiffW p q q' u v hp, zero_add]
  show tupEval (ZMod p) X (2 * p) (k + 1) (cartanFun p q q' u v)
      (((compHomotopy p).s k X).hom
        (oddDiffS p (oddSingularBoundary p) X k (0 : Fin (k + 2)) (simplexEquiv X 0 σ))) = 0
  rw [oddDiffS_zero, map_zero, map_zero]

/-- At simplex degree `m + 1` the two composites differ by the alternating face sum of the
homotopy's evaluation. -/
theorem cartanEvalA_succ (hp : Odd p) (hu : cochainCoboundary (ZMod p) X q u = 0)
    (hv : cochainCoboundary (ZMod p) X q' v = 0) (k m : ℕ) (hm : m + 1 < k + 1 + 1)
    (σ : singularSimplices X (m + 1)) :
    cartanEvalA p q q' u v (k + 1) (m + 1) hm σ - cartanEvalB p q q' u v (k + 1) (m + 1) hm σ
      = (-1 : ZMod p) ^ (k - m) * ∑ f : Fin (m + 2), (-1 : ZMod p) ^ (f : ℕ) *
          cartanEvalH p q q' u v k m (by omega) (faceSimplex X m f σ) := by
  unfold cartanEvalA cartanEvalB cartanEvalH
  rw [tupEval_compA_sub_compB p q q' u v hp hu hv, oddDiff_single, oddDiffGen, map_add, map_add,
    tupEval_homotopy_oddDiffW p q q' u v hp, zero_add]
  exact tupEval_homotopy_oddDiffS_succ p q q' u v hp k ⟨m, by omega⟩ σ

/-- The first composite's cochain at simplex degree `N`. -/
def cartanCochainA (K N : ℕ) (hN : N < K + 1) : singularCochainGroup (ZMod p) X N :=
  cochainOfFun N (cartanEvalA p q q' u v K N hN)

/-- The second composite's cochain at simplex degree `N`. -/
def cartanCochainB (K N : ℕ) (hN : N < K + 1) : singularCochainGroup (ZMod p) X N :=
  cochainOfFun N (cartanEvalB p q q' u v K N hN)

/-- The homotopy's cochain at simplex degree `m`. -/
def cartanCochainH (k m : ℕ) (hm : m < k + 1) : singularCochainGroup (ZMod p) X m :=
  cochainOfFun m (cartanEvalH p q q' u v k m hm)

theorem cartanCochainA_zero_eq (hp : Odd p) (hu : cochainCoboundary (ZMod p) X q u = 0)
    (hv : cochainCoboundary (ZMod p) X q' v = 0) (k : ℕ) :
    cartanCochainA p q q' u v (k + 1) 0 (Nat.succ_pos _)
      = cartanCochainB p q q' u v (k + 1) 0 (Nat.succ_pos _) := by
  apply cochain_ext
  intro σ
  simp only [cartanCochainA, cartanCochainB, cochainEval_cochainOfFun]
  exact cartanEvalA_zero p q q' u v hp hu hv k σ

/-- **The comparison at cochain level**: `A = B + (−1)^{W-index} · δH` at positive simplex degree. -/
theorem cartanCochainA_succ_eq (hp : Odd p) (hu : cochainCoboundary (ZMod p) X q u = 0)
    (hv : cochainCoboundary (ZMod p) X q' v = 0) (k m : ℕ) (hm : m + 1 < k + 1 + 1) :
    cartanCochainA p q q' u v (k + 1) (m + 1) hm
      = cartanCochainB p q q' u v (k + 1) (m + 1) hm
        + (-1 : ZMod p) ^ (k - m) •
            cochainCoboundary (ZMod p) X m (cartanCochainH p q q' u v k m (by omega)) := by
  apply cochain_ext
  intro σ
  simp only [cartanCochainA, cartanCochainB, cartanCochainH, cochainEval_add, cochainEval_smul,
    cochainCoboundary_eval, cochainEval_cochainOfFun]
  rw [← sub_eq_iff_eq_add']
  exact cartanEvalA_succ p q q' u v hp hu hv k m hm σ

omit [NeZero p] [Fact p.Prime] in
theorem cochainCoboundary_add' (m : ℕ) (φ ψ : singularCochainGroup (ZMod p) X m) :
    cochainCoboundary (ZMod p) X m (φ + ψ)
      = cochainCoboundary (ZMod p) X m φ + cochainCoboundary (ZMod p) X m ψ := by
  unfold cochainCoboundary
  exact map_add _ φ ψ

omit [NeZero p] [Fact p.Prime] in
theorem cocycleClassK_eq_of_eq' {n : ℕ} {φ ψ : singularCochainGroup (ZMod p) X n} (h : φ = ψ)
    (hφ : cochainCoboundary (ZMod p) X n φ = 0) (hψ : cochainCoboundary (ZMod p) X n ψ = 0) :
    cocycleClassK (ZMod p) X n φ hφ = cocycleClassK (ZMod p) X n ψ hψ := by
  subst h
  rfl

/-- The second composite's cochain is a cocycle whenever the first composite's is. -/
theorem cartanCochainB_cocycle (hp : Odd p) (hu : cochainCoboundary (ZMod p) X q u = 0)
    (hv : cochainCoboundary (ZMod p) X q' v = 0) (K N : ℕ) (hK : 1 ≤ K) (hN : N < K + 1)
    (hA : cochainCoboundary (ZMod p) X N (cartanCochainA p q q' u v K N hN) = 0) :
    cochainCoboundary (ZMod p) X N (cartanCochainB p q q' u v K N hN) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  cases N with
  | zero => rwa [← cartanCochainA_zero_eq p q q' u v hp hu hv k]
  | succ m =>
    rw [cartanCochainA_succ_eq p q q' u v hp hu hv k m hN, cochainCoboundary_add',
      CupOneLocal.cochainCoboundary_smul, cochainCoboundary_cochainCoboundaryK, smul_zero,
      add_zero] at hA
    exact hA

/-- **The comparison at class level**, at a variable simplex degree: the two composites' cochains
have the same class. -/
theorem cocycleClassK_cartanCochainA (hp : Odd p) (hu : cochainCoboundary (ZMod p) X q u = 0)
    (hv : cochainCoboundary (ZMod p) X q' v = 0) (K N : ℕ) (hK : 1 ≤ K) (hN : N < K + 1)
    (hA : cochainCoboundary (ZMod p) X N (cartanCochainA p q q' u v K N hN) = 0) :
    cocycleClassK (ZMod p) X N (cartanCochainA p q q' u v K N hN) hA
      = cocycleClassK (ZMod p) X N (cartanCochainB p q q' u v K N hN)
          (cartanCochainB_cocycle p q q' u v hp hu hv K N hK hN hA) := by
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  cases N with
  | zero => exact cocycleClassK_eq_of_eq' p (cartanCochainA_zero_eq p q q' u v hp hu hv k) _ _
  | succ m =>
    have hB := cartanCochainB_cocycle p q q' u v hp hu hv (k + 1) (m + 1) hK hN hA
    have hH : cochainCoboundary (ZMod p) X (m + 1)
        ((-1 : ZMod p) ^ (k - m) •
          cochainCoboundary (ZMod p) X m (cartanCochainH p q q' u v k m (by omega))) = 0 := by
      rw [CupOneLocal.cochainCoboundary_smul, cochainCoboundary_cochainCoboundaryK, smul_zero]
    have hsum : cochainCoboundary (ZMod p) X (m + 1)
        (cartanCochainB p q q' u v (k + 1) (m + 1) hN
          + (-1 : ZMod p) ^ (k - m) •
              cochainCoboundary (ZMod p) X m (cartanCochainH p q q' u v k m (by omega))) = 0 := by
      rw [cochainCoboundary_add', hB, hH, add_zero]
    rw [cocycleClassK_eq_of_eq' p (cartanCochainA_succ_eq p q q' u v hp hu hv k m hN) hA hsum,
      CupOneLocal.cocycleClassK_add (ZMod p) X (m + 1) _ _ hB hH hsum,
      CupOneLocal.cocycleClassK_smul (ZMod p) X (m + 1) _ _
        (cochainCoboundary_cochainCoboundaryK (ZMod p) X m _) hH,
      cocycleClassK_coboundary_zero, smul_zero, add_zero]

/-- **The first composite's cochain is `D_i(u ⌣ v)`.** -/
theorem cartanCochainA_eq_oddD (i : ℕ) :
    cartanCochainA p q q' u v (p * (q + q')) (p * (q + q') - i)
        (Nat.lt_succ_of_le (Nat.sub_le _ _))
      = oddD p (q + q') i (cochainCup q q' u v) := by
  apply cochain_ext
  intro σ
  simp only [cartanCochainA, cartanEvalA, cartanFun, cochainEval_cochainOfFun]
  exact tupEval_compA_oddD p X q q' i u v σ

end

end GroupApproximation.CharClass

open GroupApproximation.CharClass

#audit_axioms compHomotopy
#audit_axioms cocycleClassK_cartanCochainA
#audit_axioms cartanCochainA_eq_oddD
