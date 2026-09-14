import GroupApproximation.CharClass.OddPCompA
import GroupApproximation.CharClass.OddPCompBReal
import GroupApproximation.CharClass.OddPCochainSum

/-!
# The second composite of the odd-primary Cartan comparison

The second natural `F_p[ℤ/p]`-linear chain map `W ⊗ C(X) → C(X)^{⊗2p}` of the Cartan comparison is
defined on the free generators `e_j ⊗ σ` of the source and extended over the group ring:

```text
compB (e_j ⊗ σ) = riffle ( Σ_{AW splits σ = σ'·σ''}  R_{σ',σ''} (ψ_W e_j) ),
R_{σ',σ''} (T^s e_a ⊗ T^{s'} e_b) = (−1)^{b·|σ'|} · concat (Δ(T^s e_a ⊗ σ'), Δ(T^{s'} e_b ⊗ σ'')),
```

`compBSum` (`OddPCompBReal.lean`) is the sum over the splits.  The group ring acts on the target
through `T²`, and the riffle turns the blockwise rotation into `T²` (`tupRiffleAll_conj`), which is
what makes the extension from the generators a chain map: the resolution half of the source
differential is `ψ_W`'s chain-map identity (`psiW_chainMap`) carried through `compBSum`'s equivariance,
and the simplicial half is `compBSum`'s Alexander–Whitney identity.

The values are built in the full model and land in degree `k` (`compBSum_mem_range`); the generator
of the degree-`k` component is the unique preimage under the inclusion.

## Main results

* `compBAll`, `compBGen` — the second composite on a generator.
* `compBLin` — its extension over the group ring, in degree `k`.
* `tupIncl_compBLin_oddDiff_single` — **the chain-map identity on generators.**
* `compB` — **the second composite**, a natural transformation `oddSrc ⟶ oddTgt p (2p) 2`.
* `compB_zero` — in degree `0` it sends `e_0 ⊗ x` to the constant tuple `x^{⊗2p}`.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

variable (p : ℕ) [NeZero p]

/-! ## 1. Group-ring bookkeeping on the full model -/

theorem tupTAll_sq_pow_card (X : TopCat.{0}) : (tupTAll (ZMod p) X (2 * p) ^ 2) ^ p = 1 := by
  rw [← pow_mul, tupTAll_pow_card]

/-- **The riffle carries the blockwise group-ring action to the `T²` action.** -/
theorem tupRiffleAll_galAlgHomP (X : TopCat.{0}) (c : GroupRingZMod p)
    (z : tupAllMod (ZMod p) X (2 * p)) :
    tupRiffleAll (ZMod p) X p
        (galAlgHomP (tupBlockRotAll (ZMod p) X p) (tupBlockRotAll_pow_card p X) c z)
      = galAlgHomP (tupTAll (ZMod p) X (2 * p) ^ 2) (tupTAll_sq_pow_card p X) c
          (tupRiffleAll (ZMod p) X p z) :=
  galAlgHomP_comm p (tupBlockRotAll (ZMod p) X p) (tupBlockRotAll_pow_card p X)
    (tupTAll (ZMod p) X (2 * p) ^ 2) (tupTAll_sq_pow_card p X) (tupRiffleAll (ZMod p) X p)
    (fun v => by
      have h := LinearMap.congr_fun (tupRiffleAll_conj (ZMod p) X p) v
      simpa only [Module.End.mul_apply] using h) c z

/-- **The inclusion of the degree-`k` carrier intertwines the two `T²` actions.** -/
theorem tupIncl_galAlgHomP (X : TopCat.{0}) (k : ℕ) (c : GroupRingZMod p)
    (y : tupMod (ZMod p) X (2 * p) k) :
    tupIncl (ZMod p) X (2 * p) k
        (galAlgHomP (tupT (ZMod p) X (2 * p) k ^ 2)
          (tupT_pow_pow p X (2 * p) k 2 (dvd_two_mul_self p)) c y)
      = galAlgHomP (tupTAll (ZMod p) X (2 * p) ^ 2) (tupTAll_sq_pow_card p X) c
          (tupIncl (ZMod p) X (2 * p) k y) :=
  galAlgHomP_comm p (tupT (ZMod p) X (2 * p) k ^ 2)
    (tupT_pow_pow p X (2 * p) k 2 (dvd_two_mul_self p))
    (tupTAll (ZMod p) X (2 * p) ^ 2) (tupTAll_sq_pow_card p X) (tupIncl (ZMod p) X (2 * p) k)
    (fun v => by rw [tupIncl_tupT_pow]) c y

/-- **The pushforward commutes with every signed slot permutation.**  Pushing forward keeps the
degree of every slot, so the Koszul sign does not move. -/
theorem tupAllMap_tupPermAll {X Y : TopCat.{0}} (f : X ⟶ Y) (r : ℕ) (π : Equiv.Perm (Fin r))
    (z : tupAllMod (ZMod p) X r) :
    tupAllMap (ZMod p) f r (tupPermAll (ZMod p) X r π z)
      = tupPermAll (ZMod p) Y r π (tupAllMap (ZMod p) f r z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | single t a =>
    have hs : Finsupp.single t a = a • Finsupp.single t (1 : ZMod p) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    simp only [hs, map_smul, tupPermAll_single, tupAllMap_single]
    rfl

/-- `ψ_W` in total `W`-degree `0` has no differential. -/
theorem wwDAll_psiW_zero (x : GroupRingZMod p) : wwDAll p (psiW p 0 x) = 0 := by
  rw [psiW_apply, Finset.Nat.antidiagonal_zero, Finset.sum_singleton, wwDAll_atBideg,
    wdLeftBd_zero, wdRightBd_zero, add_zero]

/-- A group-ring scalar that is a sign acts as that sign. -/
theorem galAlgHomP_neg_one_pow {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (τ : Module.End (ZMod p) V) (hτ : τ ^ p = 1) (a b : ℕ) (v : V) :
    galAlgHomP τ hτ ((-1 : GroupRingZMod p) ^ a * (-1) ^ b) v = ((-1 : ZMod p) ^ a * (-1) ^ b) • v := by
  have hc : ((-1 : GroupRingZMod p) ^ a * (-1) ^ b)
      = algebraMap (ZMod p) (GroupRingZMod p) ((-1 : ZMod p) ^ a * (-1) ^ b) := by
    simp only [map_mul, map_pow, map_neg, map_one]
  rw [hc, AlgHom.commutes, Module.algebraMap_end_apply]

/-! ## 2. The second composite on generators -/

variable [Fact p.Prime]

/-- **The second composite on the generator** `e_{k−n} ⊗ σ`, in the full model. -/
def compBAll (X : TopCat.{0}) (k : ℕ) (q : WSIndex k X) : tupAllMod (ZMod p) X (2 * p) :=
  tupRiffleAll (ZMod p) X p
    (compBSum p X q.1.val ((simplexEquiv X q.1.val).symm q.2) (psiW p (k - q.1.val) 1))

/-- The second composite on a generator of degree `k` lands in degree `k`. -/
theorem compBAll_mem_range (X : TopCat.{0}) (k : ℕ) (q : WSIndex k X) :
    compBAll p X k q ∈ LinearMap.range (tupIncl (ZMod p) X (2 * p) k) := by
  have h := compBSum_mem_range p X q.1.val ((simplexEquiv X q.1.val).symm q.2) (k - q.1.val) 1
  have hk : k - q.1.val + q.1.val = k := Nat.sub_add_cancel (Nat.le_of_lt_succ q.1.2)
  rw [hk] at h
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp h
  refine LinearMap.mem_range.mpr ⟨tupRiffle (ZMod p) X p k y, ?_⟩
  rw [← LinearMap.comp_apply (tupIncl (ZMod p) X (2 * p) k) (tupRiffle (ZMod p) X p k),
    tupIncl_comp_tupRiffle, LinearMap.comp_apply, hy]
  rfl

/-- **The second composite on a generator, in the degree-`k` carrier**: the preimage of
`compBAll` under the inclusion. -/
def compBGen (X : TopCat.{0}) (k : ℕ) (q : WSIndex k X) : tupMod (ZMod p) X (2 * p) k :=
  (LinearMap.mem_range.mp (compBAll_mem_range p X k q)).choose

theorem tupIncl_compBGen (X : TopCat.{0}) (k : ℕ) (q : WSIndex k X) :
    tupIncl (ZMod p) X (2 * p) k (compBGen p X k q) = compBAll p X k q :=
  (LinearMap.mem_range.mp (compBAll_mem_range p X k q)).choose_spec

/-- **The second composite in degree `k`**, extended over the group ring from the generators. -/
def compBLin (X : TopCat.{0}) (k : ℕ) :
    @LinearMap (GroupRingZMod p) (GroupRingZMod p) _ _ (RingHom.id (GroupRingZMod p))
      (OddWTensor p k X) (tupMod (ZMod p) X (2 * p) k) _ _ _
      (tupModule p X (2 * p) k 2 (dvd_two_mul_self p)) :=
  letI := tupModule p X (2 * p) k 2 (dvd_two_mul_self p)
  Finsupp.linearCombination (GroupRingZMod p) (compBGen p X k)

theorem compBLin_single (X : TopCat.{0}) (k : ℕ) (q : WSIndex k X) :
    compBLin p X k (Finsupp.single q (1 : GroupRingZMod p)) = compBGen p X k q := by
  letI := tupModule p X (2 * p) k 2 (dvd_two_mul_self p)
  show Finsupp.linearCombination (GroupRingZMod p) (compBGen p X k) (Finsupp.single q 1) = _
  rw [Finsupp.linearCombination_single, one_smul]

/-- On a scaled generator, the inclusion of the second composite is the `T²` action on
`compBAll`. -/
theorem tupIncl_compBLin_smul_single (X : TopCat.{0}) (k : ℕ) (q : WSIndex k X)
    (c : GroupRingZMod p) :
    tupIncl (ZMod p) X (2 * p) k (compBLin p X k (c • Finsupp.single q 1))
      = galAlgHomP (tupTAll (ZMod p) X (2 * p) ^ 2) (tupTAll_sq_pow_card p X) c
          (compBAll p X k q) := by
  letI := tupModule p X (2 * p) k 2 (dvd_two_mul_self p)
  have h1 : compBLin p X k (c • Finsupp.single q 1)
      = galAlgHomP (tupT (ZMod p) X (2 * p) k ^ 2)
          (tupT_pow_pow p X (2 * p) k 2 (dvd_two_mul_self p)) c (compBGen p X k q) := by
    rw [LinearMap.map_smul, compBLin_single]
    rfl
  rw [h1, tupIncl_galAlgHomP, tupIncl_compBGen]

/-! ## 3. The chain-map identity on generators -/

/-- **The resolution half of the source differential**, through the second composite. -/
theorem tupIncl_compBLin_oddDiffW (X : TopCat.{0}) (j : ℕ) (n : Fin (j + 2))
    (σ : stdSimplexTop n.val ⟶ X) :
    tupIncl (ZMod p) X (2 * p) j (compBLin p X j (oddDiffW p X j n σ))
      = tupRiffleAll (ZMod p) X p
          (compBSum p X n.val ((simplexEquiv X n.val).symm σ)
            (wwDAll p (psiW p (j + 1 - n.val) 1))) := by
  revert σ
  induction n using Fin.lastCases with
  | last =>
    intro σ
    have h0 : j + 1 - (Fin.last (j + 1)).val = 0 := by simp
    rw [oddDiffW_last, map_zero, map_zero, h0, wwDAll_psiW_zero, map_zero, map_zero]
  | cast m =>
    intro σ
    have hm : j + 1 - (Fin.castSucc m).val = j - m.val + 1 := by
      simp only [Fin.coe_castSucc]
      omega
    rw [oddDiffW_castSucc, tupIncl_compBLin_smul_single, hm, ← psiW_chainMap,
      psiW_mul_galAlgHomP, compBSum_galAlgHomP, tupRiffleAll_galAlgHomP]
    rfl

/-- **The simplicial half of the source differential**, through the second composite, at a generator
of positive simplex degree. -/
theorem tupIncl_compBLin_oddDiffS_succ (X : TopCat.{0}) (j : ℕ) (m : Fin (j + 1))
    (σ : singularSimplices X (m.val + 1)) :
    tupIncl (ZMod p) X (2 * p) j
        (compBLin p X j (oddDiffS p (oddSingularBoundary p) X j (Fin.succ m)
          (simplexEquiv X (m.val + 1) σ)))
      = (-1 : ZMod p) ^ (j - m.val) • ∑ f : Fin (m.val + 2), (-1 : ZMod p) ^ (f : ℕ) •
          tupRiffleAll (ZMod p) X p
            (compBSum p X m.val (faceSimplex X m.val f σ) (psiW p (j - m.val) 1)) := by
  rw [oddDiffS_succ_eq_sum, map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [tupIncl_compBLin_smul_single, galAlgHomP_neg_one_pow, mul_smul]
  congr 2
  show tupRiffleAll (ZMod p) X p
      (compBSum p X m.val ((simplexEquiv X m.val).symm
        (simplexEquiv X m.val (faceSimplex X m.val f σ))) (psiW p (j - m.val) 1)) = _
  rw [Equiv.symm_apply_apply]

/-- **The chain-map identity on generators**: the inclusion of the second composite applied to the
source differential of a generator is the riffle of the boundary of `compBSum`. -/
theorem tupIncl_compBLin_oddDiff_single (X : TopCat.{0}) (j : ℕ) (q : WSIndex (j + 1) X) :
    tupIncl (ZMod p) X (2 * p) j
        (compBLin p X j (oddDiff p (oddSingularBoundary p) X j (Finsupp.single q 1)))
      = tupRiffleAll (ZMod p) X p (tupDAll (ZMod p) X (2 * p)
          (compBSum p X q.1.val ((simplexEquiv X q.1.val).symm q.2)
            (psiW p (j + 1 - q.1.val) 1))) := by
  obtain ⟨n, σ⟩ := q
  rw [oddDiff_single, oddDiffGen, map_add, map_add, tupIncl_compBLin_oddDiffW]
  revert σ
  induction n using Fin.cases with
  | zero =>
    intro σ
    rw [oddDiffS_zero, map_zero, map_zero, add_zero]
    show _ = tupRiffleAll (ZMod p) X p (tupDAll (ZMod p) X (2 * p)
      (compBSum p X 0 ((simplexEquiv X 0).symm σ) (psiW p (j + 1 - 0) 1)))
    rw [tupDAll_compBSum_zero]
    rfl
  | succ m =>
    intro σ
    have hS := tupIncl_compBLin_oddDiffS_succ p X j m ((simplexEquiv X (m.val + 1)).symm σ)
    rw [Equiv.apply_symm_apply] at hS
    rw [hS]
    have hw : j + 1 - (Fin.succ m).val = j - m.val := by
      simp only [Fin.val_succ]
      omega
    show _ = tupRiffleAll (ZMod p) X p (tupDAll (ZMod p) X (2 * p)
      (compBSum p X (m.val + 1) ((simplexEquiv X (m.val + 1)).symm σ)
        (psiW p (j + 1 - (Fin.succ m).val) 1)))
    rw [hw, tupDAll_compBSum_succ, map_add, map_smul, map_sum]
    simp only [map_smul]
    rfl

/-! ## 4. The second composite as a natural transformation -/

/-- The degree-`k` component of the second composite, as a morphism over the group ring. -/
def compBHom (X : TopCat.{0}) (k : ℕ) :
    ((oddSrc p (oddSingularBoundary p)).obj X).X k
      ⟶ ((oddTgt p (2 * p) 2 (dvd_two_mul_self p)).obj X).X k :=
  letI := tupModule p X (2 * p) k 2 (dvd_two_mul_self p)
  ModuleCat.ofHom (compBLin p X k)

theorem compBHom_hom_apply (X : TopCat.{0}) (k : ℕ) (x : OddWTensor p k X) :
    (compBHom p X k).hom x = compBLin p X k x := by
  unfold compBHom
  rfl

/-- **The second composite at one space, as a map of complexes.** -/
def compBCx (X : TopCat.{0}) :
    (oddSrc p (oddSingularBoundary p)).obj X ⟶ (oddTgt p (2 * p) 2 (dvd_two_mul_self p)).obj X where
  f k := compBHom p X k
  comm' i j hij := by
    have hij' : j + 1 = i := hij
    subst hij'
    rw [oddSrc_obj_d, oddTgt_obj_d]
    letI := tupModule p X (2 * p) (j + 1) 2 (dvd_two_mul_self p)
    letI := tupModule p X (2 * p) j 2 (dvd_two_mul_self p)
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro q
    apply LinearMap.ext_ring
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Finsupp.lsingle_apply, ModuleCat.hom_ofHom,
      compBHom_hom_apply, tupDHom_hom_apply]
    apply tupIncl_injective (ZMod p) X j
    rw [tupIncl_compBLin_oddDiff_single,
      ← LinearMap.comp_apply (tupIncl (ZMod p) X (2 * p) j) (tupD (ZMod p) X (2 * p) j),
      tupIncl_comp_tupD, LinearMap.comp_apply, compBLin_single, tupIncl_compBGen, compBAll]
    have h := LinearMap.congr_fun (tupRiffleAll_mul_tupDAll (ZMod p) X p)
      (compBSum p X q.1.val ((simplexEquiv X q.1.val).symm q.2) (psiW p (j + 1 - q.1.val) 1))
    simpa only [Module.End.mul_apply] using h.symm

theorem compBCx_f (X : TopCat.{0}) (k : ℕ) : (compBCx p X).f k = compBHom p X k := rfl

/-- **The second composite** `W ⊗ C(X) → C(X)^{⊗2p}`, natural in the space. -/
def compB : oddSrc p (oddSingularBoundary p) ⟶ oddTgt p (2 * p) 2 (dvd_two_mul_self p) where
  app X := compBCx p X
  naturality X Y φ := by
    refine HomologicalComplex.hom_ext _ _ fun k => ?_
    letI := tupModule p X (2 * p) k 2 (dvd_two_mul_self p)
    letI := tupModule p Y (2 * p) k 2 (dvd_two_mul_self p)
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro q
    apply LinearMap.ext_ring
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      Finsupp.lsingle_apply]
    show compBLin p Y k ((((oddSrc p (oddSingularBoundary p)).map φ).f k).hom
        (Finsupp.single q 1))
      = (tupMapHom p φ (2 * p) k 2 (dvd_two_mul_self p)).hom (compBLin p X k (Finsupp.single q 1))
    rw [oddSrc_map_single, tupMapHom_hom_apply, compBLin_single, compBLin_single]
    apply tupIncl_injective (ZMod p) Y k
    rw [tupIncl_compBGen,
      ← LinearMap.comp_apply (tupIncl (ZMod p) Y (2 * p) k) (tupMap (ZMod p) φ (2 * p) k),
      tupIncl_comp_tupMap, LinearMap.comp_apply, tupIncl_compBGen]
    obtain ⟨n, σ⟩ := q
    have hpush : (simplexEquiv Y n.val).symm (σ ≫ φ)
        = pushSimplex φ n.val ((simplexEquiv X n.val).symm σ) := by
      apply (simplexEquiv Y n.val).injective
      rw [simplexEquiv_pushSimplex, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    show tupRiffleAll (ZMod p) Y p
        (compBSum p Y n.val ((simplexEquiv Y n.val).symm (σ ≫ φ)) (psiW p (k - n.val) 1))
      = tupAllMap (ZMod p) φ (2 * p) (tupRiffleAll (ZMod p) X p
          (compBSum p X n.val ((simplexEquiv X n.val).symm σ) (psiW p (k - n.val) 1)))
    rw [hpush, tupRiffleAll, tupRiffleAll, tupAllMap_tupPermAll, tupAllMap_compBSum]

/-- The components of the second composite, as functions. -/
theorem compB_app_f_apply (X : TopCat.{0}) (k : ℕ) (x : OddWTensor p k X) :
    (((compB p).app X).f k).hom x = compBLin p X k x := by
  show (compBHom p X k).hom x = _
  rw [compBHom_hom_apply]

/-- **In degree `0` the second composite is the constant tuple** `x^{⊗2p}`. -/
theorem compB_zero (X : TopCat.{0}) (x : stdSimplexTop 0 ⟶ X) :
    (((compB p).app X).f 0).hom (Finsupp.single (⟨0, x⟩ : WSIndex 0 X) (1 : GroupRingZMod p))
      = Finsupp.single (diagPt X (2 * p) x) (1 : ZMod p) := by
  rw [compB_app_f_apply, compBLin_single]
  apply tupIncl_injective (ZMod p) X 0
  rw [tupIncl_compBGen, tupIncl_single]
  change tupRiffleAll (ZMod p) X p
      (compBSum p X 0 ((simplexEquiv X 0).symm x) (psiW p 0 1)) = _
  rw [compBSum_zero_psiW_zero, tupRiffleAll, tupPermAll_single]
  have hconst : tupAppendSq p (fun _ => (⟨0, (simplexEquiv X 0).symm x⟩ : TagSimp X))
      (fun _ => ⟨0, (simplexEquiv X 0).symm x⟩) = fun _ => ⟨0, (simplexEquiv X 0).symm x⟩ := by
    funext i
    unfold tupAppendSq
    split_ifs <;> rfl
  have hexp : permExp X (riffleEquiv p)
      (fun _ : Fin (2 * p) => (⟨0, (simplexEquiv X 0).symm x⟩ : TagSimp X)) = 0 := by
    unfold permExp
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun l _ => ?_
    split_ifs <;> simp
  rw [hconst, hexp, pow_zero, one_smul]
  rfl

end

end GroupApproximation.CharClass

open GroupApproximation.CharClass

#audit_axioms compB
#audit_axioms compB_zero
#audit_axioms tupIncl_compBLin_oddDiff_single
