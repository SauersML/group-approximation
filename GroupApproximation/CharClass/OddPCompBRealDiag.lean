import GroupApproximation.CharClass.OddPDiagonal
import GroupApproximation.CharClass.OddPWDiagonal
import GroupApproximation.CharClass.OddPProductEval
import GroupApproximation.Meta.AxiomGuard

/-!
# The equivariant diagonal on generators, in the full tuple model

The realisation `B` of the Cartan comparison (lx-cartan-b's lemma list, item 5) is assembled from
values `Φ(T^s e_a ⊗ σ')` of the equivariant diagonal `Φ = oddDiagApp p` on single generators of
`W ⊗ C(X)`, placed in the full tuple model `tupAllMod (ZMod p) X p`, where the degree is data rather
than part of the type.  This file computes the boundary of such a value, which is everything the
chain-map argument for `B` needs to know about `Φ`.

For a generator `c · (e_a ⊗ τ)` with `τ : Δ^m → X`, write `Φ(a, m, c, τ)` for
`tupIncl (a + m) (Φ (c · (e_a ⊗ τ)))`.  Then

```text
∂ Φ(a, m, c, τ) = Φ(a − 1, m, altCoeff (a − 1) · c, τ)                    (a ≥ 1)
                 + (−1)^a Σ_f (−1)^f Φ(a, m − 1, c, ∂_f τ)                 (m ≥ 1)
```

because `Φ` is a chain map and the source differential is `d(e_a ⊗ τ) = d_W e_a ⊗ τ + (−1)^a e_a ⊗ ∂τ`.

The degree `a + m` is ordered so that the simplicial half is definitional (`a + (m' + 1) = (a + m') + 1`),
and the resolution half moves between degrees through `phiAll_single_deg_congr`, which costs
nothing because the full model does not mention the degree.

## Main results

* `CompBReal.tupDAll_phiAll_succ` — `Φ` intertwines the two differentials on the full model.
* `CompBReal.phiAll_grGen_smul` — the generator of the group ring acts as the cyclic operator.
* `CompBReal.tupDAll_phiG_succ`, `tupDAll_phiG_succ_zero`, `tupDAll_phiG_zero_zero` — the boundary of
  `Φ(a, m, c, τ)` in the three cases.
* `CompBReal.wdCAlt_wdT1`, `wdCAlt_wdT2` — the differential coefficients of `W ⊗ W` are the images of
  `altCoeff` under the two factor embeddings `wdInl`, `wdInr`.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

namespace CompBReal

/-! ## 1. Group-ring generators and the factor embeddings -/

/-- `T^s` in the group ring. -/
def monoGen (p : ℕ) (s : ZMod p) : GroupRingZMod p :=
  MonoidAlgebra.single (Multiplicative.ofAdd s) (1 : ZMod p)

theorem monoGen_eq_pow (p : ℕ) [NeZero p] (s : ZMod p) : monoGen p s = grGen p ^ s.val := by
  unfold monoGen grGen
  rw [MonoidAlgebra.single_pow, one_pow, ← ofAdd_nsmul, nsmul_eq_mul, mul_one,
    ZMod.natCast_zmod_val]

theorem monoGen_one_add (p : ℕ) (s : ZMod p) : monoGen p (1 + s) = grGen p * monoGen p s := by
  unfold monoGen grGen
  rw [MonoidAlgebra.single_mul_single, mul_one, ofAdd_add]

/-- The group ring into the left factor of `F_p[ℤ/p × ℤ/p]`. -/
def wdInl (p : ℕ) : GroupRingZMod p →ₐ[ZMod p] GroupRingZMod2 p :=
  MonoidAlgebra.mapDomainAlgHom (ZMod p) (ZMod p)
    (MonoidHom.inl (Multiplicative (ZMod p)) (Multiplicative (ZMod p)))

/-- The group ring into the right factor of `F_p[ℤ/p × ℤ/p]`. -/
def wdInr (p : ℕ) : GroupRingZMod p →ₐ[ZMod p] GroupRingZMod2 p :=
  MonoidAlgebra.mapDomainAlgHom (ZMod p) (ZMod p)
    (MonoidHom.inr (Multiplicative (ZMod p)) (Multiplicative (ZMod p)))

theorem wdInl_single (p : ℕ) (g : Multiplicative (ZMod p)) (c : ZMod p) :
    wdInl p (MonoidAlgebra.single g c) = MonoidAlgebra.single (g, 1) c := by
  simp [wdInl, MonoidAlgebra.mapDomain_single]

theorem wdInr_single (p : ℕ) (g : Multiplicative (ZMod p)) (c : ZMod p) :
    wdInr p (MonoidAlgebra.single g c) = MonoidAlgebra.single (1, g) c := by
  simp [wdInr, MonoidAlgebra.mapDomain_single]

theorem wdInl_grGen (p : ℕ) : wdInl p (grGen p) = wdT1 p := by
  unfold grGen wdT1
  rw [wdInl_single]

theorem wdInr_grGen (p : ℕ) : wdInr p (grGen p) = wdT2 p := by
  unfold grGen wdT2
  rw [wdInr_single]

/-- The left differential coefficient of `W ⊗ W` is `altCoeff` on the left factor. -/
theorem wdCAlt_wdT1 (p a : ℕ) :
    wdCAlt p a (wdT1 p) = wdInl p (altCoeff (grS p) (grNorm p) a) := by
  unfold wdCAlt altCoeff
  split_ifs
  · rw [grS, map_sub, map_one, wdInl_grGen]
  · simp only [grNorm, map_sum, map_pow, wdInl_grGen, wdNormSum]

/-- The right differential coefficient of `W ⊗ W` is `altCoeff` on the right factor. -/
theorem wdCAlt_wdT2 (p b : ℕ) :
    wdCAlt p b (wdT2 p) = wdInr p (altCoeff (grS p) (grNorm p) b) := by
  unfold wdCAlt altCoeff
  split_ifs
  · rw [grS, map_sub, map_one, wdInr_grGen]
  · simp only [grNorm, map_sum, map_pow, wdInr_grGen, wdNormSum]

/-- A basis vector of one bidegree is the product of its two factors. -/
theorem wdMono_eq (p : ℕ) (s s' : ZMod p) :
    wdMono p s s' = wdInl p (monoGen p s) * wdInr p (monoGen p s') := by
  unfold wdMono monoGen
  rw [wdInl_single, wdInr_single, MonoidAlgebra.single_mul_single, Prod.mk_mul_mk, mul_one,
    one_mul, mul_one]

/-! ## 2. Index lemmas for the source differential -/

section Source

variable (p : ℕ) (X : TopCat.{0})

/-- The resolution half vanishes on a generator of `W`-index `0`. -/
theorem oddDiffW_of_val_eq_last (k : ℕ) (n : Fin (k + 2)) (hn : n.val = k + 1)
    (σ : stdSimplexTop n.val ⟶ X) : oddDiffW p X k n σ = 0 := by
  induction n using Fin.lastCases with
  | last => exact oddDiffW_last p X k σ
  | cast j =>
    have hj := j.isLt
    simp only [Fin.coe_castSucc] at hn
    omega

/-- The simplicial half vanishes on a generator of simplex degree `0`. -/
theorem oddDiffS_of_val_eq_zero (data : OddPBoundaryData p) (k : ℕ) (n : Fin (k + 2))
    (hn : n.val = 0) (σ : stdSimplexTop n.val ⟶ X) : oddDiffS p data X k n σ = 0 := by
  induction n using Fin.cases with
  | zero => exact oddDiffS_zero p data X k σ
  | succ j =>
    simp only [Fin.val_succ] at hn
    omega

/-- The signed boundary of one simplex, relabelled into a fixed `W`-index, as a face sum. -/
theorem lmapDomain_bdRHom_single (k m' : ℕ) (hm : m' < k + 1) (τ : stdSimplexTop (m' + 1) ⟶ X) :
    Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p)
        (fun τ' : stdSimplexTop m' ⟶ X => (⟨⟨m', hm⟩, τ'⟩ : WSIndex k X))
        (bdRHom (GroupRingZMod p) X m' (Finsupp.single τ 1))
      = ∑ f : Fin (m' + 2), ((-1 : ℤ) ^ (f : ℕ)) •
          Finsupp.single (⟨⟨m', hm⟩, simplexEquiv X m'
            (faceSimplex X m' f ((simplexEquiv X (m' + 1)).symm τ))⟩ : WSIndex k X)
            (1 : GroupRingZMod p) := by
  rw [bdRHom_apply, Finsupp.mapDomain_single, singFreeR_d_single,
    ← Finsupp.lmapDomain_apply (GroupRingZMod p) (GroupRingZMod p), ← LinearMap.comp_apply,
    map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [map_zsmul, LinearMap.comp_apply, Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, Finsupp.mapDomain_single]

/-- The generator `c · (e_a ⊗ τ)` of `W ⊗ C(X)`, in total degree `a + m`. -/
def srcGen (a m : ℕ) (c : GroupRingZMod p) (τ : stdSimplexTop m ⟶ X) : OddWTensor p (a + m) X :=
  Finsupp.single (⟨⟨m, Nat.lt_succ_of_le (Nat.le_add_left m a)⟩, τ⟩ : WSIndex (a + m) X) c

/-- The face `∂_f τ` of a singular simplex given as a map out of `Δ^{m'+1}`. -/
def faceMap (m' : ℕ) (f : Fin (m' + 2)) (τ : stdSimplexTop (m' + 1) ⟶ X) : stdSimplexTop m' ⟶ X :=
  simplexEquiv X m' (faceSimplex X m' f ((simplexEquiv X (m' + 1)).symm τ))

theorem faceMap_def (m' : ℕ) (f : Fin (m' + 2)) (τ : stdSimplexTop (m' + 1) ⟶ X) :
    faceMap X m' f τ = simplexEquiv X m' (faceSimplex X m' f ((simplexEquiv X (m' + 1)).symm τ)) :=
  rfl

end Source

/-! ## 3. The diagonal on the full model -/

section Diagonal

variable (p : ℕ) [NeZero p] [Fact p.Prime] (X : TopCat.{0})

/-- **The equivariant diagonal, into the full tuple model**: `Φ` followed by the inclusion of the
degree-`k` carrier. -/
def phiAll (k : ℕ) : OddWTensor p k X →+ tupAllMod (ZMod p) X p :=
  AddMonoidHom.mk' (fun x => tupIncl (ZMod p) X p k (oddDiagApp p X k x))
    (fun x y => by rw [oddDiagApp_add, map_add])

theorem phiAll_apply (k : ℕ) (x : OddWTensor p k X) :
    phiAll p X k x = tupIncl (ZMod p) X p k (oddDiagApp p X k x) := rfl

/-- **`Φ` intertwines the differentials**, on the full model. -/
theorem tupDAll_phiAll_succ (k : ℕ) (x : OddWTensor p (k + 1) X) :
    tupDAll (ZMod p) X p (phiAll p X (k + 1) x)
      = phiAll p X k (oddDiff p (oddSingularBoundary p) X k x) := by
  have h := LinearMap.congr_fun (tupIncl_comp_tupD (ZMod p) X k) (oddDiagApp p X (k + 1) x)
  simp only [LinearMap.comp_apply] at h
  rw [phiAll_apply, phiAll_apply, ← h, oddDiagApp_d]

/-- In total degree `0` there is no boundary. -/
theorem tupDAll_phiAll_zero (x : OddWTensor p 0 X) :
    tupDAll (ZMod p) X p (phiAll p X 0 x) = 0 := by
  rw [phiAll_apply]
  generalize oddDiagApp p X 0 x = y
  induction y using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add y₁ y₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, add_zero]
  | single t c =>
    rw [← Finsupp.smul_single_one, map_smul, map_smul, tupIncl_single,
      tupDAll_single_of_tot_eq_zero (ZMod p) t.1 t.2, smul_zero]

/-- **The generator of the group ring acts as the cyclic operator.** -/
theorem phiAll_grGen_smul (k : ℕ) (x : OddWTensor p k X) :
    phiAll p X k (grGen p • x) = tupTAll (ZMod p) X p (phiAll p X k x) := by
  rw [phiAll_apply, phiAll_apply, oddDiagApp_grGen]
  exact LinearMap.congr_fun (tupIncl_comp_tupT (ZMod p) X k) (oddDiagApp p X k x)

theorem phiAll_grGen_pow_smul (k n : ℕ) (x : OddWTensor p k X) :
    phiAll p X k (grGen p ^ n • x) = (tupTAll (ZMod p) X p ^ n) (phiAll p X k x) := by
  induction n with
  | zero => rw [pow_zero, one_smul, pow_zero, Module.End.one_apply]
  | succ n ih =>
    rw [pow_succ', mul_smul, phiAll_grGen_smul, ih, pow_succ', Module.End.mul_apply]

/-- A sign in the group ring comes out as a sign in `F_p`. -/
theorem phiAll_neg_one_pow_smul (k n : ℕ) (x : OddWTensor p k X) :
    phiAll p X k (((-1 : GroupRingZMod p) ^ n) • x) = ((-1 : ZMod p) ^ n) • phiAll p X k x := by
  rcases Nat.even_or_odd n with h | h
  · rw [h.neg_one_pow, h.neg_one_pow, one_smul, one_smul]
  · rw [h.neg_one_pow, h.neg_one_pow, neg_one_smul, neg_one_smul, map_neg]

/-- `Φ` is `F_p`-linear. -/
theorem phiAll_zmod_smul (k : ℕ) (r : ZMod p) (x : OddWTensor p k X) :
    phiAll p X k (r • x) = r • phiAll p X k x := by
  rw [phiAll_apply, phiAll_apply, ← map_smul]
  congr 1
  rw [← algebraMap_smul (GroupRingZMod p) r x, oddDiagApp_smul, AlgHom.commutes,
    Module.algebraMap_end_apply]

/-- The full model does not see the degree of the carrier a generator was placed in. -/
theorem phiAll_single_deg_congr {k k' : ℕ} (h : k = k') (j : ℕ) (hj : j < k + 1)
    (hj' : j < k' + 1) (σ : stdSimplexTop j ⟶ X) (c : GroupRingZMod p) :
    phiAll p X k (Finsupp.single (⟨⟨j, hj⟩, σ⟩ : WSIndex k X) c)
      = phiAll p X k' (Finsupp.single (⟨⟨j, hj'⟩, σ⟩ : WSIndex k' X) c) := by
  subst h
  rfl

/-- The boundary of `Φ` on one generator, split into its two halves. -/
theorem tupDAll_phiAll_single (k : ℕ) (q : WSIndex (k + 1) X) (c : GroupRingZMod p) :
    tupDAll (ZMod p) X p (phiAll p X (k + 1) (Finsupp.single q c))
      = phiAll p X k (c • oddDiffW p X k q.1 q.2)
        + phiAll p X k (c • oddDiffS p (oddSingularBoundary p) X k q.1 q.2) := by
  rw [tupDAll_phiAll_succ, ← Finsupp.smul_single_one, map_smul, oddDiff_single, oddDiffGen,
    smul_add, map_add]

/-! ## 4. The diagonal on a generator -/

/-- **`Φ(a, m, c, τ)`**: the diagonal on the generator `c · (e_a ⊗ τ)`, in the full model. -/
def phiG (a m : ℕ) (c : GroupRingZMod p) (τ : stdSimplexTop m ⟶ X) : tupAllMod (ZMod p) X p :=
  phiAll p X (a + m) (srcGen p X a m c τ)

theorem phiG_eq (a m : ℕ) (c : GroupRingZMod p) (τ : stdSimplexTop m ⟶ X) :
    phiG p X a m c τ
      = tupIncl (ZMod p) X p (a + m) (oddDiagApp p X (a + m)
          (Finsupp.single (⟨⟨m, Nat.lt_succ_of_le (Nat.le_add_left m a)⟩, τ⟩ : WSIndex (a + m) X) c)) :=
  rfl

theorem phiG_add (a m : ℕ) (c₁ c₂ : GroupRingZMod p) (τ : stdSimplexTop m ⟶ X) :
    phiG p X a m (c₁ + c₂) τ = phiG p X a m c₁ τ + phiG p X a m c₂ τ := by
  simp only [phiG, srcGen, Finsupp.single_add, map_add]

theorem phiG_zero_coeff (a m : ℕ) (τ : stdSimplexTop m ⟶ X) : phiG p X a m 0 τ = 0 := by
  simp only [phiG, srcGen, Finsupp.single_zero, map_zero]

theorem phiG_zmod_smul (a m : ℕ) (r : ZMod p) (c : GroupRingZMod p) (τ : stdSimplexTop m ⟶ X) :
    phiG p X a m (r • c) τ = r • phiG p X a m c τ := by
  simp only [phiG, srcGen]
  rw [← Finsupp.smul_single, phiAll_zmod_smul]

/-- The generator of the group ring acts on `Φ(a, m, c, τ)` as the cyclic operator. -/
theorem phiG_grGen_mul (a m : ℕ) (c : GroupRingZMod p) (τ : stdSimplexTop m ⟶ X) :
    phiG p X a m (grGen p * c) τ = tupTAll (ZMod p) X p (phiG p X a m c τ) := by
  simp only [phiG, srcGen]
  rw [← smul_eq_mul, ← Finsupp.smul_single, phiAll_grGen_smul]

/-- A sign in the group ring comes out as a sign in `F_p`. -/
theorem phiG_neg_one_pow_mul (a m n : ℕ) (c : GroupRingZMod p) (τ : stdSimplexTop m ⟶ X) :
    phiG p X a m ((-1 : GroupRingZMod p) ^ n * c) τ = ((-1 : ZMod p) ^ n) • phiG p X a m c τ := by
  simp only [phiG, srcGen]
  rw [← smul_eq_mul, ← Finsupp.smul_single, phiAll_neg_one_pow_smul]

/-- The cyclic shift of the exponent of `T` is the cyclic operator. -/
theorem phiG_monoGen_one_add (a m : ℕ) (s : ZMod p) (τ : stdSimplexTop m ⟶ X) :
    phiG p X a m (monoGen p (1 + s)) τ = tupTAll (ZMod p) X p (phiG p X a m (monoGen p s) τ) := by
  rw [monoGen_one_add, phiG_grGen_mul]

/-- **The resolution half** of `∂ Φ(a, m, c, τ)`: `Φ(a − 1, m, altCoeff (a − 1) · c, τ)`, and `0` at
`a = 0`. -/
def phiGW (a m : ℕ) (c : GroupRingZMod p) (τ : stdSimplexTop m ⟶ X) : tupAllMod (ZMod p) X p :=
  match a with
  | 0 => 0
  | a' + 1 => phiG p X a' m (altCoeff (grS p) (grNorm p) a' * c) τ

@[simp] theorem phiGW_zero (m : ℕ) (c : GroupRingZMod p) (τ : stdSimplexTop m ⟶ X) :
    phiGW p X 0 m c τ = 0 := rfl

@[simp] theorem phiGW_succ (a' m : ℕ) (c : GroupRingZMod p) (τ : stdSimplexTop m ⟶ X) :
    phiGW p X (a' + 1) m c τ = phiG p X a' m (altCoeff (grS p) (grNorm p) a' * c) τ := rfl

/-- **The simplicial half** of `∂ Φ(a, m, c, τ)`: `Σ_f (−1)^f Φ(a, m − 1, c, ∂_f τ)`, and `0` at
`m = 0`. -/
def phiGS (a : ℕ) (c : GroupRingZMod p) : (m : ℕ) → (stdSimplexTop m ⟶ X) → tupAllMod (ZMod p) X p
  | 0, _ => 0
  | m' + 1, τ => ∑ f : Fin (m' + 2), ((-1 : ℤ) ^ (f : ℕ)) • phiG p X a m' c (faceMap X m' f τ)

@[simp] theorem phiGS_zero (a : ℕ) (c : GroupRingZMod p) (τ : stdSimplexTop 0 ⟶ X) :
    phiGS p X a c 0 τ = 0 := rfl

@[simp] theorem phiGS_succ (a m' : ℕ) (c : GroupRingZMod p) (τ : stdSimplexTop (m' + 1) ⟶ X) :
    phiGS p X a c (m' + 1) τ
      = ∑ f : Fin (m' + 2), ((-1 : ℤ) ^ (f : ℕ)) • phiG p X a m' c (faceMap X m' f τ) := rfl

/-- **The boundary of `Φ` on a generator of total degree `0`.** -/
theorem tupDAll_phiG_zero_zero (c : GroupRingZMod p) (τ : stdSimplexTop 0 ⟶ X) :
    tupDAll (ZMod p) X p (phiG p X 0 0 c τ) = 0 :=
  tupDAll_phiAll_zero p X (srcGen p X 0 0 c τ)

/-- **The boundary of `Φ` on a generator of simplex degree `0`**: only the resolution half. -/
theorem tupDAll_phiG_succ_zero (a' : ℕ) (c : GroupRingZMod p) (τ : stdSimplexTop 0 ⟶ X) :
    tupDAll (ZMod p) X p (phiG p X (a' + 1) 0 c τ)
      = phiG p X a' 0 (altCoeff (grS p) (grNorm p) a' * c) τ := by
  show tupDAll (ZMod p) X p (phiAll p X (a' + 1)
      (Finsupp.single (⟨⟨0, by omega⟩, τ⟩ : WSIndex (a' + 1) X) c)) = _
  rw [tupDAll_phiAll_single]
  show phiAll p X a' (c • oddDiffW p X a' (Fin.castSucc ⟨0, by omega⟩) τ)
      + phiAll p X a' (c • oddDiffS p (oddSingularBoundary p) X a' ⟨0, by omega⟩ τ) = _
  rw [oddDiffS_of_val_eq_zero p X (oddSingularBoundary p) a' ⟨0, by omega⟩ rfl τ, smul_zero,
    map_zero, add_zero, oddDiffW_castSucc, smul_smul, Finsupp.smul_single_one, mul_comm,
    Fin.val_mk, Nat.sub_zero]
  rfl

/-- **The boundary of `Φ` on a generator of positive simplex degree.** -/
theorem tupDAll_phiG_succ (a m' : ℕ) (c : GroupRingZMod p) (τ : stdSimplexTop (m' + 1) ⟶ X) :
    tupDAll (ZMod p) X p (phiG p X a (m' + 1) c τ)
      = phiGW p X a (m' + 1) c τ
        + ((-1 : ZMod p) ^ a) •
          ∑ f : Fin (m' + 2), ((-1 : ℤ) ^ (f : ℕ)) • phiG p X a m' c (faceMap X m' f τ) := by
  show tupDAll (ZMod p) X p (phiAll p X (a + m' + 1)
      (Finsupp.single (⟨⟨m' + 1, by omega⟩, τ⟩ : WSIndex (a + m' + 1) X) c)) = _
  rw [tupDAll_phiAll_single]
  show phiAll p X (a + m') (c • oddDiffW p X (a + m') ⟨m' + 1, by omega⟩ τ)
      + phiAll p X (a + m')
          (c • oddDiffS p (oddSingularBoundary p) X (a + m') (Fin.succ ⟨m', by omega⟩) τ) = _
  congr 1
  · -- the resolution half
    rcases a with _ | a'
    · rw [phiGW_zero, oddDiffW_of_val_eq_last p X (0 + m') ⟨m' + 1, by omega⟩ (by simp) τ,
        smul_zero, map_zero]
    · show phiAll p X (a' + 1 + m')
          (c • oddDiffW p X (a' + 1 + m') (Fin.castSucc ⟨m' + 1, by omega⟩) τ) = _
      rw [oddDiffW_castSucc, smul_smul, Finsupp.smul_single_one, mul_comm, phiGW_succ, Fin.val_mk,
        show a' + 1 + m' - (m' + 1) = a' by omega]
      exact phiAll_single_deg_congr p X (by omega) (m' + 1) _ _ τ _
  · -- the simplicial half
    rw [oddDiffS_succ, smul_comm, phiAll_neg_one_pow_smul, Fin.val_mk, Nat.add_sub_cancel]
    congr 1
    show phiAll p X (a + m') (c • Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p)
        (fun τ' : stdSimplexTop m' ⟶ X => (⟨⟨m', by omega⟩, τ'⟩ : WSIndex (a + m') X))
        (bdRHom (GroupRingZMod p) X m' (Finsupp.single τ 1))) = _
    rw [lmapDomain_bdRHom_single, Finset.smul_sum, map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [smul_comm, map_zsmul, Finsupp.smul_single_one]
    rfl

/-- **The boundary of `Φ` on a generator**, in one statement:
`∂ Φ(a, m, c, τ) = phiGW a m c τ + (−1)^a • phiGS a c m τ`. -/
theorem tupDAll_phiG (a m : ℕ) (c : GroupRingZMod p) (τ : stdSimplexTop m ⟶ X) :
    tupDAll (ZMod p) X p (phiG p X a m c τ)
      = phiGW p X a m c τ + ((-1 : ZMod p) ^ a) • phiGS p X a c m τ := by
  cases m with
  | zero =>
    rw [phiGS_zero, smul_zero, add_zero]
    cases a with
    | zero =>
      rw [phiGW_zero]
      exact tupDAll_phiG_zero_zero p X c τ
    | succ a' =>
      rw [phiGW_succ]
      exact tupDAll_phiG_succ_zero p X a' c τ
  | succ m' =>
    rw [phiGS_succ]
    exact tupDAll_phiG_succ p X a m' c τ

end Diagonal

end CompBReal

end

end GroupApproximation.CharClass

open GroupApproximation.CharClass.CompBReal

#audit_axioms wdCAlt_wdT1
#audit_axioms wdMono_eq
#audit_axioms tupDAll_phiAll_succ
#audit_axioms phiAll_zmod_smul
#audit_axioms tupDAll_phiG_succ_zero
#audit_axioms tupDAll_phiG_succ
