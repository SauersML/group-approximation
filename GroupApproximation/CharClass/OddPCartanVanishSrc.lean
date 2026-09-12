import GroupApproximation.CharClass.OddPDiagonal
import GroupApproximation.CharClass.OddPShufflePrimRoot
import GroupApproximation.Meta.AxiomGuard

/-!
# The chain map `Φ ∘ (A_r ⊗ 1)` for the bad-residue vanishing

For a natural number `r` prime to `p` the resolution `W` carries a chain map `A_r : W → W`,
semilinear for the ring automorphism `T ↦ T ^ r` of `F_p[ℤ/p]`:

  `A_r(e_{2m}) = r^m e_{2m}`,   `A_r(e_{2m+1}) = r^m (1 + T + ⋯ + T^{r−1}) e_{2m+1}`.

It is a chain map because `(1 + ⋯ + T^{r−1})(T − 1) = T^r − 1` and `N · (1 + ⋯ + T^{r−1}) = r · N`,
where the norm `N` is fixed by `T ↦ T ^ r` (a reindexing, `r` being a unit mod `p`).

This file does not build `A_r` itself.  It builds the composite `Φ ∘ (A_r ⊗ 1)` directly on the
free source, as `vanSrc p r hr : oddSrc ⟶ oddTgt p p r`: on a generator `e_i ⊗ σ` it is
`vanCoef p r i` acting through `T` on `Φ(e_i ⊗ σ)`, extended linearly over the group ring acting
on the target through `T ^ r`.  The chain-map identity reduces to `galAlgHomP_vanCoef_succ`, the
two group-ring identities above; the simplicial half of the differential is a `ℤ`-combination of
generators of one `W`-index (`addHom_oddDiffS_succ_eq`), on which the two sides agree.

In degree `0` the composite is `Φ` itself (`vanSrc_app_f_zero`).
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

namespace OddPCartanVanish

/-! ## 1. Group-ring identities -/

section GroupRing

variable (p : ℕ)

/-- `N_r = 1 + T + ⋯ + T^{r−1}`. -/
def grNr (r : ℕ) : GroupRingZMod p := ∑ l ∈ Finset.range r, grGen p ^ l

/-- **The coefficient of `A_r` on the generator `e_i`**: `r^m` on `e_{2m}`, `r^m N_r` on
`e_{2m+1}`. -/
def vanCoef (r i : ℕ) : GroupRingZMod p :=
  (r : GroupRingZMod p) ^ (i / 2) * (if Even i then 1 else grNr p r)

theorem grNr_mul_grS (r : ℕ) : grNr p r * grS p = grGen p ^ r - 1 := by
  unfold grNr grS
  exact geom_sum_mul (grGen p) r

theorem grGen_mul_grNorm : grGen p * grNorm p = grNorm p := by
  have h1 : ∑ i ∈ Finset.range (p + 1), grGen p ^ i
      = ∑ i ∈ Finset.range p, grGen p ^ (i + 1) + 1 := by
    rw [Finset.sum_range_succ', pow_zero]
  have h2 : ∑ i ∈ Finset.range (p + 1), grGen p ^ i = ∑ i ∈ Finset.range p, grGen p ^ i + 1 := by
    rw [Finset.sum_range_succ, grGen_pow_card]
  have h3 : grGen p * grNorm p = ∑ i ∈ Finset.range p, grGen p ^ (i + 1) := by
    unfold grNorm
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (pow_succ' (grGen p) i).symm
  rw [h3]
  exact add_right_cancel (h1.symm.trans h2)

theorem grGen_pow_mul_grNorm (l : ℕ) : grGen p ^ l * grNorm p = grNorm p := by
  induction l with
  | zero => rw [pow_zero, one_mul]
  | succ l ih => rw [pow_succ', mul_assoc, ih, grGen_mul_grNorm]

theorem grNorm_mul_grNr (r : ℕ) : grNorm p * grNr p r = (r : GroupRingZMod p) * grNorm p := by
  unfold grNr
  rw [Finset.mul_sum]
  have h : ∀ l ∈ Finset.range r, grNorm p * grGen p ^ l = grNorm p := fun l _ => by
    rw [mul_comm]
    exact grGen_pow_mul_grNorm p l
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end GroupRing

/-! ## 2. The same identities through `galAlgHomP` -/

section Operators

variable {p : ℕ} [NeZero p] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

theorem galAlgHomP_grGen (hp : 1 < p) (τ : Module.End (ZMod p) V) (hτ : τ ^ p = 1) :
    galAlgHomP τ hτ (grGen p) = τ := by
  unfold galAlgHomP grGen
  rw [MonoidAlgebra.lift_single, one_smul]
  show τ ^ ((1 : ZMod p)).val = τ
  rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hp, pow_one]

/-- **The norm is fixed by `T ↦ T ^ r`**, for `r` prime to `p`: a reindexing of the powers of
`T` along multiplication by `r` on `ℤ/p` (lx-redpow's `mulPerm`). -/
theorem galAlgHomP_grNorm_of_eq_pow (hp : p.Prime) (τ σ : Module.End (ZMod p) V)
    (hτ : τ ^ p = 1) (hσ : σ ^ p = 1) (r : ℕ) (hr : Nat.Coprime r p) (hστ : σ = τ ^ r) :
    galAlgHomP σ hσ (grNorm p) = galAlgHomP τ hτ (grNorm p) := by
  simp only [grNorm, map_sum, map_pow, galAlgHomP_grGen hp.one_lt]
  rw [hστ]
  have hre : ∀ j ∈ Finset.range p, (τ ^ r) ^ j = τ ^ ((r * j) % p) := fun j _ => by
    rw [← pow_mul, pow_mod_of_pow_card_eq_one hτ]
  have h1 : ∑ j ∈ Finset.range p, τ ^ ((r * j) % p) = ∑ j : Fin p, τ ^ ((r * j.val) % p) :=
    (Fin.sum_univ_eq_sum_range (fun j => τ ^ ((r * j) % p)) p).symm
  have h2 : ∑ j ∈ Finset.range p, τ ^ j = ∑ j : Fin p, τ ^ j.val :=
    (Fin.sum_univ_eq_sum_range (fun j => τ ^ j) p).symm
  have h3 : ∑ j : Fin p, τ ^ ((r * j.val) % p) = ∑ j : Fin p, τ ^ j.val := by
    have h := Equiv.sum_comp (mulPerm p r hr) (fun j : Fin p => τ ^ j.val)
    simp only [mulPerm_val] at h
    exact h
  rw [Finset.sum_congr rfl hre, h1, h3, ← h2]

/-- **The chain-map identity of `A_r`**, as operators: the coefficient one degree up times the
differential of `W` equals the twisted differential times the coefficient. -/
theorem galAlgHomP_vanCoef_succ (hp : p.Prime) (τ σ : Module.End (ZMod p) V)
    (hτ : τ ^ p = 1) (hσ : σ ^ p = 1) (r : ℕ) (hr : Nat.Coprime r p) (hστ : σ = τ ^ r) (i : ℕ) :
    galAlgHomP τ hτ (vanCoef p r (i + 1)) * galAlgHomP τ hτ (altCoeff (grS p) (grNorm p) i)
      = galAlgHomP σ hσ (altCoeff (grS p) (grNorm p) i) * galAlgHomP τ hτ (vanCoef p r i) := by
  rcases Nat.even_or_odd i with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have he : Even (m + m) := ⟨m, rfl⟩
    have ho : ¬ Even (m + m + 1) := by
      rw [Nat.not_even_iff_odd]
      exact ⟨m, by omega⟩
    have hS : galAlgHomP σ hσ (grS p) = galAlgHomP τ hτ (grGen p ^ r - 1) := by
      rw [grS, map_sub, map_one, galAlgHomP_grGen hp.one_lt, map_sub, map_pow, map_one,
        galAlgHomP_grGen hp.one_lt, hστ]
    rw [altCoeff_even _ _ he, ← map_mul, hS, ← map_mul]
    congr 1
    rw [vanCoef, vanCoef, if_neg ho, if_pos he, show (m + m + 1) / 2 = m by omega,
      show (m + m) / 2 = m by omega, mul_one, mul_assoc, grNr_mul_grS, mul_comm]
  · have he : Even (2 * m + 1 + 1) := ⟨m + 1, by omega⟩
    have ho : ¬ Even (2 * m + 1) := by
      rw [Nat.not_even_iff_odd]
      exact ⟨m, rfl⟩
    rw [altCoeff_odd _ _ ho, ← map_mul, galAlgHomP_grNorm_of_eq_pow hp τ σ hτ hσ r hr hστ,
      ← map_mul]
    congr 1
    rw [vanCoef, vanCoef, if_pos he, if_neg ho, show (2 * m + 1 + 1) / 2 = m + 1 by omega,
      show (2 * m + 1) / 2 = m by omega, mul_one, mul_left_comm, grNorm_mul_grNr, ← mul_assoc,
      ← pow_succ]

end Operators

/-! ## 3. The composite on the free source -/

section Source

variable (p : ℕ) [NeZero p] [Fact p.Prime]

omit [NeZero p] [Fact p.Prime] in
/-- The simplicial half of the differential, against two additive maps agreeing on the generators
of one `W`-index: it is a `ℤ`-combination of those generators. -/
theorem addHom_oddDiffS_succ_eq {X : TopCat.{0}} {M : Type} [AddCommGroup M] (k : ℕ)
    (m : Fin (k + 1)) (F₁ F₂ : OddWTensor p k X →+ M)
    (hF : ∀ τ : stdSimplexTop m.val ⟶ X,
      F₁ (Finsupp.single (⟨m, τ⟩ : WSIndex k X) 1) = F₂ (Finsupp.single (⟨m, τ⟩ : WSIndex k X) 1))
    (σ : stdSimplexTop (m.val + 1) ⟶ X) :
    F₁ (oddDiffS p (oddSingularBoundary p) X k (Fin.succ m) σ)
      = F₂ (oddDiffS p (oddSingularBoundary p) X k (Fin.succ m) σ) := by
  have key : ∀ F : OddWTensor p k X →+ M,
      F (Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p) (fun τ => (⟨m, τ⟩ : WSIndex k X))
          ((oddSingularBoundary p).bd X m.val (Finsupp.single σ (1 : GroupRingZMod p))))
        = ∑ i : Fin (m.val + 2), ((-1 : ℤ) ^ (i : ℕ)) •
            F (Finsupp.single (⟨m, simplexEquiv X m.val
              (faceSimplex X m.val i ((simplexEquiv X (m.val + 1)).symm σ))⟩ : WSIndex k X) 1) := by
    intro F
    have hb : (oddSingularBoundary p).bd X m.val (Finsupp.single σ (1 : GroupRingZMod p))
        = Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p) (simplexEquiv X m.val)
            ((((singFreeR (GroupRingZMod p)).obj X).d (m.val + 1) m.val).hom
              (Finsupp.single ((simplexEquiv X (m.val + 1)).symm σ) 1)) := by
      show bdRHom (GroupRingZMod p) X m.val (Finsupp.single σ 1) = _
      rw [bdRHom_apply, Finsupp.mapDomain_single, Finsupp.lmapDomain_apply]
    rw [hb, singFreeR_d_single, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, map_zsmul, map_zsmul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rw [oddDiffS_succ]
  rcases Nat.even_or_odd (k - m.val) with he | he
  · rw [he.neg_one_pow, one_smul, key F₁, key F₂]
    exact Finset.sum_congr rfl fun i _ => by rw [hF]
  · rw [he.neg_one_pow, neg_one_smul, map_neg, map_neg, key F₁, key F₂]
    exact congrArg Neg.neg (Finset.sum_congr rfl fun i _ => by rw [hF])

omit [Fact p.Prime] in
theorem oddDiagApp_zero_elem [Fact p.Prime] (X : TopCat.{0}) (k : ℕ) :
    oddDiagApp p X k 0 = 0 :=
  map_zero (((oddDiagonal p p 1 (dvd_mul_left p 1)).app X).f k).hom

/-- **`Φ ∘ (A_r ⊗ 1)` on a generator**: the coefficient `vanCoef p r i`, acting through `T`, on the
diagonal of the generator. -/
def vanGen (X : TopCat.{0}) (k r : ℕ) (q : WSIndex k X) : tupMod (ZMod p) X p k :=
  galAlgHomP (tupT (ZMod p) X p k ^ 1) (tupT_pow_pow p X p k 1 (dvd_mul_left p 1))
    (vanCoef p r (k - q.1.val)) (oddDiagApp p X k (Finsupp.single q (1 : GroupRingZMod p)))

/-- **`Φ ∘ (A_r ⊗ 1)`** in degree `k`, linear over the group ring acting on the target through
`T ^ r`. -/
def vanSrcLin (X : TopCat.{0}) (k r : ℕ) :
    @LinearMap (GroupRingZMod p) (GroupRingZMod p) _ _ (RingHom.id (GroupRingZMod p))
      (OddWTensor p k X) (tupMod (ZMod p) X p k) _ _ _ (tupModule p X p k r (dvd_mul_left p r)) :=
  letI := tupModule p X p k r (dvd_mul_left p r)
  Finsupp.linearCombination (GroupRingZMod p) (vanGen p X k r)

theorem vanSrcLin_single (X : TopCat.{0}) (k r : ℕ) (q : WSIndex k X) :
    vanSrcLin p X k r (Finsupp.single q 1) = vanGen p X k r q := by
  letI := tupModule p X p k r (dvd_mul_left p r)
  rw [vanSrcLin, Finsupp.linearCombination_single, one_smul]

/-- The resolution half of the chain-map identity. -/
theorem vanW (X : TopCat.{0}) (k r : ℕ) (hr : Nat.Coprime r p) (n : Fin (k + 2))
    (σ : stdSimplexTop n.val ⟶ X) :
    galAlgHomP (tupT (ZMod p) X p k ^ 1) (tupT_pow_pow p X p k 1 (dvd_mul_left p 1))
        (vanCoef p r (k + 1 - n.val)) (oddDiagApp p X k (oddDiffW p X k n σ))
      = vanSrcLin p X k r (oddDiffW p X k n σ) := by
  revert σ
  induction n using Fin.lastCases with
  | last =>
    intro σ
    rw [oddDiffW_last, oddDiagApp_zero_elem, map_zero, map_zero]
  | cast j =>
    intro σ
    have hR : vanSrcLin p X k r (altCoeff (grS p) (grNorm p) (k - j.val) •
          Finsupp.single (⟨j, σ⟩ : WSIndex k X) (1 : GroupRingZMod p))
        = galAlgHomP (tupT (ZMod p) X p k ^ r) (tupT_pow_pow p X p k r (dvd_mul_left p r))
            (altCoeff (grS p) (grNorm p) (k - j.val))
            (vanSrcLin p X k r (Finsupp.single (⟨j, σ⟩ : WSIndex k X) 1)) :=
      LinearMap.map_smul (vanSrcLin p X k r) _ _
    have hidx : k + 1 - (Fin.castSucc j).val = (k - j.val) + 1 := by
      rw [Fin.coe_castSucc]
      have := j.2
      omega
    rw [oddDiffW_castSucc, hR, vanSrcLin_single, vanGen, oddDiagApp_smul, hidx,
      ← Module.End.mul_apply, ← Module.End.mul_apply,
      galAlgHomP_vanCoef_succ (Fact.out : p.Prime) (tupT (ZMod p) X p k ^ 1)
        (tupT (ZMod p) X p k ^ r) (tupT_pow_pow p X p k 1 (dvd_mul_left p 1))
        (tupT_pow_pow p X p k r (dvd_mul_left p r)) r hr (by rw [pow_one]) (k - j.val)]
    rfl

/-- The simplicial half of the chain-map identity. -/
theorem vanS (X : TopCat.{0}) (k r : ℕ) (n : Fin (k + 2)) (σ : stdSimplexTop n.val ⟶ X) :
    galAlgHomP (tupT (ZMod p) X p k ^ 1) (tupT_pow_pow p X p k 1 (dvd_mul_left p 1))
        (vanCoef p r (k + 1 - n.val))
        (oddDiagApp p X k (oddDiffS p (oddSingularBoundary p) X k n σ))
      = vanSrcLin p X k r (oddDiffS p (oddSingularBoundary p) X k n σ) := by
  revert σ
  induction n using Fin.cases with
  | zero =>
    intro σ
    rw [oddDiffS_zero, oddDiagApp_zero_elem, map_zero, map_zero]
  | succ m =>
    intro σ
    have hidx : k + 1 - (Fin.succ m).val = k - m.val := by
      rw [Fin.val_succ]
      omega
    rw [hidx]
    exact addHom_oddDiffS_succ_eq p k m
      ((galAlgHomP (tupT (ZMod p) X p k ^ 1) (tupT_pow_pow p X p k 1 (dvd_mul_left p 1))
          (vanCoef p r (k - m.val))).toAddMonoidHom.comp
        (((oddDiagonal p p 1 (dvd_mul_left p 1)).app X).f k).hom.toAddMonoidHom)
      (vanSrcLin p X k r).toAddMonoidHom
      (fun τ => (vanSrcLin_single p X k r ⟨m, τ⟩).symm) σ

/-- **The chain-map identity on a generator.** -/
theorem vanSrcLin_d (X : TopCat.{0}) (k r : ℕ) (hr : Nat.Coprime r p) (q : WSIndex (k + 1) X) :
    tupD (ZMod p) X p k (vanSrcLin p X (k + 1) r (Finsupp.single q 1))
      = vanSrcLin p X k r (oddDiff p (oddSingularBoundary p) X k (Finsupp.single q 1)) := by
  obtain ⟨n, σ⟩ := q
  rw [vanSrcLin_single, vanGen,
    galAlgHomP_comm p (tupT (ZMod p) X p (k + 1) ^ 1)
      (tupT_pow_pow p X p (k + 1) 1 (dvd_mul_left p 1)) (tupT (ZMod p) X p k ^ 1)
      (tupT_pow_pow p X p k 1 (dvd_mul_left p 1)) (tupD (ZMod p) X p k)
      (fun v => (tupT_pow_tupD (ZMod p) k 1 v).symm),
    oddDiagApp_d, oddDiff_single, oddDiffGen, oddDiagApp_add, map_add, map_add]
  exact congrArg₂ (· + ·) (vanW p X k r hr n σ) (vanS p X k r n σ)

/-- **Naturality on a generator.** -/
theorem vanSrcLin_natural {X Y : TopCat.{0}} (f : X ⟶ Y) (k r : ℕ) (q : WSIndex k X) :
    tupMap (ZMod p) f p k (vanSrcLin p X k r (Finsupp.single q 1))
      = vanSrcLin p Y k r
          (Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p) (srcMapIdx f k)
            (Finsupp.single q 1)) := by
  rw [vanSrcLin_single, vanGen,
    galAlgHomP_comm p (tupT (ZMod p) X p k ^ 1) (tupT_pow_pow p X p k 1 (dvd_mul_left p 1))
      (tupT (ZMod p) Y p k ^ 1) (tupT_pow_pow p Y p k 1 (dvd_mul_left p 1)) (tupMap (ZMod p) f p k)
      (fun v => (tupT_pow_tupMap (ZMod p) f k 1 v).symm),
    oddDiagApp_natural, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, vanSrcLin_single, vanGen]
  rfl

/-- The degree-`k` component, as a morphism over the group ring. -/
def vanSrcHom (X : TopCat.{0}) (k r : ℕ) :
    ((oddSrc p (oddSingularBoundary p)).obj X).X k
      ⟶ ((oddTgt p p r (dvd_mul_left p r)).obj X).X k :=
  letI := tupModule p X p k r (dvd_mul_left p r)
  ModuleCat.ofHom (vanSrcLin p X k r)

/-- `Φ ∘ (A_r ⊗ 1)` at one space, as a map of complexes. -/
def vanSrcCx (X : TopCat.{0}) (r : ℕ) (hr : Nat.Coprime r p) :
    (oddSrc p (oddSingularBoundary p)).obj X ⟶ (oddTgt p p r (dvd_mul_left p r)).obj X where
  f k := vanSrcHom p X k r
  comm' i j hij := by
    have hij' : j + 1 = i := hij
    subst hij'
    rw [oddSrc_obj_d, oddTgt_obj_d]
    letI := tupModule p X p (j + 1) r (dvd_mul_left p r)
    letI := tupModule p X p j r (dvd_mul_left p r)
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro q
    apply LinearMap.ext_ring
    show tupD (ZMod p) X p j (vanSrcLin p X (j + 1) r (Finsupp.single q 1))
      = vanSrcLin p X j r (oddDiff p (oddSingularBoundary p) X j (Finsupp.single q 1))
    exact vanSrcLin_d p X j r hr q

/-- **`Φ ∘ (A_r ⊗ 1)` as a natural transformation** `oddSrc ⟶ oddTgt p p r`. -/
def vanSrc (r : ℕ) (hr : Nat.Coprime r p) :
    oddSrc p (oddSingularBoundary p) ⟶ oddTgt p p r (dvd_mul_left p r) where
  app X := vanSrcCx p X r hr
  naturality X Y f := by
    refine HomologicalComplex.hom_ext _ _ fun k => ?_
    letI := tupModule p X p k r (dvd_mul_left p r)
    letI := tupModule p Y p k r (dvd_mul_left p r)
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro q
    apply LinearMap.ext_ring
    show vanSrcLin p Y k r ((((oddSrc p (oddSingularBoundary p)).map f).f k).hom
        (Finsupp.single q 1))
      = tupMap (ZMod p) f p k (vanSrcLin p X k r (Finsupp.single q 1))
    rw [vanSrcLin_natural p f k r q]
    rfl

theorem vanSrc_app_f_apply (r : ℕ) (hr : Nat.Coprime r p) (X : TopCat.{0}) (k : ℕ)
    (x : OddWTensor p k X) :
    (((vanSrc p r hr).app X).f k).hom x = vanSrcLin p X k r x :=
  rfl

/-- **In degree `0` the composite is the diagonal.** -/
theorem vanSrc_app_f_zero (r : ℕ) (hr : Nat.Coprime r p) (X : TopCat.{0}) (q : WSIndex 0 X) :
    (((vanSrc p r hr).app X).f 0).hom (Finsupp.single q 1)
      = oddDiagApp p X 0 (Finsupp.single q 1) := by
  rw [vanSrc_app_f_apply, vanSrcLin_single, vanGen, Nat.zero_sub, vanCoef, Nat.zero_div, pow_zero,
    if_pos (⟨0, rfl⟩ : Even 0), mul_one, map_one, Module.End.one_apply]

end Source

end OddPCartanVanish

end

end GroupApproximation.CharClass
