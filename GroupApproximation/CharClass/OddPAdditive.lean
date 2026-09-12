import GroupApproximation.CharClass.OddPCochain
import GroupApproximation.CharClass.OddPCochainSum
import GroupApproximation.CharClass.OddPRedPow
import GroupApproximation.CharClass.OddPRotate
import GroupApproximation.CharClass.OddPAdditiveWeight
import GroupApproximation.CharClass.OddPNorm
import GroupApproximation.CharClass.CupOneComm
import Mathlib.FieldTheory.Finite.Basic

/-!
# The odd-primary reduced powers are additive and `F_p`-linear (plan R9)

For cocycles `u, v ∈ C^q(X; F_p)` the tensor evaluation of `(u + v)^{⊗p}` against the equivariant diagonal
`Δ` splits over the assignments `ε : Fin p → Bool` (`tupEval_add_expand`).  The two constant assignments
give `D_j(u)` and `D_j(v)`.  The mixed ones are redistributed along the rotation orbits by a weight
(`OddPAdditiveWeight.lean`), with no orbit representative chosen, and every orbit sums through `Δ` into the
norm element: `Δ (T^i • x) = T^i Δ x` moves the cochains by the rotation (the rotated E5).  On a generator
`x = e_j ⊗ σ` the norm is a boundary up to a simplicial half:

    N • x = d (c_j • (e_{j+1} ⊗ σ)) − c_j • (±e_{j+1} ⊗ ∂σ),   c_j := s^{p−2} (j even), 1 (j odd),

because `d e_{j+1} = altCoeff j • e_j` and `c_j · altCoeff j = N` (`normCofactor_mul_altCoeff`).  The
boundary evaluates to zero on a tuple of cocycles, and the simplicial half is the coboundary of an explicit
cochain.  So `D_j(u + v) = D_j(u) + D_j(v) + δΨ`, and the classes agree (`redPow_add`).

Homogeneity is `D_j(c • u) = c^p • D_j(u) = c • D_j(u)` by Fermat (`redPow_smul`).
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

variable (p : ℕ)

/-! ## 1. The group ring acts on the diagonal through the rotation -/

/-- `Δ (T^i • x) = T^i (Δ x)`. -/
theorem oddDiagApp_grGen_pow [Fact p.Prime] [NeZero p] (X : TopCat.{0}) (k i : ℕ)
    (x : OddWTensor p k X) :
    oddDiagApp p X k (grGen p ^ i • x) = (tupT (ZMod p) X p k ^ i) (oddDiagApp p X k x) := by
  induction i with
  | zero => rw [pow_zero (grGen p), one_smul, pow_zero (tupT (ZMod p) X p k), Module.End.one_apply]
  | succ i ih =>
    rw [pow_succ' (grGen p) i, mul_smul, oddDiagApp_grGen, ih, pow_succ' (tupT (ZMod p) X p k) i,
      Module.End.mul_apply]

/-- **(E5 at the diagonal)** `T^i` acting on the source moves the slot cochains. -/
theorem oddEvalHom_grGen_pow [Fact p.Prime] [NeZero p] (hp : Odd p) {X : TopCat.{0}} (k : ℕ)
    (φ : Fin p → ∀ n : ℕ, singularCochainGroup (ZMod p) X n) (q : ℕ)
    (hq : ∀ l n, n ≠ q → φ l n = 0) (i : ℕ) (x : OddWTensor p k X) :
    oddEvalHom p X k φ (grGen p ^ i • x)
      = oddEvalHom p X k (fun l => φ (((finRotate p).symm ^ i) l)) x := by
  show tupEval (ZMod p) X p k φ (oddDiagApp p X k (grGen p ^ i • x))
    = tupEval (ZMod p) X p k (fun l => φ (((finRotate p).symm ^ i) l)) (oddDiagApp p X k x)
  rw [oddDiagApp_grGen_pow, tupEval_tupT_pow_rotate (ZMod p) hp φ q hq k i]

/-- The norm sums the rotations of the slot cochains. -/
theorem oddEvalHom_grNorm_smul [Fact p.Prime] [NeZero p] (hp : Odd p) {X : TopCat.{0}} (k : ℕ)
    (φ : Fin p → ∀ n : ℕ, singularCochainGroup (ZMod p) X n) (q : ℕ)
    (hq : ∀ l n, n ≠ q → φ l n = 0) (x : OddWTensor p k X) :
    oddEvalHom p X k φ (grNorm p • x)
      = ∑ i ∈ Finset.range p, oddEvalHom p X k (fun l => φ (((finRotate p).symm ^ i) l)) x := by
  unfold grNorm
  rw [Finset.sum_smul, map_sum]
  exact Finset.sum_congr rfl fun i _ => oddEvalHom_grGen_pow p hp k φ q hq i x

/-! ## 2. The norm on a generator is a boundary up to a simplicial half -/

/-- The cofactor of the resolution's differential into `W`-degree `j` in the norm. -/
def normCofactor (j : ℕ) : GroupRingZMod p := if Even j then grS p ^ (p - 2) else 1

theorem normCofactor_mul_altCoeff [Fact p.Prime] (j : ℕ) :
    normCofactor p j * altCoeff (grS p) (grNorm p) j = grNorm p := by
  unfold normCofactor
  by_cases hj : Even j
  · rw [if_pos hj, altCoeff_even _ _ hj, mul_comm,
      ← grNorm_eq_grS_mul p (Fact.out : p.Prime).two_le]
  · rw [if_neg hj, altCoeff_odd _ _ hj, one_mul]

/-- The differential on the generator one `W`-degree up: the `W`-half is `altCoeff` times the generator. -/
theorem oddDiff_castSucc_single {X : TopCat.{0}} (k m : ℕ) (hm : m < k + 1)
    (τ : stdSimplexTop m ⟶ X) :
    oddDiff p (oddSingularBoundary p) X k
        (Finsupp.single (⟨Fin.castSucc ⟨m, hm⟩, τ⟩ : WSIndex (k + 1) X) (1 : GroupRingZMod p))
      = altCoeff (grS p) (grNorm p) (k - m) •
          Finsupp.single (⟨⟨m, hm⟩, τ⟩ : WSIndex k X) (1 : GroupRingZMod p)
        + oddDiffS p (oddSingularBoundary p) X k (Fin.castSucc ⟨m, hm⟩) τ := by
  rw [oddDiff_single]
  show oddDiffW p X k (Fin.castSucc ⟨m, hm⟩) τ
      + oddDiffS p (oddSingularBoundary p) X k (Fin.castSucc ⟨m, hm⟩) τ = _
  rw [oddDiffW_castSucc]

/-- **The norm on a generator.** -/
theorem grNorm_smul_single [Fact p.Prime] {X : TopCat.{0}} (k m : ℕ) (hm : m < k + 1)
    (τ : stdSimplexTop m ⟶ X) :
    grNorm p • Finsupp.single (⟨⟨m, hm⟩, τ⟩ : WSIndex k X) (1 : GroupRingZMod p)
      = oddDiff p (oddSingularBoundary p) X k
          (normCofactor p (k - m) •
            Finsupp.single (⟨Fin.castSucc ⟨m, hm⟩, τ⟩ : WSIndex (k + 1) X) (1 : GroupRingZMod p))
        - normCofactor p (k - m) • oddDiffS p (oddSingularBoundary p) X k (Fin.castSucc ⟨m, hm⟩) τ := by
  rw [map_smul, oddDiff_castSucc_single, smul_add, smul_smul, normCofactor_mul_altCoeff,
    add_sub_cancel_right]

/-- On a tuple of cocycles the norm of a generator evaluates to minus its scaled simplicial half. -/
theorem oddEvalHom_grNorm_smul_single [Fact p.Prime] [NeZero p] {X : TopCat.{0}} (k : ℕ)
    (φ : Fin p → ∀ n : ℕ, singularCochainGroup (ZMod p) X n)
    (hφ : ∀ l, gCoboundary (ZMod p) X (φ l) = 0) (m : ℕ) (hm : m < k + 1)
    (τ : stdSimplexTop m ⟶ X) :
    oddEvalHom p X k φ
        (grNorm p • Finsupp.single (⟨⟨m, hm⟩, τ⟩ : WSIndex k X) (1 : GroupRingZMod p))
      = - oddEvalHom p X k φ
          (normCofactor p (k - m) • oddDiffS p (oddSingularBoundary p) X k (Fin.castSucc ⟨m, hm⟩) τ) := by
  rw [grNorm_smul_single, map_sub, oddEvalHom_oddDiff_eq_zero p φ hφ, zero_sub]

/-- The coboundary is additive. -/
theorem oddCochainCoboundary_add {X : TopCat.{0}} (m : ℕ) (φ ψ : singularCochainGroup (ZMod p) X m) :
    cochainCoboundary (ZMod p) X m (φ + ψ)
      = cochainCoboundary (ZMod p) X m φ + cochainCoboundary (ZMod p) X m ψ := by
  unfold cochainCoboundary
  exact map_add _ _ _

/-! ## 3. The cochain of a generator family -/

/-- The cochain `σ ↦ (tensor evaluation of φ) (Δ (e_{k−m} ⊗ σ))` in degree `m`. -/
def oddEvalCochain [Fact p.Prime] [NeZero p] {X : TopCat.{0}} (k : ℕ)
    (φ : Fin p → ∀ n : ℕ, singularCochainGroup (ZMod p) X n) (m : ℕ) (hm : m < k + 1) :
    singularCochainGroup (ZMod p) X m :=
  cochainOfFun m fun σ => oddEvalHom p X k φ
    (Finsupp.single (⟨⟨m, hm⟩, simplexEquiv X m σ⟩ : WSIndex k X) (1 : GroupRingZMod p))

theorem oddEvalCochain_eval [Fact p.Prime] [NeZero p] {X : TopCat.{0}} (k : ℕ)
    (φ : Fin p → ∀ n : ℕ, singularCochainGroup (ZMod p) X n) (m : ℕ) (hm : m < k + 1)
    (σ : singularSimplices X m) :
    cochainEval m (oddEvalCochain p k φ m hm) σ
      = oddEvalHom p X k φ
          (Finsupp.single (⟨⟨m, hm⟩, simplexEquiv X m σ⟩ : WSIndex k X) (1 : GroupRingZMod p)) :=
  cochainEval_cochainOfFun m _ σ

/-! ## 4. The mixed part is a coboundary -/

section Mixed

variable [Fact p.Prime] [NeZero p] {X : TopCat.{0}}

/-- The slot family of an assignment. -/
abbrev slotsOf (a b : ∀ n : ℕ, singularCochainGroup (ZMod p) X n) (ε : Fin p → Bool) :
    Fin p → ∀ n : ℕ, singularCochainGroup (ZMod p) X n :=
  fun l => bif ε l then a else b

omit [Fact p.Prime] [NeZero p] in
theorem gCoboundary_slotsOf (a b : ∀ n : ℕ, singularCochainGroup (ZMod p) X n)
    (ha : gCoboundary (ZMod p) X a = 0) (hb : gCoboundary (ZMod p) X b = 0) (ε : Fin p → Bool)
    (l : Fin p) : gCoboundary (ZMod p) X (slotsOf p a b ε l) = 0 := by
  unfold slotsOf
  cases ε l
  · exact hb
  · exact ha

/-- The coefficient cochain of the mixed part: `τ ↦ Σ_ε −(w ε · (−1)^{k−n}) · L_ε (c • (e ⊗ τ))`. -/
def mixedPrimitive (a b : ∀ n : ℕ, singularCochainGroup (ZMod p) X n) (k n : ℕ) (hn : n < k + 1) :
    singularCochainGroup (ZMod p) X n :=
  cochainOfFun n fun τ => ∑ ε : Fin p → Bool,
    -(mixedWeight p ε * (-1 : ZMod p) ^ (k - n)) *
      oddEvalHom p X k (slotsOf p a b ε)
        (normCofactor p (k - (n + 1)) •
          Finsupp.single (⟨⟨n, hn⟩, simplexEquiv X n τ⟩ : WSIndex k X) (1 : GroupRingZMod p))

/-- **Additivity at cochain level, in simplex degree `n + 1`.**  With every slot a single-degree cocycle,
`D(a + b) = D(a) + D(b) + δΨ`. -/
theorem oddEvalCochain_add_succ (hp : Odd p) (a b : ∀ n : ℕ, singularCochainGroup (ZMod p) X n)
    (q : ℕ) (ha : ∀ n, n ≠ q → a n = 0) (hb : ∀ n, n ≠ q → b n = 0)
    (hδa : gCoboundary (ZMod p) X a = 0) (hδb : gCoboundary (ZMod p) X b = 0)
    (k n : ℕ) (hm : n + 1 < k + 1) :
    oddEvalCochain p k (fun _ => a + b) (n + 1) hm
      = oddEvalCochain p k (fun _ => a) (n + 1) hm + oddEvalCochain p k (fun _ => b) (n + 1) hm
        + cochainCoboundary (ZMod p) X n (mixedPrimitive p a b k n (by omega)) := by
  apply cochain_ext
  intro σ
  rw [cochainEval_add, cochainEval_add, oddEvalCochain_eval, oddEvalCochain_eval,
    oddEvalCochain_eval, cochainCoboundary_eval]
  set x : OddWTensor p k X :=
    Finsupp.single (⟨⟨n + 1, hm⟩, simplexEquiv X (n + 1) σ⟩ : WSIndex k X) (1 : GroupRingZMod p) with hx
  -- the expansion and the two constant assignments
  have hexp : oddEvalHom p X k (fun _ => a + b) x
      = ∑ ε : Fin p → Bool, oddEvalHom p X k (slotsOf p a b ε) x := by
    show tupEval (ZMod p) X p k (fun _ => a + b) (oddDiagApp p X k x)
      = ∑ ε : Fin p → Bool, tupEval (ZMod p) X p k (slotsOf p a b ε) (oddDiagApp p X k x)
    exact tupEval_add_expand (ZMod p) a b k _
  have hsplit : ∑ ε : Fin p → Bool, oddEvalHom p X k (slotsOf p a b ε) x
      = (∑ ε : Fin p → Bool, if (∃ l, ε l = true) ∧ (∃ l, ε l = false)
          then oddEvalHom p X k (slotsOf p a b ε) x else 0)
        + oddEvalHom p X k (fun _ => a) x + oddEvalHom p X k (fun _ => b) x :=
    sum_eq_mixed_add_const p _
  rw [hexp, hsplit]
  have key : (∑ ε : Fin p → Bool, if (∃ l, ε l = true) ∧ (∃ l, ε l = false)
        then oddEvalHom p X k (slotsOf p a b ε) x else 0)
      = ∑ i : Fin (n + 2), (-1 : ZMod p) ^ (i : ℕ) *
          cochainEval n (mixedPrimitive p a b k n (by omega)) (faceSimplex X n i σ) := by
    rw [← sum_weighted_rotate_eq_mixed p (fun ε => oddEvalHom p X k (slotsOf p a b ε) x)]
    -- every orbit sums into the norm, which is minus the scaled simplicial half
    have horbit : ∀ ε : Fin p → Bool,
        ∑ i ∈ Finset.range p,
            oddEvalHom p X k (slotsOf p a b (fun l => ε (((finRotate p).symm ^ i) l))) x
          = - ∑ i : Fin (n + 2), (-1 : ZMod p) ^ (k - n) * (-1 : ZMod p) ^ (i : ℕ) *
              oddEvalHom p X k (slotsOf p a b ε)
                (normCofactor p (k - (n + 1)) •
                  Finsupp.single (⟨⟨n, by omega⟩, simplexEquiv X n (faceSimplex X n i σ)⟩ : WSIndex k X)
                    (1 : GroupRingZMod p)) := by
      intro ε
      have hrot := oddEvalHom_grNorm_smul p hp k (slotsOf p a b ε) q
        (bif_concentrated (ZMod p) a b q ha hb ε) x
      have hS : oddDiffS p (oddSingularBoundary p) X k (Fin.castSucc ⟨n + 1, hm⟩)
            (simplexEquiv X (n + 1) σ)
          = ∑ i : Fin (n + 2), ((-1 : GroupRingZMod p) ^ (k - n) * (-1 : GroupRingZMod p) ^ (i : ℕ)) •
              Finsupp.single (⟨⟨n, by omega⟩, simplexEquiv X n (faceSimplex X n i σ)⟩ : WSIndex k X)
                (1 : GroupRingZMod p) :=
        oddDiffS_succ_eq_sum p k ⟨n, by omega⟩ σ
      calc ∑ i ∈ Finset.range p,
            oddEvalHom p X k (slotsOf p a b (fun l => ε (((finRotate p).symm ^ i) l))) x
          = oddEvalHom p X k (slotsOf p a b ε) (grNorm p • x) := hrot.symm
        _ = - oddEvalHom p X k (slotsOf p a b ε)
              (normCofactor p (k - (n + 1)) • oddDiffS p (oddSingularBoundary p) X k
                (Fin.castSucc ⟨n + 1, hm⟩) (simplexEquiv X (n + 1) σ)) := by
          rw [hx]
          exact oddEvalHom_grNorm_smul_single p k (slotsOf p a b ε)
            (gCoboundary_slotsOf p a b hδa hδb ε) (n + 1) hm _
        _ = _ := by
          congr 1
          rw [hS, Finset.smul_sum, map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          have hpow : ((-1 : GroupRingZMod p) ^ (k - n) * (-1 : GroupRingZMod p) ^ (i : ℕ))
              = (-1 : GroupRingZMod p) ^ (k - n + (i : ℕ)) := (pow_add _ _ _).symm
          rw [smul_comm, hpow, oddEvalHom_neg_one_pow_smul, pow_add]
    simp only [horbit, smul_eq_mul, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib,
      mixedPrimitive, cochainEval_cochainOfFun]
    refine Finset.sum_comm.trans
      (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun ε _ => ?_)
    ring
  rw [key]

/-- **Additivity at cochain level, in simplex degree `0`.**  There the simplicial half is absent. -/
theorem oddEvalCochain_add_zero (hp : Odd p) (a b : ∀ n : ℕ, singularCochainGroup (ZMod p) X n)
    (q : ℕ) (ha : ∀ n, n ≠ q → a n = 0) (hb : ∀ n, n ≠ q → b n = 0)
    (hδa : gCoboundary (ZMod p) X a = 0) (hδb : gCoboundary (ZMod p) X b = 0)
    (k : ℕ) (hm : 0 < k + 1) :
    oddEvalCochain p k (fun _ => a + b) 0 hm
      = oddEvalCochain p k (fun _ => a) 0 hm + oddEvalCochain p k (fun _ => b) 0 hm := by
  apply cochain_ext
  intro σ
  rw [cochainEval_add, oddEvalCochain_eval, oddEvalCochain_eval, oddEvalCochain_eval]
  set x : OddWTensor p k X :=
    Finsupp.single (⟨⟨0, hm⟩, simplexEquiv X 0 σ⟩ : WSIndex k X) (1 : GroupRingZMod p) with hx
  have hexp : oddEvalHom p X k (fun _ => a + b) x
      = ∑ ε : Fin p → Bool, oddEvalHom p X k (slotsOf p a b ε) x := by
    show tupEval (ZMod p) X p k (fun _ => a + b) (oddDiagApp p X k x)
      = ∑ ε : Fin p → Bool, tupEval (ZMod p) X p k (slotsOf p a b ε) (oddDiagApp p X k x)
    exact tupEval_add_expand (ZMod p) a b k _
  have hsplit : ∑ ε : Fin p → Bool, oddEvalHom p X k (slotsOf p a b ε) x
      = (∑ ε : Fin p → Bool, if (∃ l, ε l = true) ∧ (∃ l, ε l = false)
          then oddEvalHom p X k (slotsOf p a b ε) x else 0)
        + oddEvalHom p X k (fun _ => a) x + oddEvalHom p X k (fun _ => b) x :=
    sum_eq_mixed_add_const p _
  rw [hexp, hsplit]
  have key : (∑ ε : Fin p → Bool, if (∃ l, ε l = true) ∧ (∃ l, ε l = false)
        then oddEvalHom p X k (slotsOf p a b ε) x else 0) = 0 := by
    rw [← sum_weighted_rotate_eq_mixed p (fun ε => oddEvalHom p X k (slotsOf p a b ε) x)]
    refine Finset.sum_eq_zero fun ε _ => ?_
    have hrot := oddEvalHom_grNorm_smul p hp k (slotsOf p a b ε) q
      (bif_concentrated (ZMod p) a b q ha hb ε) x
    have hS : oddDiffS p (oddSingularBoundary p) X k (Fin.castSucc ⟨0, hm⟩) (simplexEquiv X 0 σ) = 0 :=
      rfl
    have hzero : oddEvalHom p X k (slotsOf p a b ε) (grNorm p • x) = 0 := by
      rw [hx, oddEvalHom_grNorm_smul_single p k (slotsOf p a b ε)
        (gCoboundary_slotsOf p a b hδa hδb ε) 0 hm, hS, smul_zero, map_zero, neg_zero]
    have horbit : ∑ i ∈ Finset.range p,
        oddEvalHom p X k (slotsOf p a b (fun l => ε (((finRotate p).symm ^ i) l))) x = 0 :=
      hrot.symm.trans hzero
    simp only [horbit, smul_zero]
  rw [key, zero_add]

/-- **Additivity of the class.**  In every simplex degree the classes of `D(a + b)`, `D(a)`, `D(b)` add. -/
theorem oddEvalCochain_class_add (hp : Odd p) (a b : ∀ n : ℕ, singularCochainGroup (ZMod p) X n)
    (q : ℕ) (ha : ∀ n, n ≠ q → a n = 0) (hb : ∀ n, n ≠ q → b n = 0)
    (hδa : gCoboundary (ZMod p) X a = 0) (hδb : gCoboundary (ZMod p) X b = 0)
    (k m : ℕ) (hm : m < k + 1)
    (h1 : cochainCoboundary (ZMod p) X m (oddEvalCochain p k (fun _ => a + b) m hm) = 0)
    (h2 : cochainCoboundary (ZMod p) X m (oddEvalCochain p k (fun _ => a) m hm) = 0)
    (h3 : cochainCoboundary (ZMod p) X m (oddEvalCochain p k (fun _ => b) m hm) = 0) :
    cocycleClassK (ZMod p) X m (oddEvalCochain p k (fun _ => a + b) m hm) h1
      = cocycleClassK (ZMod p) X m (oddEvalCochain p k (fun _ => a) m hm) h2
        + cocycleClassK (ZMod p) X m (oddEvalCochain p k (fun _ => b) m hm) h3 := by
  have h23 : cochainCoboundary (ZMod p) X m
      (oddEvalCochain p k (fun _ => a) m hm + oddEvalCochain p k (fun _ => b) m hm) = 0 := by
    rw [oddCochainCoboundary_add, h2, h3, add_zero]
  rw [← CupOneLocal.cocycleClassK_add (ZMod p) X m _ _ h2 h3 h23]
  rcases m with _ | n
  · exact cocycleClassK_congr (ZMod p) X 0 (oddEvalCochain_add_zero p hp a b q ha hb hδa hδb k hm) h1 h23
  · have hΨ : cochainCoboundary (ZMod p) X (n + 1)
        (cochainCoboundary (ZMod p) X n (mixedPrimitive p a b k n (by omega))) = 0 :=
      cochainCoboundary_cochainCoboundaryK (ZMod p) X n _
    have hsum : cochainCoboundary (ZMod p) X (n + 1)
        (oddEvalCochain p k (fun _ => a) (n + 1) hm + oddEvalCochain p k (fun _ => b) (n + 1) hm
          + cochainCoboundary (ZMod p) X n (mixedPrimitive p a b k n (by omega))) = 0 := by
      rw [oddCochainCoboundary_add, h23, hΨ, add_zero]
    rw [cocycleClassK_congr (ZMod p) X (n + 1)
        (oddEvalCochain_add_succ p hp a b q ha hb hδa hδb k n hm) h1 hsum,
      CupOneLocal.cocycleClassK_add (ZMod p) X (n + 1) _ _ h23 hΨ hsum,
      cocycleClassK_coboundary_zero, add_zero]

/-- **Homogeneity at cochain level**: scaling the cochain scales the evaluation cochain by the `p`-th power. -/
theorem oddEvalCochain_smul (c : ZMod p) (a : ∀ n : ℕ, singularCochainGroup (ZMod p) X n)
    (k m : ℕ) (hm : m < k + 1) :
    oddEvalCochain p k (fun _ => c • a) m hm = c ^ p • oddEvalCochain p k (fun _ => a) m hm := by
  apply cochain_ext
  intro σ
  rw [cochainEval_smul, oddEvalCochain_eval, oddEvalCochain_eval]
  exact tupEval_smul_const (ZMod p) c a k _

end Mixed

/-! ## 5. The classes: `D_j` and the reduced powers are additive and `F_p`-linear -/

/-- `D_j` is the generator-family cochain of the constant tuple. -/
theorem oddD_eq_oddEvalCochain [NeZero p] [Fact p.Prime] {X : TopCat.{0}} (q j : ℕ)
    (u : singularCochainGroup (ZMod p) X q) :
    oddD p q j u = oddEvalCochain p (p * q) (fun _ => Pi.single q u) (p * q - j)
      (Nat.lt_succ_of_le (Nat.sub_le _ _)) := by
  apply cochain_ext
  intro σ
  rw [oddD_eval, oddEvalCochain_eval]
  rfl

/-- **Additivity of the class of `D_j`.** -/
theorem oddD_class_add [NeZero p] [Fact p.Prime] (hp : Odd p) {X : TopCat.{0}} (q j : ℕ)
    (hj : j ≤ p * q) (u v : singularCochainGroup (ZMod p) X q)
    (hu : cochainCoboundary (ZMod p) X q u = 0) (hv : cochainCoboundary (ZMod p) X q v = 0)
    (huv : cochainCoboundary (ZMod p) X q (u + v) = 0) :
    cocycleClassK (ZMod p) X (p * q - j) (oddD p q j (u + v)) (oddD_cocycle p hp q j hj (u + v) huv)
      = cocycleClassK (ZMod p) X (p * q - j) (oddD p q j u) (oddD_cocycle p hp q j hj u hu)
        + cocycleClassK (ZMod p) X (p * q - j) (oddD p q j v) (oddD_cocycle p hp q j hj v hv) := by
  have hm : p * q - j < p * q + 1 := Nat.lt_succ_of_le (Nat.sub_le _ _)
  have e1 : oddD p q j (u + v)
      = oddEvalCochain p (p * q) (fun _ => Pi.single q u + Pi.single q v) (p * q - j) hm := by
    rw [oddD_eq_oddEvalCochain, Pi.single_add]
  have e2 : oddD p q j u = oddEvalCochain p (p * q) (fun _ => Pi.single q u) (p * q - j) hm :=
    oddD_eq_oddEvalCochain p q j u
  have e3 : oddD p q j v = oddEvalCochain p (p * q) (fun _ => Pi.single q v) (p * q - j) hm :=
    oddD_eq_oddEvalCochain p q j v
  have h1 : cochainCoboundary (ZMod p) X (p * q - j)
      (oddEvalCochain p (p * q) (fun _ => Pi.single q u + Pi.single q v) (p * q - j) hm) = 0 := by
    rw [← e1]
    exact oddD_cocycle p hp q j hj (u + v) huv
  have h2 : cochainCoboundary (ZMod p) X (p * q - j)
      (oddEvalCochain p (p * q) (fun _ => Pi.single q u) (p * q - j) hm) = 0 := by
    rw [← e2]
    exact oddD_cocycle p hp q j hj u hu
  have h3 : cochainCoboundary (ZMod p) X (p * q - j)
      (oddEvalCochain p (p * q) (fun _ => Pi.single q v) (p * q - j) hm) = 0 := by
    rw [← e3]
    exact oddD_cocycle p hp q j hj v hv
  rw [cocycleClassK_congr (ZMod p) X (p * q - j) e1 _ h1,
    cocycleClassK_congr (ZMod p) X (p * q - j) e2 _ h2,
    cocycleClassK_congr (ZMod p) X (p * q - j) e3 _ h3]
  exact oddEvalCochain_class_add p hp (Pi.single q u) (Pi.single q v) q
    (fun n hn => Pi.single_eq_of_ne hn u) (fun n hn => Pi.single_eq_of_ne hn v)
    (gCoboundary_piSingle_eq_zero (ZMod p) u hu) (gCoboundary_piSingle_eq_zero (ZMod p) v hv)
    (p * q) (p * q - j) hm h1 h2 h3

/-- **Homogeneity of the class of `D_j`**: `D_j(c • u) = c^p • D_j(u) = c • D_j(u)` (Fermat). -/
theorem oddD_class_smul [NeZero p] [Fact p.Prime] (hp : Odd p) {X : TopCat.{0}} (q j : ℕ)
    (hj : j ≤ p * q) (c : ZMod p) (u : singularCochainGroup (ZMod p) X q)
    (hu : cochainCoboundary (ZMod p) X q u = 0) (hcu : cochainCoboundary (ZMod p) X q (c • u) = 0) :
    cocycleClassK (ZMod p) X (p * q - j) (oddD p q j (c • u)) (oddD_cocycle p hp q j hj (c • u) hcu)
      = c • cocycleClassK (ZMod p) X (p * q - j) (oddD p q j u) (oddD_cocycle p hp q j hj u hu) := by
  have e : oddD p q j (c • u) = c • oddD p q j u := by
    rw [oddD_eq_oddEvalCochain p q j (c • u), oddD_eq_oddEvalCochain p q j u, Pi.single_smul,
      oddEvalCochain_smul, ZMod.pow_card]
  have hcδ : cochainCoboundary (ZMod p) X (p * q - j) (c • oddD p q j u) = 0 := by
    rw [CupOneLocal.cochainCoboundary_smul, oddD_cocycle p hp q j hj u hu, smul_zero]
  rw [cocycleClassK_congr (ZMod p) X (p * q - j) e _ hcδ,
    CupOneLocal.cocycleClassK_smul (ZMod p) X (p * q - j) c _ (oddD_cocycle p hp q j hj u hu) hcδ]

/-- **(R9) The reduced powers are additive.** -/
theorem redPow_add [Fact p.Prime] (hp : Odd p) {X : TopCat.{0}} (q i : ℕ)
    (x y : Hmod (ZMod p) X q) :
    redPow p hp q i (x + y) = redPow p hp q i x + redPow p hp q i y := by
  by_cases h : 2 * i ≤ q
  · obtain ⟨u, hu, rfl⟩ := cocycleClassK_surjective (ZMod p) X q x
    obtain ⟨v, hv, rfl⟩ := cocycleClassK_surjective (ZMod p) X q y
    have huv : cochainCoboundary (ZMod p) X q (u + v) = 0 := by
      rw [oddCochainCoboundary_add, hu, hv, add_zero]
    rw [← CupOneLocal.cocycleClassK_add (ZMod p) X q u v hu hv huv, redPow_mk p hp q i h (u + v) huv,
      redPow_mk p hp q i h u hu, redPow_mk p hp q i h v hv, ← cohCast_add,
      oddD_class_add p hp q ((q - 2 * i) * (p - 1)) (redPow_index_le p q i) u v hu hv huv]
  · rw [redPow_eq_zero_of_lt p hp q i (by omega), redPow_eq_zero_of_lt p hp q i (by omega),
      redPow_eq_zero_of_lt p hp q i (by omega), add_zero]

/-- **The reduced powers are `F_p`-linear.** -/
theorem redPow_smul [Fact p.Prime] (hp : Odd p) {X : TopCat.{0}} (q i : ℕ) (c : ZMod p)
    (x : Hmod (ZMod p) X q) : redPow p hp q i (c • x) = c • redPow p hp q i x := by
  by_cases h : 2 * i ≤ q
  · obtain ⟨u, hu, rfl⟩ := cocycleClassK_surjective (ZMod p) X q x
    have hcu : cochainCoboundary (ZMod p) X q (c • u) = 0 := by
      rw [CupOneLocal.cochainCoboundary_smul, hu, smul_zero]
    rw [← CupOneLocal.cocycleClassK_smul (ZMod p) X q c u hu hcu, redPow_mk p hp q i h (c • u) hcu,
      redPow_mk p hp q i h u hu, ← cohCast_smul,
      oddD_class_smul p hp q ((q - 2 * i) * (p - 1)) (redPow_index_le p q i) c u hu hcu]
  · rw [redPow_eq_zero_of_lt p hp q i (by omega), redPow_eq_zero_of_lt p hp q i (by omega),
      smul_zero]

/-- **The reduced power as a linear map** `H^q(X; F_p) →ₗ H^{q + 2i(p−1)}(X; F_p)`. -/
def redPowLin [Fact p.Prime] (hp : Odd p) (X : TopCat.{0}) (q i : ℕ) :
    Hmod (ZMod p) X q →ₗ[ZMod p] Hmod (ZMod p) X (q + 2 * i * (p - 1)) where
  toFun := redPow p hp q i
  map_add' := redPow_add p hp q i
  map_smul' c x := redPow_smul p hp q i c x

@[simp] theorem redPowLin_apply [Fact p.Prime] (hp : Odd p) (X : TopCat.{0}) (q i : ℕ)
    (x : Hmod (ZMod p) X q) : redPowLin p hp X q i x = redPow p hp q i x := rfl

theorem redPow_zero [Fact p.Prime] (hp : Odd p) {X : TopCat.{0}} (q i : ℕ) :
    redPow p hp q i (0 : Hmod (ZMod p) X q) = 0 :=
  map_zero (redPowLin p hp X q i)

theorem redPow_neg [Fact p.Prime] (hp : Odd p) {X : TopCat.{0}} (q i : ℕ) (x : Hmod (ZMod p) X q) :
    redPow p hp q i (-x) = -redPow p hp q i x :=
  map_neg (redPowLin p hp X q i) x

#audit_axioms oddEvalHom_grGen_pow
#audit_axioms oddEvalCochain_add_succ
#audit_axioms oddEvalCochain_class_add
#audit_axioms oddEvalCochain_smul
#audit_axioms redPow_add
#audit_axioms redPow_smul
#audit_axioms redPowLin

end

end GroupApproximation.CharClass
