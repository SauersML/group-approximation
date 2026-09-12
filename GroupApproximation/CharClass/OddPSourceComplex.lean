import GroupApproximation.CharClass.OddPSource

/-!
# `d ∘ d = 0` for `W ⊗ C(X)` at odd `p`

Four groups, exactly as at `p = 2` (`CartanSourceComplex.lean`), and only the
third is different:

* **resolution then resolution** — the two scalars are `altCoeff` at consecutive
  target degrees, so their product is `a * b` or `b * a`, which is
  `altCoeff_mul_succ`;
* **simplex then simplex** — `∂∂ = 0`, from `OddPBoundaryData.bd_bd`;
* **the two mixed terms** — at `p = 2` they are *equal* and cancel because two is
  zero.  Here they are `c · (-1)^{i-1}` and `(-1)^i · c` times the same element,
  and they cancel because `(-1)^{i-1} + (-1)^i = 0`.  That is the whole content
  of the sign carried by `oddDiffS`, and it is why the sign cannot be dropped.

The three `Finsupp` helpers are stated over an arbitrary `[CommRing R]` rather
than at the group ring; `CartanSourceComplex.lean`'s three are the `GroupRingZ2`
instances of the same statements, and are left alone.

## The one arithmetic junction

The inner differential runs at level `k + 1` and the outer at level `k`, so the
resolution scalars are `altCoeff … ((k + 1) - j.val)` and `altCoeff … (k - j'.val)`
with `j = Fin.castSucc j'`, hence `j.val = j'.val`.  The two indices are
consecutive **only because `j'.val ≤ k`**, which is what `Fin.castSucc` supplies
and what truncated subtraction would otherwise silently break.  That step is
isolated in `altCoeff_succ_junction` so that it is crossed once, with `omega`,
and never inside a rewrite.
-/

open CategoryTheory Simplicial

namespace GroupApproximation.CharClass

/-! ## 1. Scalars -/

/-- `(-1)^t + (-1)^{t+1} = 0` in any ring: the mixed-term cancellation. -/
theorem neg_one_pow_add_succ {R : Type} [CommRing R] (t : ℕ) :
    ((-1 : R) ^ t) + ((-1 : R) ^ (t + 1)) = 0 := by
  rw [pow_succ]
  ring

/-- The two consecutive resolution scalars met by `d ∘ d`, in the order in which
they arrive. -/
theorem altCoeff_mul_succ' {Λ : Type} [CommRing Λ] (a b : Λ)
    (hab : a * b = 0) (hba : b * a = 0) (i : ℕ) :
    altCoeff a b (i + 1) * altCoeff a b i = 0 := by
  rw [mul_comm]
  exact altCoeff_mul_succ a b hab hba i

/-- The index junction: for `j' : Fin (k + 1)`, `(k + 1) - (Fin.castSucc j').val`
is the successor of `k - j'.val`.  Crossed once, here, with `omega`. -/
theorem altCoeff_succ_junction (k : ℕ) (j' : Fin (k + 1)) :
    (k + 1) - (Fin.castSucc j').val = (k - j'.val) + 1 := by
  have h : (Fin.castSucc j').val = j'.val := Fin.val_castSucc j'
  have hlt : j'.val ≤ k := Nat.lt_succ_iff.mp j'.isLt
  omega

/-! ## 2. Three `Finsupp` helpers, over an arbitrary commutative ring -/

/-- A linear map is recovered from its values on the singletons. -/
theorem linearCombinationR_comp_single {R ι M : Type} [CommRing R] [AddCommGroup M]
    [Module R M] (F : (ι →₀ R) →ₗ[R] M) (z : ι →₀ R) :
    Finsupp.linearCombination R (fun a => F (Finsupp.single a (1 : R))) z = F z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | single a c => simp [Finsupp.linearCombination_single, ← map_smul, Finsupp.smul_single]

/-- `Finsupp.linearCombination` is additive in the family of values. -/
theorem linearCombinationR_add_fun {R ι M : Type} [CommRing R] [AddCommGroup M]
    [Module R M] (v w : ι → M) :
    Finsupp.linearCombination R (fun a => v a + w a)
      = Finsupp.linearCombination R v + Finsupp.linearCombination R w := by
  apply Finsupp.lhom_ext'
  intro a
  apply LinearMap.ext_ring
  simp

/-- The zero family gives the zero map. -/
theorem linearCombinationR_zero_fun {R ι M : Type} [CommRing R] [AddCommGroup M]
    [Module R M] (z : ι →₀ R) :
    Finsupp.linearCombination R (fun _ : ι => (0 : M)) z = 0 := by
  simp [Finsupp.linearCombination_apply]

/-! ## 3. The three cancellations -/

section

variable (p : ℕ) (data : OddPBoundaryData p) (X : TopCat.{0})

/-- **Resolution then resolution.**  The outer scalar is `altCoeff` one degree
below the inner one, and consecutive `altCoeff`s multiply to zero. -/
theorem altCoeff_smul_oddDiffW (k : ℕ) (n : Fin (k + 2))
    (σ : stdSimplexTop n.val ⟶ X) :
    altCoeff (grS p) (grNorm p) ((k + 1) - n.val) • oddDiffW p X k n σ = 0 := by
  revert σ
  induction n using Fin.lastCases with
  | last => intro σ; rw [oddDiffW_last, smul_zero]
  | cast j =>
      intro σ
      rw [oddDiffW_castSucc, smul_smul, altCoeff_succ_junction k j,
        altCoeff_mul_succ' (grS p) (grNorm p) (grS_mul_grNorm p) (grNorm_mul_grS p),
        zero_smul]

/-- `oddDiff` applied to a chain supported at one simplex degree. -/
theorem oddDiff_lmapDomain (k : ℕ) (m : Fin (k + 2))
    (z : (stdSimplexTop m.val ⟶ X) →₀ GroupRingZMod p) :
    oddDiff p data X k (Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p)
        (fun τ => (⟨m, τ⟩ : WSIndex (k + 1) X)) z)
      = Finsupp.linearCombination (GroupRingZMod p) (fun τ => oddDiffW p X k m τ) z
        + Finsupp.linearCombination (GroupRingZMod p)
            (fun τ => oddDiffS p data X k m τ) z := by
  rw [oddDiff, Finsupp.lmapDomain_apply, Finsupp.linearCombination_mapDomain]
  have hfun : ((fun q : WSIndex (k + 1) X => oddDiffGen p data X k q.1 q.2)
        ∘ fun τ => (⟨m, τ⟩ : WSIndex (k + 1) X))
      = fun τ => oddDiffW p X k m τ + oddDiffS p data X k m τ := rfl
  rw [hfun, linearCombinationR_add_fun, LinearMap.add_apply]

/-- **Simplex then simplex**: `∂ ∘ ∂ = 0`. -/
theorem linearCombination_oddDiffS_bd (k : ℕ) (m : Fin (k + 2))
    (z : (stdSimplexTop (m.val + 1) ⟶ X) →₀ GroupRingZMod p) :
    Finsupp.linearCombination (GroupRingZMod p) (fun τ => oddDiffS p data X k m τ)
        (data.bd X m.val z) = 0 := by
  revert z
  induction m using Fin.cases with
  | zero =>
      intro z
      have hfun : (fun τ : stdSimplexTop (0 : Fin (k + 2)).val ⟶ X =>
          oddDiffS p data X k 0 τ) = fun _ => (0 : OddWTensor p k X) :=
        funext (oddDiffS_zero p data X k)
      rw [hfun, linearCombinationR_zero_fun]
  | succ i =>
      intro z
      let F : ((stdSimplexTop (Fin.succ i).val ⟶ X) →₀ GroupRingZMod p) →ₗ[GroupRingZMod p]
          OddWTensor p k X :=
        (((-1 : GroupRingZMod p) ^ (k - i.val)) •
          (Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p)
            (fun ρ => (⟨i, ρ⟩ : WSIndex k X)))).comp (data.bd X i.val)
      have hfun : (fun τ : stdSimplexTop (Fin.succ i).val ⟶ X =>
            oddDiffS p data X k (Fin.succ i) τ)
          = fun τ => F (Finsupp.single τ (1 : GroupRingZMod p)) := by
        funext τ
        rw [oddDiffS_succ]
        rfl
      rw [hfun, linearCombinationR_comp_single]
      show F (data.bd X (Fin.succ i).val z) = 0
      show ((-1 : GroupRingZMod p) ^ (k - i.val)) •
          (Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p)
            (fun ρ => (⟨i, ρ⟩ : WSIndex k X)))
            (data.bd X i.val (data.bd X (Fin.succ i).val z)) = 0
      -- `data.bd_bd`'s statement spells the degree `i.val + 1`; the goal spells
      -- it `(Fin.succ i).val`, and that number is inside the TYPE of a `Finsupp`,
      -- so `rw` cannot cross it.  Cross it with a `have`, where defeq applies.
      have hbd : data.bd X i.val (data.bd X (Fin.succ i).val z) = 0 :=
        data.bd_bd X i.val z
      rw [hbd, map_zero, smul_zero]

/-- **The two mixed terms**, before the signs: resolution-then-simplex and
simplex-then-resolution produce the same element. -/
theorem oddMixed_terms_eq (k : ℕ) (i : Fin (k + 1))
    (σ : stdSimplexTop (Fin.succ (Fin.castSucc i)).val ⟶ X) :
    Finsupp.linearCombination (GroupRingZMod p)
        (fun τ => oddDiffW p X k (Fin.castSucc i) τ)
        (data.bd X i.val (Finsupp.single σ (1 : GroupRingZMod p)))
      = altCoeff (grS p) (grNorm p) (k - i.val) •
          Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p)
            (fun ρ => (⟨i, ρ⟩ : WSIndex k X))
            (data.bd X i.val (Finsupp.single σ (1 : GroupRingZMod p))) := by
  let G : ((stdSimplexTop (Fin.castSucc i).val ⟶ X) →₀ GroupRingZMod p) →ₗ[GroupRingZMod p]
      OddWTensor p k X :=
    altCoeff (grS p) (grNorm p) (k - i.val) •
      Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p)
        (fun ρ => (⟨i, ρ⟩ : WSIndex k X))
  have hfun : (fun τ : stdSimplexTop (Fin.castSucc i).val ⟶ X =>
        oddDiffW p X k (Fin.castSucc i) τ)
      = fun τ => G (Finsupp.single τ (1 : GroupRingZMod p)) := by
    funext τ
    rw [oddDiffW_castSucc]
    show altCoeff (grS p) (grNorm p) (k - i.val) •
        Finsupp.single (⟨i, τ⟩ : WSIndex k X) 1
      = altCoeff (grS p) (grNorm p) (k - i.val) •
        (Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p)
          (fun ρ => (⟨i, ρ⟩ : WSIndex k X)) (Finsupp.single τ 1))
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rw [hfun, linearCombinationR_comp_single]
  rfl

end

end GroupApproximation.CharClass
