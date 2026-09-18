import Mathlib.RingTheory.Ideal.Operations
import GroupApproximation.BooneHigman.Primary.Coprimary
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEOneProof
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighCoprimaryTrans
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighCoprimaryFp
import GroupApproximation.Meta.AxiomGuard

/-!
# The exponent-`p` layer of the coprimary high-exponent case (bh-met-79)

* `eHighCoprimary_pow_nsmul_eq_zero`: if `M` is coprimary with prime `P` and exponent `k`, and
  `(p : R) ∈ P`, then `p ^ k • M = 0`.
* `eHighCoprimary_two_le_of_nsmul_ne_zero`: so if `p • M ≠ 0`, then `2 ≤ k`.
* `eHighCoprimary_exists_gl_of_nsmul_eq_zero`: **the sub-case `p • M = 0` is proved
  outright.**  `M` descends to a finite `F_p[Q]`-module (`PureCharPrimeEHighCoprimaryFp`).  The
  proved `e = 1` theorem `pureCharPrimeEOne` embeds it additively into `K^d`, and the
  translation trick (`PureCharPrimeEHighCoprimaryTrans`) turns that into the multiplicative
  form in `GL_{d+1}(K)`.  This needs no coprimary hypothesis at all.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

/-- A coprimary module whose prime contains `p` is killed by `p ^ k`, where `k` is the
coprimary exponent. -/
theorem eHighCoprimary_pow_nsmul_eq_zero {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {P : Ideal R} {k p : ℕ} (hM : Primary.IsCoprimaryWith R M P k)
    (hp : (p : R) ∈ P) (x : M) : p ^ k • x = 0 := by
  have h := hM.smul_eq_zero_of_mem_pow _ (Ideal.pow_mem_pow hp k) x
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul R] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighCoprimary_pow_nsmul_eq_zero

/-- If `p • M ≠ 0` for a coprimary `M` whose prime contains `p`, then the coprimary exponent
`k` is at least `2`. -/
theorem eHighCoprimary_two_le_of_nsmul_ne_zero {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {P : Ideal R} {k p : ℕ} (hM : Primary.IsCoprimaryWith R M P k)
    (hp : (p : R) ∈ P) (hne : ∃ m : M, p • m ≠ 0) : 2 ≤ k := by
  obtain ⟨m, hm⟩ := hne
  have h0 := eHighCoprimary_pow_nsmul_eq_zero hM hp m
  by_contra hk
  have hk' : k = 0 ∨ k = 1 := by omega
  rcases hk' with rfl | rfl
  · rw [pow_zero, one_nsmul] at h0
    exact hm (by rw [h0, nsmul_zero])
  · rw [pow_one] at h0
    exact hm h0

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighCoprimary_two_le_of_nsmul_ne_zero

/-- **The exponent-`p` sub-case, proved outright.**  A finite `(ℤ/p^e)[Q]`-module `M` with
`p • M = 0`, for `Q` f.g. abelian, embeds multiplicatively into `GL_{d}(K)` with
`ringChar K = p`, and the `Q`-action is conjugation by a representation `ρ`. -/
theorem eHighCoprimary_exists_gl_of_nsmul_eq_zero {p : ℕ} (hp : p.Prime) (e : ℕ) {Q : Type}
    [CommGroup Q] (hfg : Group.FG Q) (M : Type) [AddCommGroup M]
    [Module (MonoidAlgebra (ZMod (p ^ e)) Q) M]
    (hfin : Module.Finite (MonoidAlgebra (ZMod (p ^ e)) Q) M) (hpM : ∀ m : M, p • m = 0) :
    ∃ (K : Type) (_ : Field K) (d : ℕ)
      (κ : Multiplicative M →* Matrix.GeneralLinearGroup (Fin d) K)
      (ρ : Q →* Matrix.GeneralLinearGroup (Fin d) K),
      ringChar K = p ∧ Function.Injective κ ∧
        ∀ (q : Q) (m : M),
          κ (Multiplicative.ofAdd (MonoidAlgebra.of (ZMod (p ^ e)) Q q • m)) =
            ρ q * κ (Multiplicative.ofAdd m) * (ρ q)⁻¹ := by
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  letI : Module (ZMod p) M := AddCommGroup.zmodModule hpM
  letI : Module (MonoidAlgebra (ZMod p) Q) M := eHighCoprimaryFpModule p e Q M
  have hof : ∀ (q : Q) (m : M),
      MonoidAlgebra.of (ZMod p) Q q • m = MonoidAlgebra.of (ZMod (p ^ e)) Q q • m :=
    fun q m => eHighCoprimaryAlgHom_of (p := p) (e := e) q m
  have hfin' : Module.Finite (MonoidAlgebra (ZMod p) Q) M := eHighCoprimaryFp_finite hof hfin
  obtain ⟨K, hK, d, ι, ρ, hchar, hι, hequiv⟩ :=
    pureCharPrimeEOne p hp Q (fun a b => mul_comm a b) hfg M hfin'
  obtain ⟨κ', ρ', hκ', hrel⟩ := eHighCoprimary_exists_gl_of_additive
    (fun (q : Q) (m : M) => MonoidAlgebra.of (ZMod (p ^ e)) Q q • m) ι ρ hι
    (fun q m => (congrArg ι (hof q m)).symm.trans (hequiv q m))
  exact ⟨K, hK, d + 1, κ', ρ', hchar, hκ', hrel⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighCoprimary_exists_gl_of_nsmul_eq_zero

end GroupApproximation.BooneHigman.Metabelian.Coprimary
