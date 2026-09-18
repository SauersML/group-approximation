import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittLinPoly
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittEmbed
import GroupApproximation.Meta.AxiomGuard

/-!
# The Witt embedding from a coefficient-ring embedding (bh-met-87d, part 2)

**Target.**  `EHighArtinHasseWittEmbedStatement` (`PureCharPrimeEHighWittEmbed.lean:107`).

**Not proved: the target itself.**  What is proved is a reduction,
`eHighWittLin_wittEmbed_of_coeff`, to `EHighWittLinCoeffStatement`.  That statement asks for:

* a field `L` of characteristic `p`;
* a commutative ring `C` with an injective additive `φ : C →+ W₂(L)` that is multiplicative for
  the Witt product `eHighWittLin_mul`;
* an injective additive `j : M →+ Cⁿ` such that every `q ∈ Q` acts through a `C`-matrix `U q`.

The Witt weight calculus is proved outright (`eHighWittLin_mulVec_isWeightPoly`,
`PureCharPrimeEHighWittLinPoly`).  Given the coefficient data, `ι = φⁿ ∘ j` and
`act q = (the W₂(L)-matrix φ (U q))` satisfy the target.

**LOUD: not logically weaker.**  Both statements are true, so neither is strictly weaker than the
other as a proposition.  `EHighWittLinCoeffStatement` is strictly smaller in proof content: it no
longer mentions weight-polynomial maps, and it is pure commutative algebra over `ZMod (p²)[Q]`.

**Truth (paper, Cohen-free).**  Let `R = ZMod (p²)[Q]/ann M`.  Then `p² M = 0`, `p M ≠ 0` and `M`
is infinite, so the pure characteristic-`p` shortcut and `L = ZMod p` both fail.  The paper route:

1. Pick elements of `R` whose images mod `P` form a transcendence basis of `R/P` over `𝔽_p`.
   They give `D₀ = ZMod (p²)[σ] → R`.  An element `d` with `d mod p ≠ 0` maps outside `P`, so
   it acts injectively on `M` (coprimary).
2. Let `D'` be `D₀` localized at `(p)`.  It is local with ideals `0`, `pD'` and `D'`, and it is
   self-injective by Baer's criterion.
3. `M ↪ S⁻¹M`, and `S⁻¹M` is finite over `D'`: `R/P` is integral over `Frac(𝔽_p[σ])`, and `P^k`
   kills `M`.  So `S⁻¹M ↪ D'^s`.  Each `q` acts `D'`-linearly on `S⁻¹M`, and by injectivity of
   `D'` it extends to a `D'`-matrix on `D'^s`.
4. Take `C = D'` and `L = Frac(𝔽_p[σ])`.  The Teichmüller-type map `D' → W₂(L)` sends `t ↦ [t]`
   and `p ↦ (0, 1)`.  It is injective, additive and multiplicative for `(a₀x₀, a₀^p x₁ + a₁x₀^p)`,
   and perfectness of `L` is not needed.

**Python checks.**
* For `p = 2, 3, 5, 7`, `n ↦ (n mod p, ((n - n^p)/p) mod p)` is an injective additive and
  multiplicative map `ℤ/p² → W₂(𝔽_p)`, using the model addition and `eHighWittLin_mul`.
* For `p = 2, 3, 5`, the polynomial map `ℤ/p²[t] → W₂(𝔽_p[t])` is additive and multiplicative.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

/-- **Gap (bh-met-87d).**  A coefficient ring `C` embeds into `W₂(L)` additively and
multiplicatively for the Witt product, and `M` embeds into `Cⁿ` with `Q` acting by `C`-matrices.
It is true on paper (see the module docstring).  It is not strictly weaker than
`EHighArtinHasseWittEmbedStatement`, but it is strictly smaller in proof content. -/
def EHighWittLinCoeffStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Q : Type) [CommGroup Q], Group.FG Q →
    ∀ (M : Type) [AddCommGroup M] [Module (MonoidAlgebra (ZMod (p ^ 2)) Q) M],
      Module.Finite (MonoidAlgebra (ZMod (p ^ 2)) Q) M →
      ∀ (P : Ideal (MonoidAlgebra (ZMod (p ^ 2)) Q)) (k : ℕ),
        Primary.IsCoprimaryWith (MonoidAlgebra (ZMod (p ^ 2)) Q) M P k →
        ((p : ℕ) : MonoidAlgebra (ZMod (p ^ 2)) Q) ∈ P →
        2 ≤ k → (∃ m : M, p • m ≠ 0) → Infinite M →
      ∃ (L : Type) (_ : Field L), ringChar L = p ∧
        ∃ (C : Type) (_ : CommRing C) (φ : C →+ eHighWitt_W2 L p),
          Function.Injective φ ∧ (∀ a b : C, φ (a * b) = eHighWittLin_mul (φ a) (φ b)) ∧
          ∃ (n : ℕ) (j : M →+ (Fin n → C)) (U : Q → Fin n → Fin n → C),
            Function.Injective j ∧
            ∀ (q : Q) (m : M) (i : Fin n),
              j (MonoidAlgebra.of (ZMod (p ^ 2)) Q q • m) i = ∑ l, U q i l * j m l

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.EHighWittLinCoeffStatement

/-- **Endpoint (reduction).**  The weight-polynomial Witt embedding follows from a
coefficient-ring embedding. -/
theorem eHighWittLin_wittEmbed_of_coeff (h : EHighWittLinCoeffStatement) :
    EHighArtinHasseWittEmbedStatement := by
  intro p _ Q _ hfg M _ _ hfin P k hM hpP hk hne hinf
  obtain ⟨L, hL, hchar, C, hC, φ, hφ, hmul, n, j, U, hj, hU⟩ :=
    h p Q hfg M hfin P k hM hpP hk hne hinf
  refine ⟨L, hL, hchar, n, (AddMonoidHom.compLeft φ (Fin n)).comp j,
    fun q => eHighWittLin_mulVec (fun i l => φ (U q i l)), ?_, ?_,
    fun q => eHighWittLin_mulVec_isWeightPoly _⟩
  · intro a b hab
    apply hj
    funext i
    apply hφ
    exact congrFun hab i
  · intro q m
    funext i
    show φ (j (MonoidAlgebra.of (ZMod (p ^ 2)) Q q • m) i) =
      ∑ l, eHighWittLin_mul (φ (U q i l)) (φ (j m l))
    rw [hU q m i, map_sum]
    exact Finset.sum_congr rfl fun l _ => hmul (U q i l) (j m l)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittLin_wittEmbed_of_coeff

/-- **Composite endpoint.**  The invariant function-space criterion follows from a
coefficient-ring embedding. -/
theorem eHighWittLin_polyFun_of_coeff (h : EHighWittLinCoeffStatement) :
    EHighArtinHassePolyFunStatement :=
  eHighArtinHassePolyFun_of_wittEmbed (eHighWittLin_wittEmbed_of_coeff h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittLin_polyFun_of_coeff

/-- **Composite endpoint.**  The `e = 2` infinite mixed case follows from a coefficient-ring
embedding. -/
theorem eHighWittLin_eTwo_of_coeff (h : EHighWittLinCoeffStatement) : EHighETwoStatement :=
  eHighETwo_of_polyFun (eHighWittLin_polyFun_of_coeff h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittLin_eTwo_of_coeff

end GroupApproximation.BooneHigman.Metabelian.Coprimary
