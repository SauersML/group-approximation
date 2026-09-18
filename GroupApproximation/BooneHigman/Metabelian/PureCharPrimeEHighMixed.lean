import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighMixedFinite
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighCoprimaryMixed
import GroupApproximation.Meta.AxiomGuard

/-!
# The mixed coprimary gap: finite modules are discharged (bh-met-84)

Gap of the lane: `EHighCoprimaryMixedStatement` (`PureCharPrimeEHighCoprimaryMixed.lean:35`).
It covers finite coprimary `(ℤ/p^e)[Q]`-modules with `p ∈ P`, `2 ≤ k` and `p • M ≠ 0`.

**What is proved here.**  Every *finite* `M` is discharged unconditionally
(`eHighMixed_exists_gl_of_finite_charP`, `PureCharPrimeEHighMixedFinite`).  Take `K = ZMod p`,
let `κ m` be the permutation matrix of the translation `x ↦ m + x` of `M`, and let `ρ q` be the
permutation matrix of `x ↦ q • x`.  This uses no coprimary, exponent or characteristic
hypothesis.  It covers every finite-length piece of the gap, for instance `M = ℤ/p²` over
`Q = 1`, and every `M` over a finite `Q`.  The residual is `eHighMixed_InfiniteStatement`: the
mixed statement with the extra hypothesis `Infinite M`.

**LOUD: the residual is only EQUIVALENT to `EHighCoprimaryMixedStatement`, not strictly
weaker in logical strength.**  The two are interderivable.  Mixed ⇒ residual is plain
instantiation that forgets `Infinite M`.  Residual ⇒ mixed is `eHighMixed_mixed_of_infinite`.
The gain is entirely in proof content: every finite module is removed from the gap.  For a
finite `M` the coprimary prime `P` is maximal, because `R ⧸ Ann M` is finite.  So the whole
maximal-prime (finite-length) part of the problem is closed.  What remains are the infinite
modules, whose prime `P` has positive-dimensional quotient `R ⧸ P`.

**Truth check.**  The residual is the mixed statement with one more hypothesis, so it is a
special case of `EHighCoprimaryMixedStatement`.  That statement is a special case of
`EHighDevissageCoprimaryStatement`, which is true by Wehrfritz (1975), as recorded in
`PureCharPrimeEHighDevissageStatement`.  Hence the residual is true.

**LOUD: why the target was not proved by dévissage along `M ⊇ pM ⊇ … ⊇ p^(e-1) M`.**  The
natural route would glue the proved exponent-`p` layers
(`eHighCoprimary_exists_gl_of_nsmul_eq_zero`) along the finite `p`-power filtration.  That gluing step is not valid as a reduction.
Faithful conjugation representations of `pM` and `M ⧸ pM` do not assemble into one of `M`.
`ℤ/p²` and `(ℤ/p)²` have the same graded pieces, so the pieces do not determine the extension,
and the off-diagonal cocycle realising the extension class `Q`-equivariantly is the whole
problem (see the loud remark in `PureCharPrimeEHighDevissageStatement`).  For *finite* `M` the
gluing problem disappears, because the regular permutation representation needs no layers.  For
infinite `M` no gluing statement weaker than the gap itself is known to be true, so none is
recorded.  The infinite case needs the route of `PureCharPrimeEHighModule`: Noether
normalisation, localisation, Witt vectors and the Greenberg transform.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

/-- **Residual gap (infinite mixed coprimary case).**  This is `EHighCoprimaryMixedStatement`
with the extra hypothesis `Infinite M`.  **LOUD: it is interderivable with
`EHighCoprimaryMixedStatement` (only equivalent, not strictly weaker).**  The gain is proof
content: all finite modules are discharged by `eHighMixed_exists_gl_of_finite_charP`. -/
def eHighMixed_InfiniteStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ e : ℕ, 2 ≤ e → ∀ (Q : Type) [CommGroup Q], Group.FG Q →
    ∀ (M : Type) [AddCommGroup M] [Module (MonoidAlgebra (ZMod (p ^ e)) Q) M],
      Module.Finite (MonoidAlgebra (ZMod (p ^ e)) Q) M →
      ∀ (P : Ideal (MonoidAlgebra (ZMod (p ^ e)) Q)) (k : ℕ),
        Primary.IsCoprimaryWith (MonoidAlgebra (ZMod (p ^ e)) Q) M P k →
        ((p : ℕ) : MonoidAlgebra (ZMod (p ^ e)) Q) ∈ P →
        2 ≤ k → (∃ m : M, p • m ≠ 0) → Infinite M →
      ∃ (K : Type) (_ : Field K) (d : ℕ)
        (κ : Multiplicative M →* Matrix.GeneralLinearGroup (Fin d) K)
        (ρ : Q →* Matrix.GeneralLinearGroup (Fin d) K),
        ringChar K = p ∧ Function.Injective κ ∧
          ∀ (q : Q) (m : M),
            κ (Multiplicative.ofAdd (MonoidAlgebra.of (ZMod (p ^ e)) Q q • m)) =
              ρ q * κ (Multiplicative.ofAdd m) * (ρ q)⁻¹

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighMixed_InfiniteStatement

/-- **Endpoint (reduction).**  The mixed coprimary gap follows from its infinite case.  The
finite case is proved outright by the permutation representation. -/
theorem eHighMixed_mixed_of_infinite (h : eHighMixed_InfiniteStatement) :
    EHighCoprimaryMixedStatement := by
  intro p hp e he Q _ hfg M _ _ hfin P k hM hpP hk hne
  by_cases hMfin : Finite M
  · haveI : Finite M := hMfin
    exact eHighMixed_exists_gl_of_finite_charP hp (MonoidAlgebra.of (ZMod (p ^ e)) Q) M
  · exact h p hp e he Q hfg M hfin P k hM hpP hk hne (not_finite_iff_infinite.mp hMfin)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighMixed_mixed_of_infinite

/-- **Endpoint (composite).**  The coprimary high-exponent gap follows from the infinite mixed
case. -/
theorem eHighMixed_devissage_of_infinite (h : eHighMixed_InfiniteStatement) :
    EHighDevissageCoprimaryStatement :=
  eHighCoprimary_devissage_of_mixed (eHighMixed_mixed_of_infinite h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighMixed_devissage_of_infinite

/-- **Endpoint (composite).**  The high-exponent module statement follows from the infinite
mixed case. -/
theorem eHighMixed_pureCharPrimeEHighModule_of_infinite (h : eHighMixed_InfiniteStatement) :
    PureCharPrimeEHighModuleStatement :=
  eHighCoprimary_pureCharPrimeEHighModule_of_mixed (eHighMixed_mixed_of_infinite h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighMixed_pureCharPrimeEHighModule_of_infinite

end GroupApproximation.BooneHigman.Metabelian.Coprimary
