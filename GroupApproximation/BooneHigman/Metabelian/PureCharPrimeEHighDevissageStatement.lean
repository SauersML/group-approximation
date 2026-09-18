import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import GroupApproximation.BooneHigman.Primary.Coprimary
import GroupApproximation.Meta.AxiomGuard

/-!
# High exponent: the coprimary residual statement (lanes bh-met-67, bh-met-67c)

Gap of the lane: `PureCharPrimeEHighModuleStatement` (`PureCharPrimeEHighModule.lean:61`).  We
split along a coprimary decomposition of the module (dévissage by primes).  This is the first
step of the intended route recorded in `PureCharPrimeEHighModule` (primary decomposition,
Noether normalisation, localisation, Witt vectors, Greenberg transform).  The reduction
`pureCharPrimeEHighModule_of_eHighDevissageCoprimary` lives in `PureCharPrimeEHighDevissage`.

**The residual statement** `EHighDevissageCoprimaryStatement`.  Let `Q` be f.g. abelian,
`e ≥ 2`, `R = (ℤ/p^e)[Q]`, and let `M` be a finite `R`-module that is coprimary with some prime
`P` and exponent `k`.  So `M ≠ 0`, `P ^ k • M = 0`, and every `r ∉ P` acts injectively.  Assume
moreover `p ∈ P` (the prime lies over `p`).  Then some field `K` with `ringChar K = p` has an
injective `κ : Multiplicative M →* GL_d(K)` and a `ρ : Q →* GL_d(K)` with
`κ (q • m) = ρ q * κ m * (ρ q)⁻¹`.

*Truth.*  This is a special case of the target without the witness hypothesis
`∃ m, p ^ (e - 1) • m ≠ 0`, and that version follows from `PureCharPrimeEHighModuleStatement`.
Apply the target to `M × R`.  It is finite, and `p ^ (e - 1) • (0, 1) ≠ 0` because
`p ^ (e - 1) ≠ 0` in `ZMod (p ^ e)`.  Then restrict `κ` along `m ↦ (m, 0)`.  The target itself
is true (Wehrfritz 1975, Thm 1.1; see `PureCharPrimeEHighModule`).  So the residual statement
is true.

*Strength (loud).*  It is a special case: the modules are restricted to coprimary ones over
primes containing `p`, so it is logically no stronger than the gap; by the *Truth* paragraph
the two are (unconditionally) interderivable, so the gain is in proof content only.  The
reduction discharges:
* the Lasker–Noether decomposition `0 = ⋂ S_j` (`Primary.exists_coprimary_decomposition`, which
  needs `R` Noetherian: `ZMod (p ^ e)` is finite, then Hilbert's basis theorem);
* `p ∈ P_j` for every associated prime (`p ^ e = 0` in `R` and `P_j` is prime);
* a common field of characteristic `p` for the pieces (`exists_common_field_charP_finset`);
* the block-diagonal assembly of the *multiplicative* conjugation representations
  (`eHighDevissage_exists_gl_of_field_pieces`, `PureCharPrimeEHighDevissageBlock`).
The residual keeps the structure that the rest of the route needs.  Elements outside `P` act
injectively.  So a lifted Noether normalisation `t` of `R ⧸ P` makes every element of
`(ℤ/p^e)[t] \ p(ℤ/p^e)[t]` act injectively.  Hence `M ↪ S⁻¹ M`, a finite module over
`ℤ[t]_(p) ⧸ p^e`.

**Loud remark: why the dévissage along `M ⊇ pM ⊇ … ⊇ p^(e-1) M` (or along a composition
series) was not used.**  Faithful conjugation representations of `pM` and `M ⧸ pM` (the
exponent-`p` case) do *not* assemble into one of `M`.  The graded pieces do not determine the
extension: `ℤ/p²` and `(ℤ/p)²` have the same pieces.  In a block upper-triangular representation
whose diagonal blocks come from the pieces, the off-diagonal part is a cocycle
`M → Hom(V₁, V₂)`.  It has to realise the extension class `Q`-equivariantly, and building it is
the whole problem.  In general extensions of linear groups are not linear.  Sizes in the model
case `Q = 1`: the unipotent `J = 1 + N_n` (one Jordan block) has order `p ^ ⌈log_p n⌉`.  So
`ℤ/p²` embeds in `U_n(F_p)` iff `n ≥ p + 1`.  It does not embed in `U_2(F_p)`, and it embeds in
`U_3(F_p)` only for `p = 2`.  No reduction to the `e = 1` statement of this kind is recorded
here.  The same objection applies to any filtration with more than one step: only
*intersections* of submodules with faithful quotients (subdirect products), not extensions,
assemble block-diagonally, which is why the dévissage is by primes (coprimary decomposition).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

/-- **Residual gap (exponent `p ^ e`, `e ≥ 2`, coprimary module form).**  A finite coprimary
`(ℤ/p^e)[Q]`-module `M`, for `Q` f.g. abelian, whose prime `P` contains `p`, embeds
multiplicatively into `GL_d(K)` with `ringChar K = p`, and the `Q`-action is conjugation by a
representation `ρ`. -/
def EHighDevissageCoprimaryStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ e : ℕ, 2 ≤ e → ∀ (Q : Type) [CommGroup Q], Group.FG Q →
    ∀ (M : Type) [AddCommGroup M] [Module (MonoidAlgebra (ZMod (p ^ e)) Q) M],
      Module.Finite (MonoidAlgebra (ZMod (p ^ e)) Q) M →
      ∀ (P : Ideal (MonoidAlgebra (ZMod (p ^ e)) Q)) (k : ℕ),
        Primary.IsCoprimaryWith (MonoidAlgebra (ZMod (p ^ e)) Q) M P k →
        ((p : ℕ) : MonoidAlgebra (ZMod (p ^ e)) Q) ∈ P →
      ∃ (K : Type) (_ : Field K) (d : ℕ)
        (κ : Multiplicative M →* Matrix.GeneralLinearGroup (Fin d) K)
        (ρ : Q →* Matrix.GeneralLinearGroup (Fin d) K),
        ringChar K = p ∧ Function.Injective κ ∧
          ∀ (q : Q) (m : M),
            κ (Multiplicative.ofAdd (MonoidAlgebra.of (ZMod (p ^ e)) Q q • m)) =
              ρ q * κ (Multiplicative.ofAdd m) * (ρ q)⁻¹

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.EHighDevissageCoprimaryStatement

end GroupApproximation.BooneHigman.Metabelian.Coprimary
