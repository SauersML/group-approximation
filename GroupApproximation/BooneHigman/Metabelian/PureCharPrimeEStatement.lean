import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import GroupApproximation.Meta.AxiomGuard

/-!
# Pure characteristic `p` linearity of split extensions: the two residual statements (bh-met-26)

Lane bh-met-18 isolated `PureCharPrimeSplitStatement` (`PureCharPrimeSplit`).  We split it along
the exponent.  This file only *states* the two residual gaps; the reduction
`pureCharPrimeSplit_of_eOne_high` lives in `PureCharPrimeESplit`.

**Truth check.**  Both statements are true (Wehrfritz, *Infinite linear groups*, 1973, and
Wehrfritz 1975, *Faithful representations of finitely generated metabelian groups*, Thm 1.1):

* `PureCharPrimeEOneEmbeddingStatement` (exponent `p`, stated module-theoretically).  Let
  `R = F_p[Q]` with `Q` f.g. abelian, so `R` is Noetherian (Hall), and `M` a f.g. `R`-module.
  A primary decomposition gives `M ↪ ⊕ M ⧸ S_i` with `M_i = M ⧸ S_i` coprimary for a prime `𝔭_i`
  (`Primary.exists_coprimary_decomposition`).  **Caution:** a coprimary module is *not* in
  general an `R ⧸ 𝔭`-module (e.g. `R ⧸ 𝔭²`), so the naive "submodule of a free
  `R⧸𝔭`-module" sketch is inaccurate.  The correct route: `A_i = R ⧸ Ann M_i` has nilradical
  `𝔭_i ⧸ Ann`; lift a Noether-normalization basis `t_1, …, t_r` of `R ⧸ 𝔭_i`; `A_i` is finite
  over `F_p[t]` (generators are integral modulo nilpotents, hence integral), and every nonzero
  `f ∈ F_p[t]` lies outside `𝔭_i`, hence acts injectively on `M_i`.  So
  `M_i ↪ F_p(t)⊗M_i`, a finite-dimensional `F_p(t)`-space on which `Q` acts `F_p(t)`-linearly.
  All `F_p(t_1..t_r)` embed in one purely transcendental field, and scalar extension to a field is
  injective, which gives `ι` and `ρ` below.
* `PureCharPrimeEHighStatement` (exact exponent `p ^ e`, `e ≥ 2`, full group f.g.): Wehrfritz's
  theorem again.  Here there is **no** additive embedding into an exponent-`p` group, and the
  filtration `B ⊇ B^p ⊇ …` does not by itself give linearity, because extensions of linear groups
  need not be linear.  The carry (Witt vector) structure is genuine.

**Why these are strictly smaller than the target.**  `PureCharPrimeSplitStatement` implies
`PureCharPrimeEHighStatement` (take `H = ⊤`), but not conversely, since the latter excludes the
exponent-`p` case by the minimality hypothesis `∃ b, b ^ p ^ (e - 1) ≠ 1`.  The module statement
carries no group theory: base restriction, the passage `B ↦ F_p[Q]`-module, finite generation,
faithfulness on `Q` and the affine `GL_{d+1}` trick are all proved in
`PureCharPrimeEBase`, `PureCharPrimeEOne` and `PureCharPrimeEAffine`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

/-- **Residual gap (exponent `p`).**  For a f.g. abelian group `Q` and a finitely generated
`F_p[Q]`-module `M`, there is an additive embedding `ι : M ↪ K^d` into a vector space over a
field of characteristic `p`, intertwining the `Q`-action with a linear representation `ρ`. -/
def PureCharPrimeEOneEmbeddingStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ (Q : Type) [Group Q], (∀ a b : Q, a * b = b * a) → Group.FG Q →
    ∀ (M : Type) [AddCommGroup M] [Module (MonoidAlgebra (ZMod p) Q) M],
      Module.Finite (MonoidAlgebra (ZMod p) Q) M →
      ∃ (K : Type) (_ : Field K) (d : ℕ) (ι : M →+ (Fin d → K))
        (ρ : Q →* Matrix.GeneralLinearGroup (Fin d) K),
        ringChar K = p ∧ Function.Injective ι ∧
          ∀ (q : Q) (m : M), ι (MonoidAlgebra.of (ZMod p) Q q • m) =
            (ρ q : Matrix (Fin d) (Fin d) K) *ᵥ ι m

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.PureCharPrimeEOneEmbeddingStatement

/-- **Residual gap (exact exponent `p ^ e`, `e ≥ 2`).**  A finitely generated split extension
`B ⋊ Q` of an abelian group `B` of exact exponent `p ^ e` (`e ≥ 2`) by an abelian group `Q` embeds
in `GL_d(K)` with `ringChar K = p`. -/
def PureCharPrimeEHighStatement : Prop :=
  ∀ (B Q : Type) [Group B] [Group Q] (φ : Q →* MulAut B), (∀ a b : B, a * b = b * a) →
    (∀ a b : Q, a * b = b * a) → ∀ p : ℕ, p.Prime → ∀ e : ℕ, 2 ≤ e →
    (∀ b : B, b ^ (p ^ e) = 1) → (∃ b : B, b ^ (p ^ (e - 1)) ≠ 1) → Group.FG (B ⋊[φ] Q) →
      ∃ (K : Type) (_ : Field K) (d : ℕ) (f : (B ⋊[φ] Q) →* Matrix.GeneralLinearGroup (Fin d) K),
        ringChar K = p ∧ Function.Injective f

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.PureCharPrimeEHighStatement

end GroupApproximation.BooneHigman.Metabelian.Coprimary
