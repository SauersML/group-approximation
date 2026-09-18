import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import GroupApproximation.Meta.AxiomGuard

/-!
# High exponent: the module-theoretic residual statement (bh-met-56)

Target of the lane: `PureCharPrimeEHighStatement` (`PureCharPrimeEStatement.lean:63`).  Let `B` be
abelian of exact exponent `p ^ e` with `e ≥ 2`, let `Q` be abelian, and let `B ⋊ Q` be finitely
generated.  Then `B ⋊ Q` embeds in `GL_d(K)` with `ringChar K = p`.

**Truth check.** The target is true.  `B ⋊ Q` is a f.g. metabelian group whose derived subgroup
lies in `B`, so it is a `p`-group.  By Wehrfritz 1975, Thm 1.1, such a group has a faithful
representation of finite degree over a field of characteristic `p`.

**Why the exponent-`p` affine trick cannot be reused.** In characteristic `p` an element of order
`p ^ e` is unipotent with a Jordan block of size `> p ^ (e - 1)`.  So `B` cannot embed additively
in `K^d` (exponent `p`).  It has to embed *multiplicatively* as a commutative unipotent subgroup
of `GL_d(K)`, normalised by the image of `Q`.  The statement below records exactly that, for
modules, as the analogue of `PureCharPrimeEOneStatement`.

**The residual statement** `PureCharPrimeEHighModuleStatement`.  Let `Q` be f.g. abelian and `M` a
f.g. `(ℤ/p^e)[Q]`-module (`e ≥ 2`) with `p ^ (e - 1) • M ≠ 0`.  Then some field `K` with
`ringChar K = p` admits an injective hom `κ : Multiplicative M →* GL_d(K)` and a hom
`ρ : Q →* GL_d(K)` with `κ (q • m) = ρ q * κ m * (ρ q)⁻¹`.

*Truth.*  `M ⋊ Q` is f.g. (module generators plus generators of `Q`), metabelian, and its derived
subgroup lies in `M`, a `p`-group.  Wehrfritz 1975, Thm 1.1, gives a faithful
`f : M ⋊ Q →* GL_d(K)`.  Take `κ = f ∘ inl` and `ρ = f ∘ inr`; the relation
`inl (q • m) = inr q * inl m * (inr q)⁻¹` gives the intertwining.

*Why strictly smaller.* The statement has no group theory in it.  The reduction
`pureCharPrimeEHigh_of_module` (`PureCharPrimeEHigh`) proves the rest:
* the `(ℤ/p^e)[Q]`-module structure on `B` (we reuse `EOneMod φ (p ^ e) hexp`);
* finite generation (`eOne_finite`);
* the regular summand `(ℤ/p^e)[Q]`, which forces `ρ q ∉ κ(B)` for `q ≠ 1`;
* the faithful representation `x ↦ κ x.left * ρ x.right` (`PureCharPrimeEHighConj`).
Faithfulness of `ρ` is not asked for.

*Intended proof (not formalised).* Take a primary decomposition of `M` over the Noetherian ring
`R = (ℤ/p^e)[Q]`.  For a coprimary piece `M_i` with prime `𝔭_i ∋ p`, lift a Noether normalisation
`t` of `R / 𝔭_i`.  The elements of `(ℤ/p^e)[t]` that are nonzero mod `p` act injectively.
Localising embeds `M_i` in a finite module over `O / p^e`, where `O = ℤ[t]_(p)`, and
`O / p^e ↪ W_e(F_p(t)^perf)`.  This yields `M ⋊ Q ≤ GL_n(W_e(L))`.  The Greenberg transform of
`GL_n` over `W_e` is an affine algebraic group over `F_p`, hence linear, and this gives
`GL_n(W_e(L)) ↪ GL_N(L)`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

/-- **Residual gap (exponent `p ^ e`, `e ≥ 2`, module form).**  A f.g. `(ℤ/p^e)[Q]`-module `M`
with `p ^ (e - 1) • M ≠ 0`, for `Q` f.g. abelian, embeds multiplicatively into `GL_d(K)`,
`ringChar K = p`, and the `Q`-action is conjugation by a representation `ρ`. -/
def PureCharPrimeEHighModuleStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ e : ℕ, 2 ≤ e → ∀ (Q : Type) [Group Q], (∀ a b : Q, a * b = b * a) →
    Group.FG Q →
    ∀ (M : Type) [AddCommGroup M] [Module (MonoidAlgebra (ZMod (p ^ e)) Q) M],
      Module.Finite (MonoidAlgebra (ZMod (p ^ e)) Q) M → (∃ m : M, p ^ (e - 1) • m ≠ 0) →
      ∃ (K : Type) (_ : Field K) (d : ℕ)
        (κ : Multiplicative M →* Matrix.GeneralLinearGroup (Fin d) K)
        (ρ : Q →* Matrix.GeneralLinearGroup (Fin d) K),
        ringChar K = p ∧ Function.Injective κ ∧
          ∀ (q : Q) (m : M),
            κ (Multiplicative.ofAdd (MonoidAlgebra.of (ZMod (p ^ e)) Q q • m)) =
              ρ q * κ (Multiplicative.ofAdd m) * (ρ q)⁻¹

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.PureCharPrimeEHighModuleStatement

end GroupApproximation.BooneHigman.Metabelian.Coprimary
