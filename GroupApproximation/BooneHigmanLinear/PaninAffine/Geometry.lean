import GroupApproximation.Meta.AxiomGuard
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The affine presentation statement (lane k2-panin, piece GEO)

The statement `AffineMonicFibreStatement` and its fibre map, split off from
`PaninAffine.Statements`. This module imports only Mathlib, so the proof (`PaninAffine.Main`) and
its consumer (`PaninAffine.Cor29`) do not pull in the `K₂` library. The context and the reduction
from `F_p` to an infinite field are in `PaninAffine.Statements`. Not root-wired.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace PaninAffine

section Geometry

/-- **The fibre map** of the coordinates `φ`: `K[s₁..s_n] → R/M`, `sⱼ ↦ φ⁻¹(sⱼ₊₁) mod M`.
Its kernel is `𝔭 = φ(M) ∩ K[s₁..s_n]`, the point under `M` of the base of the projection that
forgets `s₀`. Mapping coefficients along it restricts a polynomial in `s₀` to the fibre over `𝔭`,
viewed over the extension field `R/M` of the residue field `k(𝔭)`. -/
noncomputable def fibreMap {K : Type} [Field K] {n : ℕ} (M : Ideal (MvPolynomial (Fin (n + 1)) K))
    (φ : MvPolynomial (Fin (n + 1)) K ≃ₐ[K] MvPolynomial (Fin (n + 1)) K) :
    MvPolynomial (Fin n) K →+* MvPolynomial (Fin (n + 1)) K ⧸ M :=
  (Ideal.Quotient.mk M).comp
    ((φ.symm : MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin (n + 1)) K).toRingHom.comp
      (MvPolynomial.rename (Fin.succ : Fin n → Fin (n + 1))).toRingHom)

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.fibreMap

/-- **Affine presentation over a field `K`** (board piece GEO, specialized to polynomial rings).
Let `M` be a maximal ideal of `K[s₀..s_n]`, let `f ∈ M` be nonzero, and let `f' ∉ M` be coprime
to `f`. Then some `K`-automorphism `φ` satisfies:
- `φ f` is a nonzero constant times a polynomial monic in `s₀` over `K[s₁..s_n]`;
- `φ f` and `φ f'` are coprime on the fibre through `M`, i.e. coprime in `(R/M)[s₀]` after
  mapping coefficients along `fibreMap M φ`.
By `Polynomial.isCoprime_map` the fibre condition descends to the residue field `k(𝔭)`. Since
`φ f` is monic up to a unit, Nakayama then makes `(φ f, φ f')` the unit ideal of
`K[s₁..s_n]_𝔭[s₀]`. That is the Zariski-excision input of LSV Cor 2.9 (see
`research/artifacts/gq-k2-panin-affine-presentation.md`). For an infinite `K`, a linear `φ` (a
shear) works: `PaninAffine.Main.infiniteFieldAffineMonicFibre`. -/
def AffineMonicFibreStatement (K : Type) [Field K] : Prop :=
  ∀ (n : ℕ) (f f' : MvPolynomial (Fin (n + 1)) K) (M : Ideal (MvPolynomial (Fin (n + 1)) K)),
    M.IsMaximal → f ∈ M → f' ∉ M → f ≠ 0 → IsRelPrime f f' →
      ∃ φ : MvPolynomial (Fin (n + 1)) K ≃ₐ[K] MvPolynomial (Fin (n + 1)) K,
        (∃ c : K, c ≠ 0 ∧ (MvPolynomial.finSuccEquiv K n (MvPolynomial.C c * φ f)).Monic) ∧
          IsCoprime ((MvPolynomial.finSuccEquiv K n (φ f)).map (fibreMap M φ))
            ((MvPolynomial.finSuccEquiv K n (φ f')).map (fibreMap M φ))

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.AffineMonicFibreStatement

/-- The affine presentation for every infinite field. It is the only geometric input the
polynomial-ring case of the LSV route needs, once `unstableNKAt_of_ratFunc` has moved the finite
base field `F_p` to `F_p(T)`. Proved in `PaninAffine.Main`. -/
def InfiniteFieldAffineMonicFibreStatement : Prop :=
  ∀ (K : Type) [Field K] [Infinite K], AffineMonicFibreStatement K

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.InfiniteFieldAffineMonicFibreStatement

end Geometry

end PaninAffine
end BooneHigmanLinear
end GroupApproximation
