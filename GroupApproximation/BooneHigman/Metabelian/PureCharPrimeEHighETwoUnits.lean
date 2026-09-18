import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import GroupApproximation.Meta.AxiomGuard

/-!
# Conjugation representations from unit groups of finite algebras (bh-met-87)

Let `K` be a field and `B` a finite-dimensional `K`-algebra.  Let `θ : Multiplicative M →* B`
be injective, and let `Q` act on `B` by `K`-algebra automorphisms `σ q` with
`θ (q • m) = σ q (θ m)`.  Then left multiplication `L_b : x ↦ b * x` and the maps `σ q`, written
in a basis of `B`, give an injective `κ : Multiplicative M →* GL_d(K)` (with `d = dim_K B`) and a
`ρ : Q →* GL_d(K)` with `κ (q • m) = ρ q * κ m * (ρ q)⁻¹`.

The key identity is `L_{σ b} ∘ σ = σ ∘ L_b`, that is, `σ b * σ x = σ (b * x)`.  This only uses
that `σ` is multiplicative.  `κ` is injective because `b ↦ L_b` is injective
(`Algebra.lmul_injective`: `L_b 1 = b`).

This is the *multiplicative* form of the linearization used for `e = 1`.  In exponent `p ^ 2`
it is the right form: a group of exponent `p ^ 2` never embeds additively into a vector space
over a field of characteristic `p`, but it can embed into the unit group of a
finite-dimensional algebra.  For example `ℤ/p²` embeds into `(F_p[ε]/(ε^(p+1)))ˣ` via
`1 ↦ 1 + ε`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

section Units

variable {K B : Type*} [Field K] [Ring B] [Algebra K B]

/-- The action `q ↦ σ q` on `B`, viewed as `K`-linear endomorphisms. -/
noncomputable def eHighETwo_autEnd {Q : Type*} [Monoid Q] (σ : Q →* (B ≃ₐ[K] B)) :
    Q →* Module.End K B where
  toFun q := (σ q).toLinearMap
  map_one' := LinearMap.ext fun x => by
    show σ 1 x = x
    rw [map_one, AlgEquiv.one_apply]
  map_mul' q r := LinearMap.ext fun x => by
    show σ (q * r) x = σ q (σ r x)
    rw [map_mul, AlgEquiv.mul_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighETwo_autEnd

/-- An algebra automorphism intertwines left multiplications: `L_{σ b} ∘ σ = σ ∘ L_b`. -/
theorem eHighETwo_lmul_comp (σ : B ≃ₐ[K] B) (b : B) :
    Algebra.lmul K B (σ b) * σ.toLinearMap = σ.toLinearMap * Algebra.lmul K B b := by
  refine LinearMap.ext fun x => ?_
  show σ b * σ x = σ (b * x)
  exact (map_mul σ b x).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighETwo_lmul_comp

/-- **Linearization from units.**  An injective `θ : Multiplicative M →* B` into a
finite-dimensional `K`-algebra, equivariant for an action of `Q` on `B` by algebra
automorphisms, gives an injective `κ : Multiplicative M →* GL_d(K)` and `ρ : Q →* GL_d(K)` such
that conjugation by `ρ q` realises `act q`. -/
theorem eHighETwo_exists_gl_of_units {M Q : Type*} [AddCommGroup M] [Group Q]
    [Module.Finite K B] (act : Q → M → M) (θ : Multiplicative M →* B)
    (hθ : Function.Injective θ) (σ : Q →* (B ≃ₐ[K] B))
    (hequiv : ∀ (q : Q) (m : M),
      θ (Multiplicative.ofAdd (act q m)) = σ q (θ (Multiplicative.ofAdd m))) :
    ∃ (d : ℕ) (κ : Multiplicative M →* Matrix.GeneralLinearGroup (Fin d) K)
      (ρ : Q →* Matrix.GeneralLinearGroup (Fin d) K), Function.Injective κ ∧
        ∀ (q : Q) (m : M), κ (Multiplicative.ofAdd (act q m)) =
          ρ q * κ (Multiplicative.ofAdd m) * (ρ q)⁻¹ := by
  let e := LinearMap.toMatrixAlgEquiv (Module.finBasis K B)
  refine ⟨Module.finrank K B,
    ((e.toRingEquiv.toMonoidHom.comp (Algebra.lmul K B).toRingHom.toMonoidHom).comp
      θ).toHomUnits,
    (e.toRingEquiv.toMonoidHom.comp (eHighETwo_autEnd σ)).toHomUnits, ?_, fun q m => ?_⟩
  · refine (injective_iff_map_eq_one _).mpr fun x hx => ?_
    have h1 : e (Algebra.lmul K B (θ x)) = e 1 := by
      rw [map_one]
      exact congrArg Units.val hx
    have h2 : Algebra.lmul K B (θ x) = Algebra.lmul K B 1 :=
      (e.injective h1).trans (map_one (Algebra.lmul K B)).symm
    exact hθ ((Algebra.lmul_injective h2).trans (map_one θ).symm)
  · refine eq_mul_inv_of_mul_eq (Units.ext ?_)
    show e (Algebra.lmul K B (θ (Multiplicative.ofAdd (act q m)))) * e (σ q).toLinearMap =
      e (σ q).toLinearMap * e (Algebra.lmul K B (θ (Multiplicative.ofAdd m)))
    rw [← map_mul, ← map_mul, hequiv]
    exact congrArg e (eHighETwo_lmul_comp (σ q) (θ (Multiplicative.ofAdd m)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighETwo_exists_gl_of_units

end Units

end GroupApproximation.BooneHigman.Metabelian.Coprimary
