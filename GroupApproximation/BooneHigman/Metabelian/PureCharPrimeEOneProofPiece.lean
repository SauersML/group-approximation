import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.End
import Mathlib.Algebra.Module.Hom
import Mathlib.Algebra.Module.RingHom
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import GroupApproximation.BooneHigman.Primary.Coprimary
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEOneProofCover
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEOneProofLocalize
import GroupApproximation.Meta.AxiomGuard

/-!
# Linearizing a coprimary piece in characteristic `p` (lane bh-met-52)

Let `R = 𝔽_p[Q]` with `Q` finitely generated commutative, and let `N` be a finitely generated
`R`-module that is coprimary with prime `P` and exponent `e`.  The ring map
`r ↦ (x ↦ r ^ (p ^ e) • x)` is additive (Frobenius) and kills `P` (since `e ≤ p ^ e`), so it
makes `N` a module over the domain `D = R ⧸ P`.  Over `D`, `N` is finitely generated
(`twist_finite`: the twist is compensated because `c ^ (p ^ e) = c` on `𝔽_p` and `Q ⧸ Q^(p^e)` is
finite) and torsion-free (elements outside `P` act injectively, and `P` is prime), and `Q` acts
`D`-linearly because `R` is commutative.  Hence `N` linearizes over `Frac D`, a field of
characteristic `p` (`exists_matrix_of_domain_torsionFree`).

* `exists_charP_linearization_of_coprimary`: the linearization of one coprimary piece.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Coprimary

/-- **One coprimary piece in characteristic `p`.**  A finitely generated coprimary
`𝔽_p[Q]`-module embeds `Q`-equivariantly into `K^d`, with `Q` acting through `GL_d(K)` for a
field `K` of characteristic `p`. -/
theorem exists_charP_linearization_of_coprimary {p : ℕ} [hp : Fact p.Prime] {Q : Type}
    [CommGroup Q] [Group.FG Q] {N : Type} [AddCommGroup N]
    [Module (MonoidAlgebra (ZMod p) Q) N] [Module.Finite (MonoidAlgebra (ZMod p) Q) N]
    {P : Ideal (MonoidAlgebra (ZMod p) Q)} {e : ℕ}
    (hcop : Primary.IsCoprimaryWith (MonoidAlgebra (ZMod p) Q) N P e) :
    ∃ (K : Type) (_ : Field K) (d : ℕ) (ρ : Q →* Matrix.GeneralLinearGroup (Fin d) K)
      (ι : N →+ (Fin d → K)), CharP K p ∧ Function.Injective ι ∧
        ∀ q x, ι (MonoidAlgebra.of (ZMod p) Q q • x) =
          Matrix.mulVec (ρ q : Matrix (Fin d) (Fin d) K) (ι x) := by
  haveI : CharP (MonoidAlgebra (ZMod p) Q) p :=
    charP_of_injective_ringHom (algebraMap (ZMod p) (MonoidAlgebra (ZMod p) Q)).injective p
  haveI : P.IsPrime := hcop.isPrime
  let act : MonoidAlgebra (ZMod p) Q →+* AddMonoid.End N :=
    (Module.toAddMonoidEnd (MonoidAlgebra (ZMod p) Q) N).comp
      (iterateFrobenius (MonoidAlgebra (ZMod p) Q) p e)
  have hact : ∀ a : MonoidAlgebra (ZMod p) Q, a ∈ P → act a = 0 := by
    intro a ha
    have hmem : a ^ p ^ e ∈ P ^ e :=
      Ideal.pow_le_pow_right (Nat.lt_pow_self (n := e) hp.out.one_lt).le
        (Ideal.pow_mem_pow ha (p ^ e))
    exact AddMonoidHom.ext fun x => hcop.smul_eq_zero_of_mem_pow _ hmem x
  letI : Module (MonoidAlgebra (ZMod p) Q ⧸ P) N :=
    Module.compHom N (Ideal.Quotient.lift P act hact)
  have hsmul : ∀ (r : MonoidAlgebra (ZMod p) Q) (y : N),
      Ideal.Quotient.mk P r • y = r ^ p ^ e • y := fun _ _ => rfl
  haveI : Module.Finite (MonoidAlgebra (ZMod p) Q ⧸ P) N :=
    twist_finite (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective (pow_pos hp.out.pos e)
      (fun c => ZMod.pow_card_pow c) hsmul
  have htf : ∀ c : MonoidAlgebra (ZMod p) Q ⧸ P, c ≠ 0 →
      Function.Injective fun x : N => c • x := by
    intro c hc x₁ x₂ hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    have hr : r ^ p ^ e ∉ P := fun hmem =>
      hc (Ideal.Quotient.eq_zero_iff_mem.mpr (hcop.isPrime.mem_of_pow_mem _ hmem))
    exact hcop.smul_injective_of_notMem _ hr hx
  let T : Q →* Module.End (MonoidAlgebra (ZMod p) Q ⧸ P) N :=
    { toFun := fun q =>
        { toFun := fun x => MonoidAlgebra.of (ZMod p) Q q • x
          map_add' := fun x y => smul_add _ x y
          map_smul' := fun c x => by
            obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
            show MonoidAlgebra.of (ZMod p) Q q • r ^ p ^ e • x =
              r ^ p ^ e • MonoidAlgebra.of (ZMod p) Q q • x
            rw [smul_smul, smul_smul, mul_comm (MonoidAlgebra.of (ZMod p) Q q)] }
      map_one' := LinearMap.ext fun x => by
        show MonoidAlgebra.of (ZMod p) Q 1 • x = x
        rw [map_one, one_smul]
      map_mul' := fun a b => LinearMap.ext fun x => by
        show MonoidAlgebra.of (ZMod p) Q (a * b) • x =
          MonoidAlgebra.of (ZMod p) Q a • MonoidAlgebra.of (ZMod p) Q b • x
        rw [map_mul, mul_smul] }
  obtain ⟨d, ρ, ι, hinj, hequiv⟩ := exists_matrix_of_domain_torsionFree htf
    (fun q (x : N) => MonoidAlgebra.of (ZMod p) Q q • x) T fun _ _ => rfl
  haveI : CharP (MonoidAlgebra (ZMod p) Q ⧸ P) p :=
    charP_of_injective_ringHom
      ((Ideal.Quotient.mk P).comp (algebraMap (ZMod p) (MonoidAlgebra (ZMod p) Q))).injective p
  exact ⟨FractionRing (MonoidAlgebra (ZMod p) Q ⧸ P), inferInstance, d, ρ, ι, inferInstance,
    hinj, hequiv⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.exists_charP_linearization_of_coprimary

end Coprimary
end Metabelian
end BooneHigman
end GroupApproximation
