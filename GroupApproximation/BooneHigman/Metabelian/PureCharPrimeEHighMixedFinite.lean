import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Data.Finite.Defs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.SetTheory.Cardinal.NatCard
import GroupApproximation.Meta.AxiomGuard

/-!
# Finite modules: the permutation representation (bh-met-84)

Let `M` be a **finite** abelian group and let a group `Q` act on it by additive automorphisms
through a monoid hom `f : Q →* R` into a monoid acting distributively on `M`.  Over any field `K`
there is a faithful "conjugation representation":

* `κ m` is the permutation matrix of the translation `x ↦ m + x` of `M`;
* `ρ q` is the permutation matrix of the automorphism `x ↦ f q • x`;
* `ρ q * κ m * (ρ q)⁻¹ = κ (f q • m)`, since `f q • (m + f q⁻¹ • x) = f q • m + x`.

This uses no exponent, coprimary or characteristic hypothesis.  With `K = ZMod p` it gives
`ringChar K = p`.  It discharges every *finite* module in the mixed coprimary gap
(`PureCharPrimeEHighMixed`), for instance `M = ℤ/p²` over `Q = 1`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

section Perm

/-- Translations of `M` as a monoid hom `Multiplicative M →* Perm M`. -/
def eHighMixed_transPerm (M : Type*) [AddCommGroup M] : Multiplicative M →* Equiv.Perm M where
  toFun x :=
    { toFun := fun m => Multiplicative.toAdd x + m
      invFun := fun m => -Multiplicative.toAdd x + m
      left_inv := fun m => neg_add_cancel_left (Multiplicative.toAdd x) m
      right_inv := fun m => add_neg_cancel_left (Multiplicative.toAdd x) m }
  map_one' := Equiv.ext fun m => by
    show Multiplicative.toAdd (1 : Multiplicative M) + m = m
    rw [toAdd_one, zero_add]
  map_mul' x y := Equiv.ext fun m => by
    show Multiplicative.toAdd (x * y) + m =
      Multiplicative.toAdd x + (Multiplicative.toAdd y + m)
    rw [toAdd_mul, add_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighMixed_transPerm

theorem eHighMixed_transPerm_injective (M : Type*) [AddCommGroup M] :
    Function.Injective (eHighMixed_transPerm M) := by
  intro x y hxy
  have h0 : Multiplicative.toAdd x + 0 = Multiplicative.toAdd y + 0 :=
    congrArg (fun σ : Equiv.Perm M => σ 0) hxy
  rw [add_zero, add_zero] at h0
  exact Multiplicative.toAdd.injective h0

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighMixed_transPerm_injective

/-- The action `x ↦ f q • x` as a monoid hom `Q →* Perm M`. -/
def eHighMixed_actPerm (M : Type*) [AddCommGroup M] {Q R : Type*} [Group Q] [Monoid R]
    [DistribMulAction R M] (f : Q →* R) : Q →* Equiv.Perm M where
  toFun q :=
    { toFun := fun m => f q • m
      invFun := fun m => f q⁻¹ • m
      left_inv := fun m => by
        show f q⁻¹ • f q • m = m
        rw [smul_smul, ← map_mul f, inv_mul_cancel, map_one, one_smul]
      right_inv := fun m => by
        show f q • f q⁻¹ • m = m
        rw [smul_smul, ← map_mul f, mul_inv_cancel, map_one, one_smul] }
  map_one' := Equiv.ext fun m => by
    show f 1 • m = m
    rw [map_one, one_smul]
  map_mul' q r := Equiv.ext fun m => by
    show f (q * r) • m = f q • f r • m
    rw [map_mul, mul_smul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighMixed_actPerm

/-- Conjugating a translation by the action gives the translation by the acted element. -/
theorem eHighMixed_transPerm_conj (M : Type*) [AddCommGroup M] {Q R : Type*} [Group Q]
    [Monoid R] [DistribMulAction R M] (f : Q →* R) (q : Q) (m : M) :
    eHighMixed_transPerm M (Multiplicative.ofAdd (f q • m)) =
      eHighMixed_actPerm M f q * eHighMixed_transPerm M (Multiplicative.ofAdd m) *
        (eHighMixed_actPerm M f q)⁻¹ := by
  refine eq_mul_inv_of_mul_eq (Equiv.ext fun x => ?_)
  show f q • m + f q • x = f q • (m + x)
  exact (smul_add (f q) m x).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighMixed_transPerm_conj

end Perm

section Matrices

/-- Permutation matrices give an injective hom `Perm (Fin n) →* GL_n(K)`. -/
theorem eHighMixed_permMatrixUnits_injective (K : Type*) [Field K] (n : ℕ) :
    Function.Injective (Matrix.permMatrixHom (n := Fin n) (R := K)).toHomUnits := by
  refine (injective_iff_map_eq_one _).mpr fun σ hσ => ?_
  have h0 : (Matrix.permMatrixHom (n := Fin n) (R := K)) σ = 1 := by
    have h := congrArg Units.val hσ
    rwa [MonoidHom.coe_toHomUnits, Units.val_one] at h
  have h1 : (σ⁻¹).permMatrix K = (Equiv.refl (Fin n)).permMatrix K := by
    rw [Matrix.permMatrix_refl]
    exact h0
  have h2 : (σ⁻¹).toPEquiv = (Equiv.refl (Fin n)).toPEquiv :=
    PEquiv.toMatrix_injective (α := K) h1
  have h3 : σ⁻¹ = 1 := Equiv.ext fun x => by
    have h4 := congrArg (fun g : Fin n ≃. Fin n => g x) h2
    simp only [Equiv.toPEquiv_apply, Option.some.injEq] at h4
    exact h4
  exact inv_eq_one.mp h3

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighMixed_permMatrixUnits_injective

/-- The permutation representation of `Perm M` for a finite `M`, indexed by `Fin (Nat.card M)`. -/
noncomputable def eHighMixed_permRep (K : Type*) [Field K] (M : Type*) [Finite M] :
    Equiv.Perm M →* Matrix.GeneralLinearGroup (Fin (Nat.card M)) K :=
  (Matrix.permMatrixHom (n := Fin (Nat.card M)) (R := K)).toHomUnits.comp
    (Finite.equivFin M).permCongrHom.toMonoidHom

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighMixed_permRep

theorem eHighMixed_permRep_injective (K : Type*) [Field K] (M : Type*) [Finite M] :
    Function.Injective (eHighMixed_permRep K M) := by
  intro a b hab
  have h' : (Matrix.permMatrixHom (n := Fin (Nat.card M)) (R := K)).toHomUnits
        ((Finite.equivFin M).permCongrHom a) =
      (Matrix.permMatrixHom (n := Fin (Nat.card M)) (R := K)).toHomUnits
        ((Finite.equivFin M).permCongrHom b) := hab
  exact (Finite.equivFin M).permCongrHom.injective
    (eHighMixed_permMatrixUnits_injective K (Nat.card M) h')

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighMixed_permRep_injective

end Matrices

section Finite

/-- **Finite modules, over any field.**  A finite abelian group `M` with a `Q`-action through
`f : Q →* R` embeds into `GL_{|M|}(K)` by a faithful `κ`, and the action is conjugation by `ρ`. -/
theorem eHighMixed_exists_gl_of_finite (K : Type*) [Field K] {Q R : Type*} [Group Q] [Monoid R]
    (f : Q →* R) (M : Type*) [AddCommGroup M] [DistribMulAction R M] [Finite M] :
    ∃ (d : ℕ) (κ : Multiplicative M →* Matrix.GeneralLinearGroup (Fin d) K)
      (ρ : Q →* Matrix.GeneralLinearGroup (Fin d) K), Function.Injective κ ∧
        ∀ (q : Q) (m : M), κ (Multiplicative.ofAdd (f q • m)) =
          ρ q * κ (Multiplicative.ofAdd m) * (ρ q)⁻¹ := by
  refine ⟨Nat.card M, (eHighMixed_permRep K M).comp (eHighMixed_transPerm M),
    (eHighMixed_permRep K M).comp (eHighMixed_actPerm M f), fun a b hab => ?_, fun q m => ?_⟩
  · have h' : eHighMixed_permRep K M (eHighMixed_transPerm M a) =
        eHighMixed_permRep K M (eHighMixed_transPerm M b) := hab
    exact eHighMixed_transPerm_injective M (eHighMixed_permRep_injective K M h')
  · have h := congrArg (eHighMixed_permRep K M) (eHighMixed_transPerm_conj M f q m)
    rw [map_mul, map_mul, map_inv] at h
    exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighMixed_exists_gl_of_finite

/-- **Finite modules, in characteristic `p`.**  The same with `K = ZMod p`, so `ringChar K = p`.
This is the form of the conclusion of `EHighCoprimaryMixedStatement`. -/
theorem eHighMixed_exists_gl_of_finite_charP {p : ℕ} (hp : p.Prime) {Q R : Type*} [Group Q]
    [Monoid R] (f : Q →* R) (M : Type) [AddCommGroup M] [DistribMulAction R M] [Finite M] :
    ∃ (K : Type) (_ : Field K) (d : ℕ)
      (κ : Multiplicative M →* Matrix.GeneralLinearGroup (Fin d) K)
      (ρ : Q →* Matrix.GeneralLinearGroup (Fin d) K),
      ringChar K = p ∧ Function.Injective κ ∧
        ∀ (q : Q) (m : M), κ (Multiplicative.ofAdd (f q • m)) =
          ρ q * κ (Multiplicative.ofAdd m) * (ρ q)⁻¹ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, κ, ρ, hκ, hrel⟩ := eHighMixed_exists_gl_of_finite (ZMod p) f M
  exact ⟨ZMod p, inferInstance, d, κ, ρ, ZMod.ringChar_zmod_n p, hκ, hrel⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighMixed_exists_gl_of_finite_charP

end Finite

end GroupApproximation.BooneHigman.Metabelian.Coprimary
