import Mathlib.RingTheory.Lasker
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.CharP.Defs
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Coprimary decompositions of finitely generated modules

A module `M` over a commutative ring `R` is *coprimary* with prime `P` and exponent `e` when it is
nonzero, `P ^ e` annihilates it, and every element outside `P` acts injectively
(`IsCoprimaryWith`).  This is the shape the linear representations of the metabelian pieces consume:
the ideal `P` is the unique associated prime, elements of `P` act nilpotently, and the characteristic
of `R ⧸ P` separates the torsion-free pieces from the pieces of prime-power exponent.

* `isCoprimaryWith_quotient_of_isPrimary`: the quotient by a primary submodule `S` is coprimary with
  the prime `√(S : M)`.  The exponent comes from finite generation of the radical.
* `exists_coprimary_decomposition`: a finitely generated module over a Noetherian ring has finitely
  many submodules `S i`, jointly detecting `0`, whose quotients are coprimary with pairwise distinct
  primes.  The decomposition itself is Mathlib's Lasker–Noether theorem (`Submodule.isLasker`).
* `IsCoprimaryWith.torsionFree_or_primeExponent`: a coprimary module is torsion-free as an abelian
  group, or is annihilated by `p ^ e` for a prime `p` lying in `P`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Primary

open Submodule

section Coprimary

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

/-- `M` is **coprimary** with prime `P` and exponent `e`: `M` is nonzero, `P` is prime, `P ^ e`
annihilates `M`, and every element outside `P` acts injectively on `M`. -/
structure IsCoprimaryWith (P : Ideal R) (e : ℕ) : Prop where
  nontrivial : Nontrivial M
  isPrime : P.IsPrime
  smul_eq_zero_of_mem_pow : ∀ r ∈ P ^ e, ∀ x : M, r • x = 0
  smul_injective_of_notMem : ∀ r : R, r ∉ P → Function.Injective fun x : M => r • x

end Coprimary

section Quotient

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The quotient by a primary submodule `S` is coprimary with the prime `√(S : M)`. -/
theorem isCoprimaryWith_quotient_of_isPrimary [IsNoetherianRing R] {S : Submodule R M}
    (hS : S.IsPrimary) :
    ∃ e : ℕ, IsCoprimaryWith R (M ⧸ S) (S.colon Set.univ).radical e := by
  obtain ⟨e, he⟩ :=
    Ideal.exists_radical_pow_le_of_fg (S.colon Set.univ) (IsNoetherian.noetherian _)
  refine ⟨e, ⟨Submodule.Quotient.nontrivial_iff.mpr hS.ne_top, hS.isPrime_radical_colon, ?_, ?_⟩⟩
  · intro r hr x
    induction x using Submodule.Quotient.induction_on with
    | H m =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_colon.mp (he hr) m (Set.mem_univ m)
  · intro r hr x y hxy
    induction x using Submodule.Quotient.induction_on with
    | H a =>
      induction y using Submodule.Quotient.induction_on with
      | H b =>
        change r • (Submodule.Quotient.mk a : M ⧸ S) = r • Submodule.Quotient.mk b at hxy
        rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
          Submodule.Quotient.eq, ← smul_sub] at hxy
        rw [Submodule.Quotient.eq]
        exact (hS.mem_or_mem hxy).resolve_right hr

variable (R M) in
/-- **Coprimary decomposition.** A finitely generated module over a Noetherian ring has finitely
many submodules `S i` that jointly detect `0`, whose quotients are coprimary with pairwise distinct
primes `P i`. -/
theorem exists_coprimary_decomposition [IsNoetherianRing R] [Module.Finite R M] :
    ∃ (n : ℕ) (S : Fin n → Submodule R M) (P : Fin n → Ideal R) (e : Fin n → ℕ),
      (∀ m : M, (∀ i, m ∈ S i) → m = 0) ∧ Function.Injective P ∧
        ∀ i, IsCoprimaryWith R (M ⧸ S i) (P i) (e i) := by
  classical
  obtain ⟨t, ht⟩ :=
    Submodule.IsLasker.exists_isMinimalPrimaryDecomposition (Submodule.isLasker R M) ⊥
  let E := t.equivFin
  let S : Fin t.card → Submodule R M := fun i => (E.symm i : Submodule R M)
  have hprim : ∀ i, (S i).IsPrimary := fun i => ht.primary (E.symm i).2
  choose e he using fun i => isCoprimaryWith_quotient_of_isPrimary (hprim i)
  refine ⟨t.card, S, fun i => ((S i).colon Set.univ).radical, e, ?_, ?_, he⟩
  · intro m hm
    have h : m ∈ t.inf id := by
      rw [Submodule.mem_finsetInf]
      intro J hJ
      have hJ' := hm (E ⟨J, hJ⟩)
      simpa [S] using hJ'
    rw [ht.inf_eq] at h
    simpa using h
  · intro i j hij
    by_contra hne
    have hne' : (E.symm i : Submodule R M) ≠ E.symm j := by
      intro h
      exact hne (E.symm.injective (Subtype.ext h))
    exact ht.distinct (E.symm i).2 (E.symm j).2 hne' hij

end Quotient

section Characteristic

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
variable {P : Ideal R} {e : ℕ}

/-- The prime `P` of a coprimary module contains no nonzero integer, or contains a prime number. -/
theorem IsCoprimaryWith.intCast_notMem_or_prime_mem (h : IsCoprimaryWith R M P e) :
    (∀ n : ℤ, n ≠ 0 → (n : R) ∉ P) ∨ ∃ p : ℕ, p.Prime ∧ (p : R) ∈ P := by
  haveI := h.isPrime
  rcases CharP.char_is_prime_or_zero (R ⧸ P) (ringChar (R ⧸ P)) with hp | h0
  · right
    refine ⟨ringChar (R ⧸ P), hp, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    simp
  · left
    intro n hn hmem
    haveI : CharP (R ⧸ P) 0 := ringChar.of_eq h0
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_intCast,
      CharP.intCast_eq_zero_iff (R ⧸ P) 0] at hmem
    exact hn (by simpa using hmem)

/-- An integer outside `P` acts injectively on a coprimary module. -/
theorem IsCoprimaryWith.zsmul_injective (h : IsCoprimaryWith R M P e) {n : ℤ}
    (hn : (n : R) ∉ P) : Function.Injective fun x : M => n • x := by
  intro x y hxy
  apply h.smul_injective_of_notMem (n : R) hn
  simpa only [Int.cast_smul_eq_zsmul] using hxy

/-- A prime number in `P` annihilates a coprimary module to the power `e`. -/
theorem IsCoprimaryWith.pow_zsmul_eq_zero (h : IsCoprimaryWith R M P e) {p : ℕ}
    (hp : (p : R) ∈ P) (x : M) : ((p : ℤ) ^ e) • x = 0 := by
  have hx := h.smul_eq_zero_of_mem_pow ((p : R) ^ e) (Ideal.pow_mem_pow hp e) x
  rw [← Int.cast_smul_eq_zsmul R, Int.cast_pow, Int.cast_natCast]
  exact hx

/-- **Characteristic dichotomy.** A coprimary module is torsion-free as an abelian group, or is
annihilated by `p ^ e` for a prime `p` lying in its prime `P`. -/
theorem IsCoprimaryWith.torsionFree_or_primeExponent (h : IsCoprimaryWith R M P e) :
    (∀ n : ℤ, n ≠ 0 → Function.Injective fun x : M => n • x) ∨
      ∃ p : ℕ, p.Prime ∧ (p : R) ∈ P ∧ ∀ x : M, ((p : ℤ) ^ e) • x = 0 := by
  rcases h.intCast_notMem_or_prime_mem with h0 | ⟨p, hp, hpP⟩
  · exact Or.inl fun n hn => h.zsmul_injective (h0 n hn)
  · exact Or.inr ⟨p, hp, hpP, h.pow_zsmul_eq_zero hpP⟩

end Characteristic

end Primary
end BooneHigman
end GroupApproximation
