import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Hom
import GroupApproximation.BooneHigman.GroupRing.Noetherian
import GroupApproximation.BooneHigman.Primary.Coprimary
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEOneProofField
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighModule
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighDevissageBlock
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighDevissageStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# High exponent: reduction of the module statement to coprimary modules

Lanes bh-met-67, bh-met-67c.  Endpoint:
`pureCharPrimeEHighModule_of_eHighDevissageCoprimary :
  EHighDevissageCoprimaryStatement → PureCharPrimeEHighModuleStatement`.

Route (the multiplicative analogue of `pureCharPrimeEOne`, `PureCharPrimeEOneProof`).
`R = (ℤ/p^e)[Q]` is Noetherian: `ZMod (p ^ e)` is finite, hence Noetherian, and Hilbert's basis
theorem applies (`GroupRing.isNoetherianRing_monoidAlgebra`).  So the finite module `M` has a
coprimary decomposition `0 = S_1 ∩ … ∩ S_n` (`Primary.exists_coprimary_decomposition`).  Every
associated prime `P_j` contains `p`: `p ^ e = 0` in `R` (`eHighDevissage_natCast_pow_eq_zero`)
and `P_j` is prime.  The residual statement linearises each `M ⧸ S_j` multiplicatively over a
field `K_j` of characteristic `p`.  All `K_j` embed in one field `L` of characteristic `p`
(`exists_common_field_charP_finset`), and the block-diagonal representation
(`eHighDevissage_exists_gl_of_field_pieces`) is faithful, because the `S_j` jointly detect `0`.
The witness hypothesis `∃ m, p ^ (e - 1) • m ≠ 0` of the target is not used.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

/-- `p ^ e = 0` in the group ring `(ℤ/p^e)[Q]`. -/
theorem eHighDevissage_natCast_pow_eq_zero (p e : ℕ) (Q : Type) [CommGroup Q] :
    ((p : ℕ) : MonoidAlgebra (ZMod (p ^ e)) Q) ^ e = 0 := by
  rw [← Nat.cast_pow]
  show (MonoidAlgebra.single (1 : Q) ((p ^ e : ℕ) : ZMod (p ^ e)) :
    MonoidAlgebra (ZMod (p ^ e)) Q) = 0
  rw [ZMod.natCast_self]
  exact MonoidAlgebra.single_zero (1 : Q)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighDevissage_natCast_pow_eq_zero

/-- **Endpoint.**  The high-exponent module statement follows from its coprimary case. -/
theorem pureCharPrimeEHighModule_of_eHighDevissageCoprimary
    (hc : EHighDevissageCoprimaryStatement) : PureCharPrimeEHighModuleStatement := by
  intro p hp e he Q _ hQ hfg M _ _ hfin _
  letI : CommGroup Q := { ‹Group Q› with mul_comm := hQ }
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  haveI : IsNoetherianRing (ZMod (p ^ e)) :=
    _root_.isNoetherian_of_finite (ZMod (p ^ e)) (ZMod (p ^ e))
  haveI : Group.FG Q := hfg
  haveI : Module.Finite (MonoidAlgebra (ZMod (p ^ e)) Q) M := hfin
  haveI : IsNoetherianRing (MonoidAlgebra (ZMod (p ^ e)) Q) :=
    GroupRing.isNoetherianRing_monoidAlgebra
  obtain ⟨n, S, P, k, hS, -, hP⟩ :=
    Primary.exists_coprimary_decomposition (MonoidAlgebra (ZMod (p ^ e)) Q) M
  have hpP : ∀ j, ((p : ℕ) : MonoidAlgebra (ZMod (p ^ e)) Q) ∈ P j := by
    intro j
    refine (hP j).isPrime.mem_of_pow_mem e ?_
    exact (congrArg (· ∈ P j) (eHighDevissage_natCast_pow_eq_zero p e Q)).mpr (P j).zero_mem
  choose K _ d κ ρ hchar hinj hequiv using
    fun j : Fin n => hc p hp e he Q hfg (M ⧸ S j) inferInstance (P j) (k j) (hP j) (hpP j)
  haveI : ∀ j, CharP (K j) p := fun j => ringChar.eq_iff.mp (hchar j)
  obtain ⟨L, _, hL, hemb⟩ := exists_common_field_charP_finset p K Finset.univ
  have f : ∀ j, K j →+* L := fun j => Classical.choice (hemb j (Finset.mem_univ j))
  let κM : ∀ j : Fin n,
      Multiplicative M →* Matrix.GeneralLinearGroup (Fin (d j)) (K j) :=
    fun j => (κ j).comp (AddMonoidHom.toMultiplicative (S j).mkQ.toAddMonoidHom)
  have hdet : ∀ m : Multiplicative M, (∀ j, κM j m = 1) → m = 1 := by
    intro m hm
    have h0 : Multiplicative.toAdd m = 0 := hS _ fun i => by
      have h1 : κ i (Multiplicative.ofAdd
          (Submodule.Quotient.mk (Multiplicative.toAdd m) : M ⧸ S i)) = κ i 1 :=
        (hm i).trans (map_one (κ i)).symm
      have h2 : Multiplicative.ofAdd
          (Submodule.Quotient.mk (Multiplicative.toAdd m) : M ⧸ S i) =
          Multiplicative.ofAdd (0 : M ⧸ S i) :=
        hinj i h1
      exact (Submodule.Quotient.mk_eq_zero (S i)).mp (Multiplicative.ofAdd.injective h2)
    calc m = Multiplicative.ofAdd (Multiplicative.toAdd m) := (ofAdd_toAdd m).symm
      _ = Multiplicative.ofAdd (0 : M) := by rw [h0]
      _ = 1 := ofAdd_zero
  have hpc : ∀ (j : Fin n) (q : Q) (m : Multiplicative M),
      κM j (Multiplicative.ofAdd
        (MonoidAlgebra.of (ZMod (p ^ e)) Q q • Multiplicative.toAdd m)) =
        ρ j q * κM j m * (ρ j q)⁻¹ := by
    intro j q m
    exact hequiv j q (Submodule.Quotient.mk (Multiplicative.toAdd m))
  obtain ⟨d', κ', ρ', hinj', hequiv'⟩ :=
    eHighDevissage_exists_gl_of_field_pieces
      (fun (q : Q) (m : Multiplicative M) => Multiplicative.ofAdd
        (MonoidAlgebra.of (ZMod (p ^ e)) Q q • Multiplicative.toAdd m))
      K f d κM ρ hdet hpc
  exact ⟨L, inferInstance, d', κ', ρ', ringChar.eq_iff.mpr hL, hinj',
    fun q m => hequiv' q (Multiplicative.ofAdd m)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.pureCharPrimeEHighModule_of_eHighDevissageCoprimary

end GroupApproximation.BooneHigman.Metabelian.Coprimary
