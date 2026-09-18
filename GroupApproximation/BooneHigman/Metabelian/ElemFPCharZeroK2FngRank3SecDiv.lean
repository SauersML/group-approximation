import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngGtOneRank3Coset
import Mathlib.Tactic.LinearCombination
import GroupApproximation.Meta.AxiomGuard

/-!
# The coset residual when `p ∣ m` (lane `bh-met-93x`, part 1)

Residual of lane `bh-met-93s`: `czK2FngGtOneRank3_CosetStatement`.  This file proves the
case `p ∣ m` of it outright.

If `p ∣ m`, write `m = p k`.  Then `mp ∣ m²`, so `1/(mp) = k/m²` already lies in `ℤ[1/m]`, and
the localisation map `φ : ℤ[1/m] → ℤ[1/(mp)]` is **surjective**
(`czK2FngRank3Sec_locMap_surjective`).  Explicitly, if `z · (mp)^n = a`, then
`z = φ(a · k^n · (1/m)^{2n})`.  So `ringMap φ` is surjective and
`Q = Φ(St_3(ℤ[1/m])) ⊔ N` is the whole group.  The constant section `σ = 1` then passes every
check, with `s = ∅` (`czK2FngRank3Sec_sectionProp_of_surjective`,
`czK2FngRank3Sec_coset_of_dvd`).

Such primes do occur in the prime induction of `bh-met-93s`: `n = c · minFac n` with
`minFac n ∣ c`, for example `n = p²`.

Proved outright.  There are no hypotheses and no literature inputs.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

/-- **`ℤ[1/m] → ℤ[1/(mp)]` is surjective when `p ∣ m`.** -/
theorem czK2FngRank3Sec_locMap_surjective (m p : ℕ) (hpm : p ∣ m) :
    Function.Surjective (czK2FngGtOneRank3_locMap m p) := by
  obtain ⟨k, hk⟩ := hpm
  intro z
  obtain ⟨n, a, hz⟩ := IsLocalization.Away.surj ((m * p : ℕ) : ℤ) z
  have hv : algebraMap ℤ (Localization.Away ((m * p : ℕ) : ℤ)) (m : ℤ) *
      czK2FngGtOneRank3_locMap m p
        (IsLocalization.Away.invSelf (m : ℤ) : Localization.Away (m : ℤ)) = 1 := by
    rw [← czK2FngGtOneRank3_locMap_algebraMap m p (m : ℤ), ← map_mul,
      IsLocalization.Away.mul_invSelf, map_one]
  have hv2 : algebraMap ℤ (Localization.Away ((m * p : ℕ) : ℤ)) (m : ℤ) ^ (2 * n) *
      czK2FngGtOneRank3_locMap m p
        (IsLocalization.Away.invSelf (m : ℤ) : Localization.Away (m : ℤ)) ^ (2 * n) = 1 := by
    rw [← mul_pow, hv, one_pow]
  have hN : m ^ (2 * n) = (m * p) ^ n * k ^ n := by
    subst hk
    ring
  have hmk : (m : ℤ) ^ (2 * n) = ((m * p : ℕ) : ℤ) ^ n * (k : ℤ) ^ n := by
    exact_mod_cast hN
  have hmkS : algebraMap ℤ (Localization.Away ((m * p : ℕ) : ℤ)) (m : ℤ) ^ (2 * n) =
      algebraMap ℤ (Localization.Away ((m * p : ℕ) : ℤ)) ((m * p : ℕ) : ℤ) ^ n *
        algebraMap ℤ (Localization.Away ((m * p : ℕ) : ℤ)) (k : ℤ) ^ n := by
    rw [← map_pow, ← map_pow, ← map_pow, ← map_mul, hmk]
  refine ⟨algebraMap ℤ (Localization.Away (m : ℤ)) a *
      algebraMap ℤ (Localization.Away (m : ℤ)) (k : ℤ) ^ n *
      (IsLocalization.Away.invSelf (m : ℤ) : Localization.Away (m : ℤ)) ^ (2 * n), ?_⟩
  rw [map_mul, map_mul, map_pow, map_pow, czK2FngGtOneRank3_locMap_algebraMap,
    czK2FngGtOneRank3_locMap_algebraMap]
  linear_combination
    (-(algebraMap ℤ (Localization.Away ((m * p : ℕ) : ℤ)) (k : ℤ) ^ n *
        czK2FngGtOneRank3_locMap m p
          (IsLocalization.Away.invSelf (m : ℤ) : Localization.Away (m : ℤ)) ^ (2 * n))) * hz -
      z * czK2FngGtOneRank3_locMap m p
          (IsLocalization.Away.invSelf (m : ℤ) : Localization.Away (m : ℤ)) ^ (2 * n) * hmkS +
      z * hv2

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Sec_locMap_surjective

/-- **A surjective coefficient map makes every section pass.**  If `φ` is surjective, then
`Q = ⊤`, so the constant section `σ = 1` satisfies `SectionProp φ s u` for every `s` and `u`. -/
theorem czK2FngRank3Sec_sectionProp_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ) (s : Set (SteinbergGroup (Fin 3) S)) (u : S) :
    czK2FngGtOneRank3_SectionProp φ s u := by
  have hsurj : Function.Surjective (ringMap (I := Fin 3) φ) :=
    ringMap_surjective_of_surjective φ hφ
  have hQ : ∀ g : SteinbergGroup (Fin 3) S, g ∈ czK2FngGtOneRank3_Q φ s := by
    intro g
    unfold czK2FngGtOneRank3_Q
    exact Subgroup.mem_sup_left (MonoidHom.mem_range.mpr (hsurj g))
  refine ⟨fun _ ↦ 1, hQ _, fun _ _ _ ↦ ?_, fun _ _ _ ↦ ?_⟩
  · intro _
    exact hQ _
  · intro _
    exact hQ _

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Sec_sectionProp_of_surjective

/-- **The case `p ∣ m` of `czK2FngGtOneRank3_CosetStatement`, proved outright** (with `s = ∅`
and `σ = 1`). -/
theorem czK2FngRank3Sec_coset_of_dvd (m p : ℕ) (hpm : p ∣ m) :
    ∃ s : Set (SteinbergGroup (Fin 3) (Localization.Away ((m * p : ℕ) : ℤ))), s.Finite ∧
      s ⊆ K2 (Fin 3) (Localization.Away ((m * p : ℕ) : ℤ)) ∧
      czK2FngGtOneRank3_SectionProp (czK2FngGtOneRank3_locMap m p) s
        (IsLocalization.Away.invSelf ((m * p : ℕ) : ℤ) :
          Localization.Away ((m * p : ℕ) : ℤ)) :=
  ⟨∅, Set.finite_empty, Set.empty_subset _,
    czK2FngRank3Sec_sectionProp_of_surjective _ (czK2FngRank3Sec_locMap_surjective m p hpm) _ _⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Sec_coset_of_dvd

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
