import GroupApproximation.Kazhdan.GHWCharZeroPlaces
import GroupApproximation.Algebra.ValuationWithTopInt
import GroupApproximation.Meta.AxiomGuard

/-!
# Additive places over `ℚ(t_1, …, t_d)` bounding minimal polynomials

A step toward "every countable subgroup of `GL_2` over a field has the Haagerup property"
(`non_mf_groups_exist.tex`, the remark after `prop:torsion-defect-ring`, tex lines 1146--1147),
in characteristic zero.

Let `B = ℤ[t_1, …, t_d]`, `L = Frac B`, `K / L` finite and `M > 0`.  `exists_places_minpoly_coeff`
gives finitely many additive discrete valuations `v_j` of `K` with uniformizers `π_j` such that,
whenever `M^k b` is integral over `B` for some `k` and `v_j b ≥ -N` for all `j`, every coefficient
of the minimal polynomial of `M^N b` over `L` is an integer polynomial of total degree at most
`N [K : L]`.  These are the places of `K` over the total-degree place of `L` and over the `p`-adic
places of `L` for the primes `p ∣ M` (`GHW.exists_places_minpoly_coeff`), made additive by
`ValuationWithTopInt.addVal`.
-/

namespace GroupApproximation
namespace IntegerPlacesMinpoly

/-- **The non-archimedean places over `ℚ(t_1, …, t_d)`, as additive valuations.** -/
theorem exists_places_minpoly_coeff (d : ℕ) (K : Type) [Field K] [CharZero K]
    [Algebra (FractionRing (MvPolynomial (Fin d) ℤ)) K]
    [FiniteDimensional (FractionRing (MvPolynomial (Fin d) ℤ)) K]
    [Algebra (MvPolynomial (Fin d) ℤ) K]
    [IsScalarTower (MvPolynomial (Fin d) ℤ) (FractionRing (MvPolynomial (Fin d) ℤ)) K]
    {M : ℕ} (hM : 0 < M) :
    ∃ (r : ℕ) (v : Fin r → AddValuation K (WithTop ℤ)) (π : Fin r → K), (∀ j, v j (π j) = 1) ∧
      ∀ (N : ℕ) (b : K), (∃ k : ℕ, IsIntegral (MvPolynomial (Fin d) ℤ) ((M : K) ^ k * b)) →
        (∀ j, (((-(N : ℤ)) : ℤ) : WithTop ℤ) ≤ v j b) → ∀ i : ℕ,
          ∃ G : MvPolynomial (Fin d) ℤ,
            G.totalDegree ≤ N * Module.finrank (FractionRing (MvPolynomial (Fin d) ℤ)) K ∧
            algebraMap (MvPolynomial (Fin d) ℤ) (FractionRing (MvPolynomial (Fin d) ℤ)) G =
              (minpoly (FractionRing (MvPolynomial (Fin d) ℤ)) ((M : K) ^ N * b)).coeff i := by
  obtain ⟨r, u, hunif, hcoeff⟩ := GHW.exists_places_minpoly_coeff d M hM K
  choose ϖ hϖ using hunif
  refine ⟨r, fun j ↦ ValuationWithTopInt.addVal (u j), ϖ,
    fun j ↦ ValuationWithTopInt.addVal_eq_one (u j) (hϖ j), fun N b hb hv i ↦ ?_⟩
  obtain ⟨k, hk⟩ := hb
  refine hcoeff N k b hk (fun j ↦ ?_) i
  by_cases hb0 : b = 0
  · rw [hb0, Valuation.map_zero]
    exact zero_le
  · exact (ValuationWithTopInt.neg_le_addVal_iff (u j) hb0 (N : ℤ)).mp (hv j)

end IntegerPlacesMinpoly
end GroupApproximation

#audit_axioms GroupApproximation.IntegerPlacesMinpoly.exists_places_minpoly_coeff
