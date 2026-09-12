import GroupApproximation.GGT.HullLemmaEe

/-!
# Under an acylindrical action every element is elliptic or escaping

`GGT/HullLemmaEe.lean` records the half of Bowditch's dichotomy the repository
did not prove, as a named proposition:

> `Elementary.EllipticOrEscaping G x` — every element has a bounded orbit, or
> its positive power orbit tends to infinity.

This module proves it for every acylindrical action, with no hyperbolicity.
Together with the proved half (`EscapingIsLoxodromic`, at a hyperbolic
acylindrical alphabet) it returns the dichotomy *elliptic or loxodromic* that
Hull's Lemma `loxorell` asks for.

## The argument

Let `c` have an unbounded positive orbit that does not tend to infinity.  Then
`d(x, cⁿ·x) < A` for infinitely many `n`.  Pick `m` with `d(x, cᵐ·x) ≥ R`, where
`R` is acylindricity's radius at `ε = max A 1`.  Every such power `cⁿ` moves
both `x` and `cᵐ·x` by less than `ε`: the second because `cⁿ` commutes with `cᵐ`.
Acylindricity makes the set of elements with that property finite, so two of
those powers coincide, `c` has finite order, and its orbit is bounded after all.

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra` through property `P_naive`;
certifies no printed sentence on its own.
-/

namespace GroupApproximation
namespace GGT
namespace AcylindricalDichotomy

open GroupApproximation.HullGeometry

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-- **A period bounds the positive orbit.** -/
theorem dist_pow_smul_le_sum_of_pow_eq_one {c : G} {p : ℕ} (hp : 0 < p)
    (hcp : c ^ p = 1) (x : X) (n : ℕ) :
    dist x ((c ^ n) • x) ≤ ∑ r ∈ Finset.range p, dist x ((c ^ r) • x) := by
  have hmod : c ^ n = c ^ (n % p) := by
    conv_lhs => rw [← Nat.mod_add_div n p, pow_add, pow_mul, hcp, one_pow, mul_one]
  rw [hmod]
  exact Finset.single_le_sum (f := fun r : ℕ => dist x ((c ^ r) • x))
    (fun r _ => dist_nonneg) (Finset.mem_range.mpr (Nat.mod_lt n hp))

/-- **A bounded positive orbit is a bounded orbit.**  Negative powers move the
basepoint as far as the corresponding positive powers. -/
theorem isElliptic_of_bounded_nat (hiso : IsIsometricAction G X) {c : G} {x : X}
    {C : ℝ} (hC : ∀ n : ℕ, dist x ((c ^ n) • x) ≤ C) : IsElliptic c x := by
  refine ⟨C, fun n => ?_⟩
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simpa only [zpow_natCast] using hC k
  · have hmove := hiso (c ^ k) x ((c ^ (-(k : ℤ))) • x)
    rw [smul_smul, ← zpow_natCast, ← zpow_add, add_neg_cancel, zpow_zero, one_smul,
      zpow_natCast] at hmove
    rw [← hmove, dist_comm]
    exact hC k

/-- **Every element of an acylindrical action is elliptic or escaping.** -/
theorem ellipticOrEscaping_of_isAcylindrical (hiso : IsIsometricAction G X)
    (hacy : IsAcylindrical G X) (x : X) : Elementary.EllipticOrEscaping G x := by
  intro c
  by_cases hbdd : ∃ C : ℝ, ∀ n : ℕ, dist x ((c ^ n) • x) ≤ C
  · obtain ⟨C, hC⟩ := hbdd
    exact Or.inl (isElliptic_of_bounded_nat hiso hC)
  · refine Or.inr ?_
    rw [IsEscaping, Filter.tendsto_atTop]
    intro A
    by_contra hnot
    rw [Filter.eventually_atTop] at hnot
    -- infinitely many powers move `x` by less than `A`
    let T : Set ℕ := {n | dist x ((c ^ n) • x) < A}
    have hTinf : T.Infinite := by
      refine Set.infinite_of_not_bddAbove ?_
      rintro ⟨N, hN⟩
      refine hnot ⟨N + 1, fun n hn => ?_⟩
      by_contra hlt
      have hmem : n ∈ T := lt_of_not_ge hlt
      have := hN hmem
      omega
    -- acylindricity at `ε = max A 1`
    obtain ⟨R, Nb, hRN⟩ := hacy (max A 1) (lt_of_lt_of_le one_pos (le_max_right A 1))
    obtain ⟨m, hm⟩ : ∃ m : ℕ, R ≤ dist x ((c ^ m) • x) := by
      by_contra hall
      refine hbdd ⟨R, fun n => ?_⟩
      by_contra hn
      exact hall ⟨n, le_of_lt (lt_of_not_ge hn)⟩
    have hfin := (hRN x ((c ^ m) • x) hm).1
    have hmaps : Set.MapsTo (fun n : ℕ => c ^ n) T
        {g : G | dist x (g • x) ≤ max A 1 ∧
          dist ((c ^ m) • x) (g • (c ^ m) • x) ≤ max A 1} := by
      intro n hn
      have hn' : dist x ((c ^ n) • x) < A := hn
      refine ⟨le_trans hn'.le (le_max_left A 1), ?_⟩
      have hcomm : (c ^ n) • (c ^ m) • x = (c ^ m) • (c ^ n) • x := by
        rw [smul_smul, smul_smul, ← pow_add, ← pow_add, add_comm]
      rw [hcomm, hiso (c ^ m) x ((c ^ n) • x)]
      exact le_trans hn'.le (le_max_left A 1)
    obtain ⟨a, _ha, b, _hb, hab, heq⟩ := hTinf.exists_ne_map_eq_of_mapsTo hmaps hfin
    -- two equal powers give a period, hence a bounded orbit
    refine hbdd ?_
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · have hp : 0 < b - a := by omega
      have hcp : c ^ (b - a) = 1 := by
        have h1 : c ^ b = c ^ a * c ^ (b - a) := by
          rw [← pow_add]
          congr 1
          omega
        have heq' : c ^ a = c ^ b := heq
        rw [h1] at heq'
        exact mul_eq_left.mp heq'.symm
      exact ⟨_, dist_pow_smul_le_sum_of_pow_eq_one hp hcp x⟩
    · have hp : 0 < a - b := by omega
      have hcp : c ^ (a - b) = 1 := by
        have h1 : c ^ a = c ^ b * c ^ (a - b) := by
          rw [← pow_add]
          congr 1
          omega
        have heq' : c ^ a = c ^ b := heq
        rw [h1] at heq'
        exact mul_eq_left.mp heq'
      exact ⟨_, dist_pow_smul_le_sum_of_pow_eq_one hp hcp x⟩

end AcylindricalDichotomy
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.AcylindricalDichotomy.dist_pow_smul_le_sum_of_pow_eq_one
#audit_axioms GroupApproximation.GGT.AcylindricalDichotomy.isElliptic_of_bounded_nat
#audit_axioms GroupApproximation.GGT.AcylindricalDichotomy.ellipticOrEscaping_of_isAcylindrical
