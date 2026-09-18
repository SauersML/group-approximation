import GroupApproximation.BooneHigman.Metabelian.SuslinHorrocksReduce
import GroupApproximation.Meta.AxiomGuard

/-!
# Local Horrocks, part 2: lowering the degree of the monic entry

Lane `bh-met-90a`.  Horrocks' degree-lowering step over a local ring `R`.  Let row `r` of an
invertible `M` over `R[X]` have a monic entry `f = M r t` of degree `d + 1`.

1. Reduce the other entries of the row modulo `f` (`suslinHorrocks_exists_row_modByMonic`).
2. Some reduced entry `g = M r c`, `c ≠ t`, is nonzero modulo `𝔪`
   (`suslinHorrocks_exists_residue_ne_zero`).  Let `j = deg ḡ ≤ d`.
3. `h = (X^(d-j) g) %ₘ f` has residue `X^(d-j) ḡ` (degree `d < d + 1`), so its coefficient of
   degree `d` is a unit `u` and `v = u⁻¹ h = g a + f b` is monic of degree `d`
   (`suslinHorrocks_exists_monic_combo`).
4. For a third column `e ∉ {t, c}` with entry `w₀`, adding `g · a w` and `f · b w` with
   `w = 1 - w₀ /ₘ v` makes the entry `v + w₀ %ₘ v`, monic of degree `d`
   (`suslinHorrocks_monic_add_mod`).  This needs at least three columns.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- `w₀ + v (1 - w₀ /ₘ v) = v + w₀ %ₘ v` is monic of the degree of the monic `v`. -/
theorem suslinHorrocks_monic_add_mod [Nontrivial R] (v w₀ : Polynomial R) (d : ℕ)
    (hv : v.Monic) (hvd : v.natDegree = d) :
    (w₀ + v * (1 - w₀ /ₘ v)).Monic ∧ (w₀ + v * (1 - w₀ /ₘ v)).natDegree = d := by
  have heq : w₀ + v * (1 - w₀ /ₘ v) = v + w₀ %ₘ v := by
    rw [Polynomial.modByMonic_eq_sub_mul_div]
    ring
  have hlt : (w₀ %ₘ v).degree < v.degree := Polynomial.degree_modByMonic_lt _ hv
  rw [heq]
  exact ⟨hv.add_of_left hlt, (Polynomial.natDegree_add_eq_left_of_degree_lt hlt).trans hvd⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinHorrocks_monic_add_mod

/-- **A monic combination of lower degree.**  Over a local ring, if `f` is monic of degree
`d + 1` and `g` has smaller degree and is nonzero modulo `𝔪`, then some `g a + f b` is monic of
degree `d`. -/
theorem suslinHorrocks_exists_monic_combo [IsLocalRing R] (f g : Polynomial R) (d : ℕ)
    (hf : f.Monic) (hfd : f.natDegree = d + 1) (hgf : g.degree < f.degree)
    (hg : g.map (IsLocalRing.residue R) ≠ 0) :
    ∃ a b : Polynomial R, (g * a + f * b).Monic ∧ (g * a + f * b).natDegree = d := by
  obtain ⟨gb, hgb⟩ : ∃ gb, g.map (IsLocalRing.residue R) = gb := ⟨_, rfl⟩
  rw [hgb] at hg
  obtain ⟨j, hj⟩ : ∃ j, gb.natDegree = j := ⟨_, rfl⟩
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [Polynomial.map_zero] at hgb
    exact hg hgb.symm
  have hjd : j ≤ d := by
    have h1 : gb.natDegree ≤ g.natDegree := by
      rw [← hgb]
      exact Polynomial.natDegree_map_le
    have h2 : g.natDegree < f.natDegree := Polynomial.natDegree_lt_natDegree hg0 hgf
    omega
  have hπf : (f.map (IsLocalRing.residue R)).Monic := hf.map (IsLocalRing.residue R)
  have hπfd : (f.map (IsLocalRing.residue R)).natDegree = d + 1 := by
    rw [hf.natDegree_map (IsLocalRing.residue R), hfd]
  obtain ⟨q, hq⟩ : ∃ q, (Polynomial.X ^ (d - j) * g) /ₘ f = q := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h, (Polynomial.X ^ (d - j) * g) %ₘ f = h := ⟨_, rfl⟩
  have hhq : h = Polynomial.X ^ (d - j) * g - f * q := by
    rw [← hh, ← hq, Polynomial.modByMonic_eq_sub_mul_div]
  have hhmap : h.map (IsLocalRing.residue R) = Polynomial.X ^ (d - j) * gb := by
    rw [← hh, Polynomial.map_modByMonic _ hf, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, hgb, (Polynomial.modByMonic_eq_self_iff hπf).2]
    apply Polynomial.degree_lt_degree
    rw [hπfd]
    have hle := (Polynomial.natDegree_mul_le (p := Polynomial.X ^ (d - j)) (q := gb)).trans
      (Nat.add_le_add (Polynomial.natDegree_X_pow_le (R := IsLocalRing.ResidueField R) (d - j))
        hj.le)
    omega
  have hcoeff : IsLocalRing.residue R (h.coeff d) ≠ 0 := by
    rw [← Polynomial.coeff_map, hhmap, Polynomial.coeff_X_pow_mul', if_pos (Nat.sub_le d j),
      Nat.sub_sub_self hjd, ← hj, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.2 hg
  obtain ⟨u, hu⟩ := (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hcoeff
  have hh0 : h ≠ 0 := by
    rintro rfl
    rw [Polynomial.coeff_zero] at hu
    exact u.ne_zero hu
  have hlt : h.degree < f.degree := by
    rw [← hh]
    exact Polynomial.degree_modByMonic_lt _ hf
  have hhd : h.natDegree ≤ d := by
    have hlt' := Polynomial.natDegree_lt_natDegree hh0 hlt
    omega
  refine ⟨Polynomial.C (↑u⁻¹ : R) * Polynomial.X ^ (d - j), -(Polynomial.C (↑u⁻¹ : R) * q), ?_⟩
  have hcomb : g * (Polynomial.C (↑u⁻¹ : R) * Polynomial.X ^ (d - j)) +
      f * -(Polynomial.C (↑u⁻¹ : R) * q) = Polynomial.C (↑u⁻¹ : R) * h := by
    rw [hhq]
    ring
  rw [hcomb]
  have hvd : (Polynomial.C (↑u⁻¹ : R) * h).coeff d = 1 := by
    rw [Polynomial.coeff_C_mul, ← hu, Units.inv_mul]
  have hvle : (Polynomial.C (↑u⁻¹ : R) * h).natDegree ≤ d :=
    (Polynomial.natDegree_C_mul_le _ _).trans hhd
  refine ⟨Polynomial.monic_of_natDegree_le_of_coeff_eq_one d hvle hvd, le_antisymm hvle ?_⟩
  apply Polynomial.le_natDegree_of_ne_zero
  rw [hvd]
  exact one_ne_zero

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinHorrocks_exists_monic_combo

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
