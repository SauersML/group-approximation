import GroupApproximation.GGT.PNaiveShadow

/-!
# The partner's local gap, and transversality of translates

Second module of property `P_naive` (Abbott--Dahmani, arXiv:1610.04143).
`GGT/PNaiveShadow.lean` gives north--south dynamics for an element `h` with a
local gap at the basepoint.  This module supplies

* **the gap**, with any prescribed slack, for a power of a loxodromic element
  (`exists_pow_local_gap`), from the proved
  `HullGeometry.exists_power_local_backtracking_gap`, whose `δ` is a free
  parameter and can absorb the slack; and
* **transversality**: a translate `g·x` of a point `x` deep in a shadow of the
  partner stays transverse to both ends of the partner.  Two regimes, both
  under the four-point condition alone:
  - `gromovProduct_smul_le_of_bounded` — `g` moves the basepoint by at most `E`
    and `g` carries the end `z` to within Gromov product `D` of the end `z'`;
  - `gromovProduct_smul_le_of_far` — `g` moves the basepoint far, and both
    `g·o` and `g⁻¹·o` are transverse to the ends.

What is *not* here is the uniformity of the constants over all nontrivial
elements of a cyclic subgroup; that is the acylindricity argument of the next
module.

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra` through property `P_naive`;
certifies no printed sentence on its own.
-/

namespace GroupApproximation
namespace GGT
namespace PNaive

open GroupApproximation.HullGeometry

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-! ## The local gap for a power -/

/-- The turn of `h` at `o` is the turn of the orbit at `h·o`. -/
theorem gromovProduct_turn_eq (hiso : IsIsometricAction G X) (h : G) (o : X) :
    gromovProduct (h • o) (h⁻¹ • o) o = gromovProduct o ((h ^ 2) • o) (h • o) := by
  have key := gromovProduct_smul hiso h (h⁻¹ • o) (h • o) o
  rw [smul_inv_smul, smul_smul, ← pow_two] at key
  rw [gromovProduct_comm (h • o) (h⁻¹ • o) o, ← key]

/-- **A power of a loxodromic element has a local gap with any prescribed
slack `D`**: its turn at the basepoint, enlarged to at least `D`, plus `δ`, is
less than half its step. -/
theorem exists_pow_local_gap {δ : ℝ} (hδ0 : 0 ≤ δ) (hiso : IsIsometricAction G X)
    {g : G} {o : X} (hg : IsLoxodromic g o) {D : ℝ} (hD : 0 ≤ D) :
    ∃ k : ℕ, 0 < k ∧
      2 * (max (gromovProduct ((g ^ k) • o) ((g ^ k)⁻¹ • o) o) D + δ) <
        dist o ((g ^ k) • o) := by
  obtain ⟨k, hk, hgap⟩ :=
    exists_power_local_backtracking_gap hiso (add_nonneg hδ0 hD) hg
  refine ⟨k, hk, ?_⟩
  have hturn : gromovProduct ((g ^ k) • o) ((g ^ k)⁻¹ • o) o =
      gromovProduct o ((g ^ (2 * k)) • o) ((g ^ k) • o) := by
    rw [gromovProduct_turn_eq hiso, ← pow_mul, mul_comm]
  rw [hturn]
  have hnn := gromovProduct_nonneg o ((g ^ (2 * k)) • o) ((g ^ k) • o)
  rcases le_total (gromovProduct o ((g ^ (2 * k)) • o) ((g ^ k) • o)) D with hle | hle
  · rw [max_eq_right hle]
    linarith
  · rw [max_eq_left hle]
    linarith

/-- **A local gap makes the partner loxodromic.** -/
theorem isLoxodromic_of_local_gap {δ C : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hiso : IsIsometricAction G X) {h : G} {o : X} (hCδ : 0 ≤ C + δ)
    (hloc : gromovProduct (h • o) (h⁻¹ • o) o ≤ C)
    (hgap : 2 * (C + δ) < dist o (h • o)) : IsLoxodromic h o := by
  refine isLoxodromic_of_local_backtracking hδ hiso hCδ hgap ?_
  rw [← gromovProduct_turn_eq hiso]
  exact hloc

/-! ## Transversality of translates -/

/-- **Transversality for a translate that moves the basepoint little.**  If
`d(o, g·o) ≤ E`, `(g·z | z')_o ≤ D` and `x` lies in the shadow of `z` at depth
`ρ > D + δ + E`, then `(g·x | z')_o ≤ D + δ`. -/
theorem gromovProduct_smul_le_of_bounded {δ D E ρ : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hiso : IsIsometricAction G X) {g : G} {o z z' x : X}
    (hE : dist o (g • o) ≤ E) (hD : gromovProduct (g • z) z' o ≤ D)
    (hρ : D + δ + E < ρ) (hx : x ∈ shadow o z ρ) :
    gromovProduct (g • x) z' o ≤ D + δ := by
  have h1 : gromovProduct (g • x) (g • z) (g • o) = gromovProduct x z o :=
    gromovProduct_smul hiso g x z o
  have h2 := gromovProduct_le_add_dist_base (g • x) (g • z) (g • o) o
  have hdist : dist (g • o) o ≤ E := by
    rw [dist_comm]
    exact hE
  rw [mem_shadow] at hx
  have hfar : gromovProduct (g • z) z' o + δ < gromovProduct (g • x) (g • z) o := by
    linarith
  have hup := gromovProduct_le_add_delta_of_lt hδ hfar
  linarith

/-- **Transversality for a translate that moves the basepoint far.**  If
`g⁻¹·o` is transverse to the end `z` and `g·o` to the end `z'` (Gromov products
at most `I`), `g` moves `o` by more than `2(I+δ)`, and `x` lies in the shadow of
`z` at depth `ρ > I + δ`, then `(g·x | z')_o ≤ I + δ`. -/
theorem gromovProduct_smul_le_of_far {δ I ρ : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hiso : IsIsometricAction G X) {g : G} {o z z' x : X}
    (hIz : gromovProduct z (g⁻¹ • o) o ≤ I) (hIz' : gromovProduct (g • o) z' o ≤ I)
    (hfar : 2 * (I + δ) < dist o (g • o)) (hρ : I + δ < ρ)
    (hx : x ∈ shadow o z ρ) :
    gromovProduct (g • x) z' o ≤ I + δ := by
  have hx' : gromovProduct x (g⁻¹ • o) o ≤ I + δ :=
    gromovProduct_le_of_mem_shadow hδ hIz hρ hx
  have hid := gromovProduct_smul_self_base hiso g x o
  have hfar' : gromovProduct (g • o) z' o + δ < gromovProduct (g • x) (g • o) o := by
    linarith
  have hup := gromovProduct_le_add_delta_of_lt hδ hfar'
  linarith

end PNaive
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.PNaive.gromovProduct_turn_eq
#audit_axioms GroupApproximation.GGT.PNaive.exists_pow_local_gap
#audit_axioms GroupApproximation.GGT.PNaive.isLoxodromic_of_local_gap
#audit_axioms GroupApproximation.GGT.PNaive.gromovProduct_smul_le_of_bounded
#audit_axioms GroupApproximation.GGT.PNaive.gromovProduct_smul_le_of_far
