import GroupApproximation.BooneHigman.SteinbergBasic.Naturality
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral
import GroupApproximation.Meta.AxiomGuard

/-!
# Centrality of unstable `K₂` from injective stabilization (lane bh-met-95d, bonus)

## Truth check (LOUD)

The lane's bonus `nkStep_K2_central` asks that `K₂(N, R)` be central in `St(N, R)` for `N ≥ 3`.
That is **not a self-contained fact**:

* for commutative `R` and `N ≥ 4` it is van der Kallen's theorem, which is a literature input;
* for `N = 3` I believe it is open in general.

The *padded* form is already in the corpus, unconditionally for every ring and every `n`:
`LeavittK2.map_stab_K2_le_center`, which says `stab K₂(n, R) ≤ center St(n+1, R)`.  It is not
duplicated here.

## What this file proves

`nkStep_K2_central_of_stab_injective`: if `K2Stab : K₂(n, R) → K₂(n+1, R)` is injective, then
`K₂(n, R)` is central in `St(n, R)`.

For `k ∈ K₂(n)` and `g ∈ St(n)`, the commutator `g k g⁻¹ k⁻¹` lies in `K₂(n)`.  By padded
centrality its stabilization is `1`, so by injectivity the commutator itself is `1`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPNKStep

open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2 (map_stab_K2_le_center)

/-- Unstable `K₂(n, R)` is central in `St(n, R)` whenever stabilization `K₂(n) → K₂(n+1)` is
injective.  The input is the corpus' padded centrality. -/
theorem nkStep_K2_central_of_stab_injective {R : Type*} [Ring R] {n : ℕ}
    (hinj : ∀ u : K2n n R, K2Stab n R u = 1 → u = 1) :
    K2n n R ≤ Subgroup.center (St n R) := by
  intro k hk
  rw [Subgroup.mem_center_iff]
  intro g
  have hc : g * k * g⁻¹ * k⁻¹ ∈ K2n n R :=
    (K2n n R).mul_mem
      (Subgroup.Normal.conj_mem (inferInstance : (K2 (Fin n) R).Normal) k hk g)
      ((K2n n R).inv_mem hk)
  have hcen := Subgroup.mem_center_iff.mp
    (map_stab_K2_le_center (R := R) (n := n) (Subgroup.mem_map_of_mem (stab n R) hk))
    (stab n R g)
  have h1 : K2Stab n R ⟨g * k * g⁻¹ * k⁻¹, hc⟩ = 1 := by
    apply Subtype.ext
    show stab n R (g * k * g⁻¹ * k⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcen, mul_inv_cancel_right,
      mul_inv_cancel]
  have h2 : g * k * g⁻¹ * k⁻¹ = 1 := congrArg Subtype.val (hinj _ h1)
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h2)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPNKStep.nkStep_K2_central_of_stab_injective

end GroupApproximation.BooneHigman.Metabelian.ElemFPNKStep
