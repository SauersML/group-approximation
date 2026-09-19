import GroupApproximation.BooneHigmanLinear.LSCore.ZC
import GroupApproximation.Meta.AxiomGuard

/-!
# Lavrenov–Sinchuk's Lemma 4.1(5), type A

A. Lavrenov, S. Sinchuk, *A Horrocks-type theorem for even orthogonal K₂*, Lemma 4.1(5), for
`α = (i, j)`, `β = (j, k)`, `α + β = (i, k)`, `ε = N_{α,β} = 1`:
`z_ik(sη, ξ) = x_ij(s) x_kj(-sξ) x_jk(sξη²) x_ik(sη) z_ij(-s, -ξη) x_ji(-sξ²η²) x_ki(-sξ²η)
z_kj(sξ, -η)` (`z_add_eq`).

The proof is L–S's (4.3):
* write `x_ik(sη) = ⁅x_ij(s), x_jk(η)⁆` and conjugate by `x_ki(ξ)`;
* expand `⁅ab, cd⁆` for commuting pairs `a, b` and `c, d` (`comm_prod`);
* apply Lemma 4.1(2) to the two `z`'s that appear (`z_conj_obtuse_col`).
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace LSCore

open scoped commutatorElement
open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigmanLinear.RelGen (zElt)

section Group

variable {G : Type*} [Group G]

theorem cj_comm (g a b : G) : cj g ⁅a, b⁆ = ⁅cj g a, cj g b⁆ := by
  unfold cj
  rw [commutatorElement_def, commutatorElement_def]
  group

/-- `⁅ab, cd⁆ = a b (d a⁻¹ d⁻¹)^{c⁻¹} (c b⁻¹ c⁻¹)^{d⁻¹}` when `a, b` and `c, d` commute. -/
theorem comm_prod {a b c d : G} (hab : Commute a b) (hcd : Commute c d) :
    ⁅a * b, c * d⁆ = a * b * cj c⁻¹ (d * a⁻¹ * d⁻¹) * cj d⁻¹ (c * b⁻¹ * c⁻¹) := by
  have e1 : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by rw [hab.eq, mul_inv_rev]
  have e2 : (c * d)⁻¹ = c⁻¹ * d⁻¹ := by rw [hcd.eq, mul_inv_rev]
  have e3 : d⁻¹ * c⁻¹ * d * c = 1 := by
    rw [← mul_inv_rev, hcd.eq, mul_assoc, inv_mul_cancel]
  calc ⁅a * b, c * d⁆ = a * b * (c * d) * (a⁻¹ * b⁻¹) * (c⁻¹ * d⁻¹) := by
        rw [commutatorElement_def, e1, e2]
    _ = a * b * c * d * a⁻¹ * (d⁻¹ * c⁻¹ * d * c) * b⁻¹ * c⁻¹ * d⁻¹ := by
        rw [e3]
        group
    _ = _ := by
        unfold cj
        group

end Group

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

/-- `x_ji(e) x_ij(s)⁻¹ x_ji(e)⁻¹ = z_ij(-s, -e)`. -/
theorem z_inv_form {i j : I} (hij : i ≠ j) (s e : R) :
    x j i hij.symm e * (x i j hij s)⁻¹ * (x j i hij.symm e)⁻¹ = zElt i j hij (-s) (-e) := by
  unfold zElt
  simp only [neg_neg, x_neg]

#audit_axioms z_inv_form

/-- `z_ik(sη, ξ) = x_ki(ξ)⁻¹ x_ik(sη) x_ki(ξ)`. -/
theorem zElt_eq_cj {i k : I} (hik : i ≠ k) (s ξ : R) :
    zElt i k hik s ξ = cj (x k i hik.symm ξ) (x i k hik s) := by
  unfold zElt cj
  rw [← x_neg]

/-- **L–S 4.1(5)** for `α = (i, j)`, `β = (j, k)` (`ε = 1`). -/
theorem z_add_eq {i j k : I} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (s ξ η : R) :
    zElt i k hik (s * η) ξ =
      x i j hij s * x k j hjk.symm (-(s * ξ)) * x j k hjk (s * ξ * η ^ 2) * x i k hik (s * η) *
        zElt i j hij (-s) (-(ξ * η)) * x j i hij.symm (-(s * ξ ^ 2 * η ^ 2)) *
        x k i hik.symm (-(s * ξ ^ 2 * η)) * zElt k j hjk.symm (s * ξ) (-η) := by
  have h0 : zElt i k hik (s * η) ξ = cj (x k i hik.symm ξ) ⁅x i j hij s, x j k hjk η⁆ := by
    rw [zElt_eq_cj, x_commutator i j k hij hjk hik]
  rw [h0, cj_comm,
    cj_x_right hik.symm hij hjk.symm ξ s, cj_x_left hjk hik.symm hij.symm η ξ,
    (x_commute_of_ne k j i j hjk.symm hij hij.symm hjk _ _).eq,
    (x_commute_of_ne j i j k hij.symm hjk hij hjk.symm _ _).eq,
    comm_prod (x_commute_of_ne i j k j hij hjk.symm hjk hij.symm _ _)
      (x_commute_of_ne j k j i hjk hij.symm hjk.symm hij _ _),
    z_inv_form hij s (η * ξ), z_inv_form hjk.symm (-(ξ * s)) η]
  simp only [← x_neg]
  rw [z_conj_obtuse_col hjk hij hik, z_conj_obtuse_col hij.symm hjk.symm hik.symm]
  simp only [mul_assoc]
  rw [show -(-(-(ξ * s)) * -η * -(η * ξ)) = -(s * ξ ^ 2 * η ^ 2) by ring,
    show -(-(ξ * s)) * -(η * ξ) = -(s * ξ ^ 2 * η) by ring,
    show -(-s * -(η * ξ) * -η) = s * ξ * η ^ 2 by ring, show -(-(ξ * s)) = s * ξ by ring,
    show -(η * ξ) = -(ξ * η) by ring, show -s * -η = s * η by ring,
    show -(ξ * s) = -(s * ξ) by ring]

#audit_axioms z_add_eq

end LSCore
end BooneHigmanLinear
end GroupApproximation
