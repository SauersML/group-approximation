import GroupApproximation.BooneHigmanLinear.RelGen.Defs
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import GroupApproximation.Meta.AxiomGuard

/-!
# The elements `z_α(s, ξ)` and `c_α(s, t)` and Lavrenov–Sinchuk's Lemma 4.1 (1)–(4), type A

A. Lavrenov, S. Sinchuk, *A Horrocks-type theorem for even orthogonal K₂*, Doc. Math. 25
(2020), §4 (piece H.L4 of k2-poly). In type `A_I` a root is an index pair `α = (i, j)`, `i ≠ j`,
with `x_α = x_ij` and `-α = (j, i)`. L–S write `y^g = g⁻¹ y g` (`cj g y`) and
* `z_α(s, ξ) = x_α(s)^{x_{-α}(ξ)} = x_ji(-ξ) x_ij(s) x_ji(ξ)` (`RelGen.zElt`, lane bh-pal-wire);
* `c_α(s, t) = [x_α(s), x_{-α}(t)]` (`RelGen.cElt`).

The type-A structure constants are `N_{(i,j),(j,k)} = 1` and `N_{(j,k),(i,j)} = -1`, from
`⁅x_ij(a), x_jk(b)⁆ = x_ik(ab)`. For `α = (i, j)`, Lemma 4.1 reads:
* (1) `z_α(s, ξ)^{x_{-α}(η)} = z_α(s, ξ + η)` (`z_conj_neg`);
* (2) `α + β ∈ Φ`: `β = (j, l)` (`z_conj_obtuse_row`) or `β = (k, i)` (`z_conj_obtuse_col`);
* (3) `α - β ∈ Φ`: `β = (i, l)` (`z_conj_acute_row`) or `β = (k, j)` (`z_conj_acute_col`);
* (4) `α ⊥ β` (`z_conj_disj`).

The proofs move root elements past each other with `mv_fwd`/`mv_rev` (the commutator relation)
and with `Commute.left_comm` (the commuting relations).
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace LSCore

open scoped commutatorElement
open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigmanLinear.RelGen (zElt cElt)

section Conj

variable {G : Type*} [Group G]

/-- `y^g = g⁻¹ y g`. -/
def cj (g y : G) : G := g⁻¹ * y * g

theorem cj_mul (g y y' : G) : cj g (y * y') = cj g y * cj g y' := by
  unfold cj
  group

theorem cj_of_commute {g y : G} (h : Commute g y) : cj g y = y := by
  unfold cj
  rw [mul_assoc, ← h.eq, inv_mul_cancel_left]

end Conj

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

section Moves

variable {p q r : I} (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r)

/-- `x_pq(c) x_qr(d) = x_pr(cd) x_qr(d) x_pq(c)`. -/
theorem mv_fwd (c d : R) (g : SteinbergGroup I R) :
    x p q hpq c * (x q r hqr d * g) = x p r hpr (c * d) * (x q r hqr d * (x p q hpq c * g)) := by
  rw [← x_commutator p q r hpq hqr hpr c d, commutatorElement_def]
  group

/-- `x_qr(d) x_pq(c) = x_pr(-(cd)) x_pq(c) x_qr(d)`. -/
theorem mv_rev (c d : R) (g : SteinbergGroup I R) :
    x q r hqr d * (x p q hpq c * g) =
      x p r hpr (-(c * d)) * (x p q hpq c * (x q r hqr d * g)) := by
  rw [x_neg, ← x_commutator p q r hpq hqr hpr c d, commutatorElement_def]
  group

/-- `x_pq(b)⁻¹ x_qr(... )`: `cj (x_qr(d)) (x_pq(c)) = x_pr(cd) x_pq(c)`. -/
theorem cj_x_left (c d : R) :
    cj (x q r hqr d) (x p q hpq c) = x p r hpr (c * d) * x p q hpq c := by
  unfold cj
  have h := mv_rev hpq hqr hpr c (-d) (x q r hqr d)
  rw [← x_neg, mul_assoc, h, x_mul, neg_add_cancel, x_zero, mul_one, mul_neg, neg_neg]

/-- `cj (x_pq(c)) (x_qr(d)) = x_pr(-(cd)) x_qr(d)`. -/
theorem cj_x_right (c d : R) :
    cj (x p q hpq c) (x q r hqr d) = x p r hpr (-(c * d)) * x q r hqr d := by
  unfold cj
  have h := mv_fwd hpq hqr hpr (-c) d (x p q hpq c)
  rw [← x_neg, mul_assoc, h, x_mul, neg_add_cancel, x_zero, mul_one, neg_mul]

end Moves

theorem x_add_tail (i j : I) (hij : i ≠ j) (a b : R) (g : SteinbergGroup I R) :
    x i j hij a * (x i j hij b * g) = x i j hij (a + b) * g := by
  rw [← mul_assoc, x_mul]

/-- **L–S 4.1(1)**: `z_α(s, ξ)^{x_{-α}(η)} = z_α(s, ξ + η)`. -/
theorem z_conj_neg (i j : I) (hij : i ≠ j) (s ξ η : R) :
    cj (x j i hij.symm η) (zElt i j hij s ξ) = zElt i j hij s (ξ + η) := by
  unfold cj zElt
  rw [← x_neg]
  simp only [mul_assoc]
  rw [x_add_tail, x_mul, show -η + -ξ = -(ξ + η) by ring]

#audit_axioms z_conj_neg

/-- **L–S 4.1(4)**: `z_β(s, ξ)^{x_α(η)} = z_β(s, ξ)` for `β = (i, j)`, `α = (k, l)` disjoint. -/
theorem z_conj_disj {i j k l : I} (hij : i ≠ j) (hkl : k ≠ l) (hki : k ≠ i) (hkj : k ≠ j)
    (hli : l ≠ i) (hlj : l ≠ j) (s ξ η : R) :
    cj (x k l hkl η) (zElt i j hij s ξ) = zElt i j hij s ξ := by
  refine cj_of_commute ?_
  unfold zElt
  exact ((x_commute_of_ne k l j i hkl hij.symm hlj hki.symm _ _).mul_right
    (x_commute_of_ne k l i j hkl hij hli hkj.symm _ _)).mul_right
    (x_commute_of_ne k l j i hkl hij.symm hlj hki.symm _ _)

#audit_axioms z_conj_disj

/-- **L–S 4.1(2)**, `α = (i, j)`, `β = (j, l)`, `α + β = (i, l)`, `N_{β,α} = -1`. -/
theorem z_conj_obtuse_row {i j l : I} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (s ξ η : R) :
    cj (x i j hij η) (zElt j l hjl s ξ) =
      x i j hij (-(s * ξ * η)) * x i l hil (-(s * η)) * zElt j l hjl s ξ := by
  have hlj := hjl.symm
  unfold zElt
  rw [cj_mul, cj_mul, cj_of_commute (x_commute_of_ne i j l j hij hlj hjl hij.symm _ _),
    cj_x_right hij hjl hil, cj_of_commute (x_commute_of_ne i j l j hij hlj hjl hij.symm _ _)]
  simp only [mul_assoc]
  rw [mv_rev hil hlj hij, show -(-(η * s) * -ξ) = -(s * ξ * η) by ring,
    show -(η * s) = -(s * η) by ring]

#audit_axioms z_conj_obtuse_row

/-- **L–S 4.1(2)**, `α = (i, j)`, `β = (k, i)`, `α + β = (k, j)`, `N_{β,α} = 1`. -/
theorem z_conj_obtuse_col {i j k : I} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (s ξ η : R) :
    cj (x i j hij η) (zElt k i hki s ξ) =
      x i j hij (-(s * ξ * η)) * x k j hkj (s * η) * zElt k i hki s ξ := by
  have hik := hki.symm
  unfold zElt
  rw [cj_mul, cj_mul, cj_of_commute (x_commute_of_ne i j i k hij hik hij.symm hki _ _),
    cj_x_left hki hij hkj, cj_of_commute (x_commute_of_ne i j i k hij hik hij.symm hki _ _)]
  simp only [mul_assoc]
  rw [mv_fwd hik hkj hij, show -ξ * (s * η) = -(s * ξ * η) by ring]

#audit_axioms z_conj_obtuse_col

/-- **L–S 4.1(3)**, `α = (i, j)`, `β = (i, l)`, `α - β = (l, j)`, `N_{β,-α} = -1`. -/
theorem z_conj_acute_row {i j l : I} (hij : i ≠ j) (hil : i ≠ l) (hlj : l ≠ j) (s ξ η : R) :
    cj (x i j hij η) (zElt i l hil s ξ) =
      x i j hij (s * ξ * η) * x l j hlj (-(s * ξ ^ 2 * η)) * zElt i l hil s ξ := by
  have hli := hil.symm
  have cij_lj : ∀ a b : R, Commute (x i j hij a) (x l j hlj b) := fun a b =>
    x_commute_of_ne i j l j hij hlj hlj.symm hij.symm a b
  have cli_lj : ∀ a b : R, Commute (x l i hli a) (x l j hlj b) := fun a b =>
    x_commute_of_ne l i l j hli hlj hil hlj.symm a b
  unfold zElt
  rw [cj_mul, cj_mul, cj_x_left hli hij hlj,
    cj_of_commute (x_commute_of_ne i j i l hij hil hij.symm hli _ _), cj_x_left hli hij hlj]
  simp only [mul_assoc]
  rw [mv_fwd hil hlj hij, mv_fwd hli hij hlj, (cli_lj _ _).left_comm, (cij_lj _ _).left_comm,
    x_add_tail l j hlj (-ξ * (s * (ξ * η))), x_add_tail, (cij_lj _ _).symm.left_comm,
    show -ξ * η + (-ξ * (s * (ξ * η)) + ξ * η) = -(s * ξ ^ 2 * η) by ring,
    show s * (ξ * η) = s * ξ * η by ring]

#audit_axioms z_conj_acute_row

/-- **L–S 4.1(3)**, `α = (i, j)`, `β = (k, j)`, `α - β = (i, k)`, `N_{β,-α} = 1`. -/
theorem z_conj_acute_col {i j k : I} (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j) (s ξ η : R) :
    cj (x i j hij η) (zElt k j hkj s ξ) =
      x i j hij (s * ξ * η) * x i k hik (s * ξ ^ 2 * η) * zElt k j hkj s ξ := by
  have hjk := hkj.symm
  have cjk_ik : ∀ a b : R, Commute (x j k hjk a) (x i k hik b) := fun a b =>
    x_commute_of_ne j k i k hjk hik hik.symm hkj a b
  have cij_ik : ∀ a b : R, Commute (x i j hij a) (x i k hik b) := fun a b =>
    x_commute_of_ne i j i k hij hik hij.symm hik.symm a b
  unfold zElt
  rw [cj_mul, cj_mul, cj_x_right hij hjk hik,
    cj_of_commute (x_commute_of_ne i j k j hij hkj hjk.symm.symm hij.symm _ _),
    cj_x_right hij hjk hik]
  simp only [mul_assoc]
  rw [mv_rev hik hkj hij, mv_rev hij hjk hik, (cjk_ik _ _).left_comm, (cij_ik _ _).left_comm,
    x_add_tail i k hik (-(-(-(η * ξ) * s) * -ξ)), x_add_tail, (cij_ik _ _).symm.left_comm,
    show -(η * -ξ) + (-(-(-(η * ξ) * s) * -ξ) + -(η * ξ)) = s * ξ ^ 2 * η by ring,
    show -(-(η * ξ) * s) = s * ξ * η by ring]

#audit_axioms z_conj_acute_col

end LSCore
end BooneHigmanLinear
end GroupApproximation
