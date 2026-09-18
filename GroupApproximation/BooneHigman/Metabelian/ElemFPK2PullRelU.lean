import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PullRelDefs
import GroupApproximation.Meta.AxiomGuard

/-!
# Steinberg identities for the elements `u_ij(h)`

Lane `bh-met-91g`, `u` module.  All three identities come from relations in `St(M, P)` through
the homomorphism `q`, using the ring identities for `k2PullRel_lift`.

* `k2PullRel_u_add`: `u_ij(a) · u_ij(b) = u_ij(a + b)`.
* `k2PullRel_u_comm`: `u_ij(a)` and `u_kl(b)` commute when `j ≠ k` and `l ≠ i`.
* `k2PullRel_u_adj`: `u_ij(a) · (u_ik(C a(0) · b) · u_jk(b)) =
  u_ik(a b) · u_jk(b) · (u_ij(a) · u_ik(-(a · C b(0))))`.  It comes from `k2PullRel_st_adj`,
  which holds in `St(M, R)` over any ring, and from `k2PullRel_lift_mul`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open scoped commutatorElement

section PullRelStAdj

/-- `⁅a, b⁆ = c` iff `a b = c b a`. -/
theorem k2PullRel_comm_iff {G : Type*} [Group G] (a b c : G) :
    ⁅a, b⁆ = c ↔ a * b = c * b * a := by
  rw [commutatorElement_def]
  constructor
  · rintro rfl
    group
  · intro h
    rw [h]
    group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_comm_iff

variable {I R : Type*} [Fintype I] [DecidableEq I] [Ring R]

/-- A consequence of the Steinberg relations for three distinct indices. -/
theorem k2PullRel_st_adj (i j k : I) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a₁ a₂ a₃ a₄ a₅ : R) (h : a₂ + a₁ * a₃ = a₄ + a₅) :
    x i j hij a₁ * (x i k hik a₂ * x j k hjk a₃) =
      x i k hik a₄ * x j k hjk a₃ * (x i j hij a₁ * x i k hik a₅) := by
  have e₁ : x i j hij a₁ * x i k hik a₂ = x i k hik a₂ * x i j hij a₁ :=
    (x_commute_of_ne i k i j hik hij hik.symm hij.symm a₂ a₁).eq.symm
  have e₂ : x i j hij a₁ * x i k hik a₅ = x i k hik a₅ * x i j hij a₁ :=
    (x_commute_of_ne i j i k hij hik hij.symm hik.symm a₁ a₅).eq
  have e₃ : x j k hjk a₃ * x i k hik a₅ = x i k hik a₅ * x j k hjk a₃ :=
    (x_commute_of_ne j k i k hjk hik hik.symm hjk.symm a₃ a₅).eq
  have hadj : x i j hij a₁ * x j k hjk a₃ = x i k hik (a₁ * a₃) * x j k hjk a₃ * x i j hij a₁ :=
    (k2PullRel_comm_iff _ _ _).mp (x_commutator i j k hij hjk hik a₁ a₃)
  calc x i j hij a₁ * (x i k hik a₂ * x j k hjk a₃)
      = x i j hij a₁ * x i k hik a₂ * x j k hjk a₃ := (mul_assoc _ _ _).symm
    _ = x i k hik a₂ * (x i j hij a₁ * x j k hjk a₃) := by rw [e₁, mul_assoc]
    _ = x i k hik a₂ * (x i k hik (a₁ * a₃) * x j k hjk a₃ * x i j hij a₁) := by rw [hadj]
    _ = x i k hik (a₂ + a₁ * a₃) * x j k hjk a₃ * x i j hij a₁ := by
      rw [← x_mul]
      simp only [mul_assoc]
    _ = x i k hik (a₄ + a₅) * x j k hjk a₃ * x i j hij a₁ := by rw [h]
    _ = x i k hik a₄ * (x i k hik a₅ * x j k hjk a₃) * x i j hij a₁ := by
      rw [← x_mul]
      simp only [mul_assoc]
    _ = x i k hik a₄ * (x j k hjk a₃ * x i k hik a₅) * x i j hij a₁ := by rw [e₃]
    _ = x i k hik a₄ * x j k hjk a₃ * (x i k hik a₅ * x i j hij a₁) := by
      simp only [mul_assoc]
    _ = x i k hik a₄ * x j k hjk a₃ * (x i j hij a₁ * x i k hik a₅) := by rw [e₂]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_st_adj

end PullRelStAdj

section PullRelU

variable {A : Type*} [CommRing A] {s : A} {M : ℕ} {H : Type*} [Group H]
  (q : k2PullRel_ker s M →* H)

theorem k2PullRel_u_add (i j : Fin M) (hij : i ≠ j) (a b : Polynomial (Localization.Away s)) :
    k2PullRel_u q i j hij a * k2PullRel_u q i j hij b = k2PullRel_u q i j hij (a + b) := by
  unfold k2PullRel_u
  rw [← map_mul]
  refine congrArg q (Subtype.ext ?_)
  change x i j hij (k2PullRel_lift s a) * x i j hij (k2PullRel_lift s b) =
    x i j hij (k2PullRel_lift s (a + b))
  rw [x_mul, k2PullRel_lift_add]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_u_add

theorem k2PullRel_u_comm (i j k l : Fin M) (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hli : l ≠ i) (a b : Polynomial (Localization.Away s)) :
    k2PullRel_u q i j hij a * k2PullRel_u q k l hkl b =
      k2PullRel_u q k l hkl b * k2PullRel_u q i j hij a := by
  unfold k2PullRel_u
  rw [← map_mul, ← map_mul]
  refine congrArg q (Subtype.ext ?_)
  change x i j hij (k2PullRel_lift s a) * x k l hkl (k2PullRel_lift s b) =
    x k l hkl (k2PullRel_lift s b) * x i j hij (k2PullRel_lift s a)
  exact (x_commute_of_ne i j k l hij hkl hjk hli _ _).eq

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_u_comm

theorem k2PullRel_u_adj (i j k : Fin M) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : Polynomial (Localization.Away s)) :
    k2PullRel_u q i j hij a *
        (k2PullRel_u q i k hik (Polynomial.C (a.eval 0) * b) * k2PullRel_u q j k hjk b) =
      k2PullRel_u q i k hik (a * b) * k2PullRel_u q j k hjk b *
        (k2PullRel_u q i j hij a * k2PullRel_u q i k hik (-(a * Polynomial.C (b.eval 0)))) := by
  unfold k2PullRel_u
  simp only [← map_mul]
  refine congrArg q (Subtype.ext ?_)
  change x i j hij (k2PullRel_lift s a) *
      (x i k hik (k2PullRel_lift s (Polynomial.C (a.eval 0) * b)) *
        x j k hjk (k2PullRel_lift s b)) =
    x i k hik (k2PullRel_lift s (a * b)) * x j k hjk (k2PullRel_lift s b) *
      (x i j hij (k2PullRel_lift s a) *
        x i k hik (k2PullRel_lift s (-(a * Polynomial.C (b.eval 0)))))
  exact k2PullRel_st_adj i j k hij hjk hik _ _ _ _ _ (k2PullRel_lift_mul s a b)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_u_adj

end PullRelU

end GroupApproximation.BooneHigman.Metabelian.ElemFP
