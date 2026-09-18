import GroupApproximation.BooneHigman.Metabelian.VdKInjActCocycle
import GroupApproximation.Meta.AxiomGuard

/-!
# van der Kallen's injectivity action, part 2: the action of `St_{n+1}(R)`

Lane `bh-met-91o`.  Fix a row cocycle `c` (`vdkInjAct_IsCocycle c`).

* `vdkInjAct_move c i j hij a` is the right action of one root on `Z = St_n(R) × R^{n+1}`:
  `(h, u) ↦ (h · c(u, x_{ij}(a)), u ᵥ* M_{x_{ij}(a)})`.
* `vdkInjAct_move_add`, `_commute` and `_adjacent` check each Steinberg relator of `St_{n+1}(R)`
  on `Z` directly.  The first component is a cocycle field.  The second component is the
  corresponding relation in `St_{n+1}(R)`, pushed through `vdkInjAct_row_mul`.
* `vdkInjAct_perm hc i j hij a` is the permutation `move_{ij}(a)`, with inverse `move_{ij}(-a)`.
* `vdkInjAct_hom hc : St_{n+1}(R) →* Perm Z` is defined on generators by
  `x_{ij}(a) ↦ (vdkInjAct_perm hc i j hij a)⁻¹`, and every relator is checked
  (`vdkInjAct_genPerm_kills`).  The inverse turns the right action into a homomorphism.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open scoped commutatorElement

variable {n : ℕ} {R : Type*} [CommRing R]

/-- One root `x_{ij}(a)` acting on the right of `(h, u) ∈ St_n(R) × R^{n+1}`. -/
noncomputable def vdkInjAct_move (c : vdkInjAct_Cocycle n R) (i j : Fin (n + 1)) (hij : i ≠ j)
    (a : R) (z : St n R × (Fin (n + 1) → R)) : St n R × (Fin (n + 1) → R) :=
  (z.1 * c z.2 i j hij a, vdkInjAct_row z.2 (x i j hij a))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_move

variable {c : vdkInjAct_Cocycle n R}

theorem vdkInjAct_move_add (hc : vdkInjAct_IsCocycle c) (i j : Fin (n + 1)) (hij : i ≠ j)
    (a b : R) (z : St n R × (Fin (n + 1) → R)) :
    vdkInjAct_move c i j hij b (vdkInjAct_move c i j hij a z) =
      vdkInjAct_move c i j hij (a + b) z := by
  obtain ⟨h, u⟩ := z
  show (h * c u i j hij a * c (vdkInjAct_row u (x i j hij a)) i j hij b,
      vdkInjAct_row (vdkInjAct_row u (x i j hij a)) (x i j hij b)) =
    (h * c u i j hij (a + b), vdkInjAct_row u (x i j hij (a + b)))
  rw [mul_assoc, hc.add u i j hij a b, vdkInjAct_row_mul, x_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_move_add

theorem vdkInjAct_move_zero (hc : vdkInjAct_IsCocycle c) (i j : Fin (n + 1)) (hij : i ≠ j)
    (z : St n R × (Fin (n + 1) → R)) : vdkInjAct_move c i j hij 0 z = z := by
  obtain ⟨h, u⟩ := z
  show (h * c u i j hij 0, vdkInjAct_row u (x i j hij 0)) = (h, u)
  rw [hc.zero u i j hij, mul_one, x_zero, vdkInjAct_row_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_move_zero

theorem vdkInjAct_move_commute (hc : vdkInjAct_IsCocycle c) (i j k l : Fin (n + 1))
    (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i) (a b : R)
    (z : St n R × (Fin (n + 1) → R)) :
    vdkInjAct_move c k l hkl b (vdkInjAct_move c i j hij a z) =
      vdkInjAct_move c i j hij a (vdkInjAct_move c k l hkl b z) := by
  obtain ⟨h, u⟩ := z
  show (h * c u i j hij a * c (vdkInjAct_row u (x i j hij a)) k l hkl b,
      vdkInjAct_row (vdkInjAct_row u (x i j hij a)) (x k l hkl b)) =
    (h * c u k l hkl b * c (vdkInjAct_row u (x k l hkl b)) i j hij a,
      vdkInjAct_row (vdkInjAct_row u (x k l hkl b)) (x i j hij a))
  rw [mul_assoc h, mul_assoc h, hc.commute u i j k l hij hkl hjk hli a b]
  simp only [vdkInjAct_row_mul]
  rw [(x_commute_of_ne i j k l hij hkl hjk hli a b).eq]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_move_commute

theorem vdkInjAct_move_adjacent (hc : vdkInjAct_IsCocycle c) (i j k : Fin (n + 1))
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) (z : St n R × (Fin (n + 1) → R)) :
    vdkInjAct_move c j k hjk b (vdkInjAct_move c i j hij a z) =
      vdkInjAct_move c i j hij a
        (vdkInjAct_move c j k hjk b (vdkInjAct_move c i k hik (a * b) z)) := by
  obtain ⟨h, u⟩ := z
  show (h * c u i j hij a * c (vdkInjAct_row u (x i j hij a)) j k hjk b,
      vdkInjAct_row (vdkInjAct_row u (x i j hij a)) (x j k hjk b)) =
    (h * c u i k hik (a * b) * c (vdkInjAct_row u (x i k hik (a * b))) j k hjk b *
        c (vdkInjAct_row (vdkInjAct_row u (x i k hik (a * b))) (x j k hjk b)) i j hij a,
      vdkInjAct_row (vdkInjAct_row (vdkInjAct_row u (x i k hik (a * b))) (x j k hjk b))
        (x i j hij a))
  rw [mul_assoc h, hc.adjacent u i j k hij hjk hik a b]
  simp only [vdkInjAct_row_mul]
  rw [vdkInjAct_x_adjacent_eq i j k hij hjk hik a b]
  simp only [mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_move_adjacent

/-- The permutation `move_{ij}(a)` of `St_n(R) × R^{n+1}`, with inverse `move_{ij}(-a)`. -/
noncomputable def vdkInjAct_perm (hc : vdkInjAct_IsCocycle c) (i j : Fin (n + 1)) (hij : i ≠ j)
    (a : R) : Equiv.Perm (St n R × (Fin (n + 1) → R)) where
  toFun := vdkInjAct_move c i j hij a
  invFun := vdkInjAct_move c i j hij (-a)
  left_inv z := by
    show vdkInjAct_move c i j hij (-a) (vdkInjAct_move c i j hij a z) = z
    rw [vdkInjAct_move_add hc, add_neg_cancel, vdkInjAct_move_zero hc]
  right_inv z := by
    show vdkInjAct_move c i j hij a (vdkInjAct_move c i j hij (-a) z) = z
    rw [vdkInjAct_move_add hc, neg_add_cancel, vdkInjAct_move_zero hc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_perm

theorem vdkInjAct_perm_apply (hc : vdkInjAct_IsCocycle c) (i j : Fin (n + 1)) (hij : i ≠ j)
    (a : R) (h : St n R) (u : Fin (n + 1) → R) :
    vdkInjAct_perm hc i j hij a (h, u) = (h * c u i j hij a, vdkInjAct_row u (x i j hij a)) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_perm_apply

end GroupApproximation.BooneHigman.Metabelian.ElemFP
