import GroupApproximation.BooneHigman.V.ConeSwap
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Tactic.Group

/-!
# A Thompson-`F` calibration identity for the all-swaps presentation of `V_2`
(lane bh-pal-met-join)

`research/higman-v-step-b-core-local-conjugation-and-f-obstruction.md` (Claim C) gives an
explicit instance of the Step-B core (`HigmanVCStepBCoreStatement`) with
`h = (0, 10)` and `P = (0, 1000)`.  No antichain, refinement or cone-local balanced
conjugation puts `h * P` into a single antichain subgroup, and `E (h * P)` has infinite order.
The identity it needs is
`(0, 10) (0, 1000) = (00, 10) (00, 1000) (01, 101) (01, 1001)`.

This file derives that identity from the relator families alone.  The statement holds in ANY
group `G` with a map `ℓ` from pairs of binary words that satisfies:
* the involution relators;
* the conjugation relators, with the `MapsCone` side conditions of `higmanVC_rels`;
* the split relators.

So it needs no Higman input and no build of the metabelian chain.  The derivation uses seven
relator steps:
1. conjugate `(0, 1000)` by `(0, 10)`, giving `(10, 000)`;
2. conjugate `(10, 000)` by `(00, 10)`, giving `(00, 100)`;
3. split `(0, 10)` and `(00, 10)`;
4. conjugate `(000, 100)` and `(001, 101)` by `(00, 100)`;
5. conjugate `(1001, 101)` by `(01, 101)`;
6. use symmetry twice to finish.

`qLetter_calibration` (`Join/HigmanVCalibration.lean`) instantiates it in
`higmanVCCommon_Q 2`.

**Scope.**  This is one instance, not the Step-B core.  It shows that the infinite-order
configurations of the core are reachable by short conjugation-first rewriting.  It is a
model test for any general proof.
-/

namespace GroupApproximation.BooneHigman.Join

/-- Closes the concrete prefix-incomparability side goals of this file. -/
macro "join_pfx" : tactic => `(tactic| first | decide | simp)

/-- A cone swap fixes, by the identity prefix substitution, every word that is incomparable
with both of its words. -/
theorem mapsCone_coneSwap_fix {X : Type*} {p q x : List X} (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hpx : ¬ p <+: x) (hxp : ¬ x <+: p) (hqx : ¬ q <+: x) (hxq : ¬ x <+: q) :
    MapsCone (coneSwap p q hpq hqp) x x := by
  intro y
  rw [coneSwap_apply]
  exact coneSwapFun_of_not
    (fun h => Set.disjoint_left.mp (disjoint_cone hpx hxp) h (prepend_mem_cone x y))
    (fun h => Set.disjoint_left.mp (disjoint_cone hqx hxq) h (prepend_mem_cone x y))

#audit_axioms GroupApproximation.BooneHigman.Join.mapsCone_coneSwap_fix

/-- The group-theoretic core of the derivation. -/
theorem calib_alg {G : Type*} [Group G] {a b e g k m n : G}
    (he : e⁻¹ = e) (hg : g⁻¹ = g) (hk : k⁻¹ = k) (hg2 : g * g = 1) (hk2 : k * k = 1)
    (s2 : e * (a * b * a⁻¹) * e⁻¹ = g) (s3 : a = g * k) (s4 : m * n = e) :
    a * b = e * (g * m * g⁻¹) * k * (k * (g * n * g⁻¹) * k⁻¹) := by
  have hb : b = a⁻¹ * (e⁻¹ * g * e) * a := by
    rw [← s2]
    group
  subst hb
  subst s3
  have hkk : ∀ x : G, k * (k * x) = x := fun x => by rw [← mul_assoc, hk2, one_mul]
  have hgg : ∀ x : G, g * (g * x) = x := fun x => by rw [← mul_assoc, hg2, one_mul]
  have hmn : ∀ x : G, m * (n * x) = e * x := fun x => by rw [← mul_assoc, s4]
  simp only [mul_inv_rev, he, hg, hk, mul_assoc, hkk, hgg, hmn]

#audit_axioms GroupApproximation.BooneHigman.Join.calib_alg

/-- **The calibration identity from the relator families.** -/
theorem calib_of_relators {G : Type*} [Group G] (ℓ : List (Fin 2) → List (Fin 2) → G)
    (hsq : ∀ x y, ℓ x y * ℓ x y = 1)
    (hconj : ∀ {p q x y x' y' : List (Fin 2)} (hpq : ¬ p <+: q) (hqp : ¬ q <+: p),
      MapsCone (coneSwap p q hpq hqp) x x' → MapsCone (coneSwap p q hpq hqp) y y' →
      ¬ x <+: y → ¬ y <+: x → ¬ x' <+: y' → ¬ y' <+: x' →
      ℓ p q * ℓ x y * (ℓ p q)⁻¹ = ℓ x' y')
    (hsplit : ∀ {x y : List (Fin 2)}, ¬ x <+: y → ¬ y <+: x →
      ℓ x y = ℓ (x ++ [0]) (y ++ [0]) * ℓ (x ++ [1]) (y ++ [1])) :
    ℓ [0] [1, 0] * ℓ [0] [1, 0, 0, 0] =
      ℓ [0, 0] [1, 0] * ℓ [0, 0] [1, 0, 0, 0] * ℓ [0, 1] [1, 0, 1] *
        ℓ [0, 1] [1, 0, 0, 1] := by
  have hinv : ∀ x y, (ℓ x y)⁻¹ = ℓ x y := fun x y => inv_eq_of_mul_eq_one_right (hsq x y)
  have hsymm : ∀ {x y : List (Fin 2)}, ¬ x <+: y → ¬ y <+: x → ℓ x y = ℓ y x := by
    intro x y h1 h2
    have h := hconj h1 h2 (mapsCone_coneSwap_left h1 h2) (mapsCone_coneSwap_right h1 h2)
      h1 h2 h2 h1
    rw [hinv, hsq, one_mul] at h
    exact h
  -- Step 1: `(0, 10)` conjugates `(0, 1000)` to `(10, 000)`.
  have hpq1 : ¬ ([0] : List (Fin 2)) <+: [1, 0] := by join_pfx
  have hqp1 : ¬ ([1, 0] : List (Fin 2)) <+: [0] := by join_pfx
  have c1 : ℓ [0] [1, 0] * ℓ [0] [1, 0, 0, 0] * (ℓ [0] [1, 0])⁻¹ = ℓ [1, 0] [0, 0, 0] :=
    hconj hpq1 hqp1 (mapsCone_coneSwap_left hpq1 hqp1)
      ((mapsCone_coneSwap_right hpq1 hqp1).append [0, 0])
      (by join_pfx) (by join_pfx) (by join_pfx) (by join_pfx)
  -- Step 2: `(00, 10)` conjugates `(10, 000)` to `(00, 100)`.
  have hpq2 : ¬ ([0, 0] : List (Fin 2)) <+: [1, 0] := by join_pfx
  have hqp2 : ¬ ([1, 0] : List (Fin 2)) <+: [0, 0] := by join_pfx
  have c2 : ℓ [0, 0] [1, 0] * ℓ [1, 0] [0, 0, 0] * (ℓ [0, 0] [1, 0])⁻¹ =
      ℓ [0, 0] [1, 0, 0] :=
    hconj hpq2 hqp2 (mapsCone_coneSwap_right hpq2 hqp2)
      ((mapsCone_coneSwap_left hpq2 hqp2).append [0])
      (by join_pfx) (by join_pfx) (by join_pfx) (by join_pfx)
  have s2 : ℓ [0, 0] [1, 0] * (ℓ [0] [1, 0] * ℓ [0] [1, 0, 0, 0] * (ℓ [0] [1, 0])⁻¹) *
      (ℓ [0, 0] [1, 0])⁻¹ = ℓ [0, 0] [1, 0, 0] := by
    rw [c1]
    exact c2
  -- Step 3: the two splits.
  have s3 : ℓ [0] [1, 0] = ℓ [0, 0] [1, 0, 0] * ℓ [0, 1] [1, 0, 1] :=
    hsplit (x := [0]) (y := [1, 0]) (by join_pfx) (by join_pfx)
  have s4 : ℓ [0, 0, 0] [1, 0, 0] * ℓ [0, 0, 1] [1, 0, 1] = ℓ [0, 0] [1, 0] :=
    (hsplit (x := [0, 0]) (y := [1, 0]) (by join_pfx) (by join_pfx)).symm
  -- Step 4: `(00, 100)` conjugates `(000, 100)` and `(001, 101)`.
  have hpq3 : ¬ ([0, 0] : List (Fin 2)) <+: [1, 0, 0] := by join_pfx
  have hqp3 : ¬ ([1, 0, 0] : List (Fin 2)) <+: [0, 0] := by join_pfx
  have c5 : ℓ [0, 0] [1, 0, 0] * ℓ [0, 0, 0] [1, 0, 0] * (ℓ [0, 0] [1, 0, 0])⁻¹ =
      ℓ [1, 0, 0, 0] [0, 0] :=
    hconj hpq3 hqp3 ((mapsCone_coneSwap_left hpq3 hqp3).append [0])
      (mapsCone_coneSwap_right hpq3 hqp3)
      (by join_pfx) (by join_pfx) (by join_pfx) (by join_pfx)
  have c6 : ℓ [0, 0] [1, 0, 0] * ℓ [0, 0, 1] [1, 0, 1] * (ℓ [0, 0] [1, 0, 0])⁻¹ =
      ℓ [1, 0, 0, 1] [1, 0, 1] :=
    hconj hpq3 hqp3 ((mapsCone_coneSwap_left hpq3 hqp3).append [1])
      (mapsCone_coneSwap_fix (x := [1, 0, 1]) hpq3 hqp3
        (by join_pfx) (by join_pfx) (by join_pfx) (by join_pfx))
      (by join_pfx) (by join_pfx) (by join_pfx) (by join_pfx)
  -- Step 5: `(01, 101)` conjugates `(1001, 101)` to `(1001, 01)`.
  have hpq4 : ¬ ([0, 1] : List (Fin 2)) <+: [1, 0, 1] := by join_pfx
  have hqp4 : ¬ ([1, 0, 1] : List (Fin 2)) <+: [0, 1] := by join_pfx
  have c7 : ℓ [0, 1] [1, 0, 1] * ℓ [1, 0, 0, 1] [1, 0, 1] * (ℓ [0, 1] [1, 0, 1])⁻¹ =
      ℓ [1, 0, 0, 1] [0, 1] :=
    hconj hpq4 hqp4
      (mapsCone_coneSwap_fix (x := [1, 0, 0, 1]) hpq4 hqp4
        (by join_pfx) (by join_pfx) (by join_pfx) (by join_pfx))
      (mapsCone_coneSwap_right hpq4 hqp4)
      (by join_pfx) (by join_pfx) (by join_pfx) (by join_pfx)
  -- Step 6: symmetry.
  have sr : ℓ [1, 0, 0, 0] [0, 0] = ℓ [0, 0] [1, 0, 0, 0] :=
    hsymm (x := [1, 0, 0, 0]) (y := [0, 0]) (by join_pfx) (by join_pfx)
  have st : ℓ [1, 0, 0, 1] [0, 1] = ℓ [0, 1] [1, 0, 0, 1] :=
    hsymm (x := [1, 0, 0, 1]) (y := [0, 1]) (by join_pfx) (by join_pfx)
  rw [← sr, ← st, ← c7, ← c6, ← c5]
  exact calib_alg (hinv _ _) (hinv _ _) (hinv _ _) (hsq _ _) (hsq _ _) s2 s3 s4

#audit_axioms GroupApproximation.BooneHigman.Join.calib_of_relators

end GroupApproximation.BooneHigman.Join
