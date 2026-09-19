import GroupApproximation.BooneHigman.Join.DChain

/-!
# The rotations `P(x, y)` and the pentagon identity (lane bh-pal-met-join)

The alphabet is `Fin (n + 2)`, and `t = tl n` is its last letter.  For incomparable `x`, `y`,
`Prot x y = K_x · ℓ(x t, y) · ℓ(x, y)` with `K_x = jPhi x (K0 n)`.  On the boundary:
* it maps `x ↦ x 0` (`Prot_x`);
* it maps `y i ↦ x (i+1)` for `i < t` (`Prot_y`);
* it maps `y t ↦ y` (`Prot_yt`);
* it fixes everything off `x` and `y` (`Prot_fix`).
So `P(x, y)` is the elementary rotation of Thompson's group `F_{n+2}` at two adjacent cones.

* `Prot_conj`: rigid conjugation carries `P(x, y)` to `P(x', y')`.
* `jPhi_Prot`: prefix lifts carry `P(x, y)` to `P(c x, c y)`.
* `mirror` (the pentagon): `P(p, q) = P(p, q 0) · ∏_{m ≤ n} P(q m, q (m+1))`.
  The derivation pushes the letters `ℓ(q m, q (m+1))` to the right by rigid conjugation, then
  telescopes (`telescope_full`, the only use of the split relator).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace GroupApproximation.BooneHigman.Join

open GroupApproximation.BooneHigman.Metabelian.Envelope

variable {n : ℕ}

/-- The last letter. -/
abbrev tl (n : ℕ) : Fin (n + 2) := fc n (n + 1)

theorem tl_succ : fc n (n + 1 + 1) = fc n 0 :=
  Fin.ext (show (n + 1 + 1) % (n + 2) = 0 % (n + 2) by
    rw [Nat.zero_mod]; exact Nat.mod_self (n + 2))

#audit_axioms GroupApproximation.BooneHigman.Join.tl_succ

theorem qinc (q : List (Fin (n + 2))) {i j : ℕ} (hi : i < n + 2) (hj : j < n + 2) (hij : i ≠ j) :
    ¬ q ++ [fc n i] <+: q ++ [fc n j] :=
  dinc_child q (fc_ne hi hj hij)

#audit_axioms GroupApproximation.BooneHigman.Join.qinc

theorem Kx_maps (x : List (Fin (n + 2))) (i : ℕ) :
    MapsCone (jperm (n + 2) (jPhi (n + 2) x (K0 n))) (x ++ [fc n i]) (x ++ [fc n (i + 1)]) :=
  dmc_phi x (K0_maps i)

#audit_axioms GroupApproximation.BooneHigman.Join.Kx_maps

theorem Kx_last (x : List (Fin (n + 2))) :
    MapsCone (jperm (n + 2) (jPhi (n + 2) x (K0 n))) (x ++ [tl n]) (x ++ [fc n 0]) := by
  have h := Kx_maps x (n + 1)
  rw [tl_succ] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Join.Kx_last

/-- `κ(x, y) = K_x ℓ(x t, y)`. -/
noncomputable def kap (x y : List (Fin (n + 2))) : higmanVCCommon_Q (n + 2) :=
  jPhi (n + 2) x (K0 n) * jL (x ++ [tl n]) y

#audit_axioms GroupApproximation.BooneHigman.Join.kap

/-- The rotation `P(x, y) = κ(x, y) ℓ(x, y)`. -/
noncomputable def Prot (x y : List (Fin (n + 2))) : higmanVCCommon_Q (n + 2) :=
  kap x y * jL x y

#audit_axioms GroupApproximation.BooneHigman.Join.Prot

theorem kap_conj {x y x' y' : List (Fin (n + 2))} (h1 : ¬ x <+: y) (h2 : ¬ y <+: x)
    (g : higmanVCCommon_Q (n + 2)) (hx : MapsCone (jperm (n + 2) g) x x')
    (hy : MapsCone (jperm (n + 2) g) y y') : g * kap x y * g⁻¹ = kap x' y' := by
  unfold kap
  have e : g * (jPhi (n + 2) x (K0 n) * jL (x ++ [tl n]) y) * g⁻¹ =
      (g * jPhi (n + 2) x (K0 n) * g⁻¹) * (g * jL (x ++ [tl n]) y * g⁻¹) := by group
  rw [e, rcl_phi (dn2 n) g hx, rcl (dn2 n) g (dinc_append_left h1 h2 _)
    (dinc_append_right h2 h1 _) (hx.append _) hy]

#audit_axioms GroupApproximation.BooneHigman.Join.kap_conj

/-- **Rigid conjugation of a rotation.** -/
theorem Prot_conj {x y x' y' : List (Fin (n + 2))} (h1 : ¬ x <+: y) (h2 : ¬ y <+: x)
    (g : higmanVCCommon_Q (n + 2)) (hx : MapsCone (jperm (n + 2) g) x x')
    (hy : MapsCone (jperm (n + 2) g) y y') : g * Prot x y * g⁻¹ = Prot x' y' := by
  unfold Prot
  have e : g * (kap x y * jL x y) * g⁻¹ = (g * kap x y * g⁻¹) * (g * jL x y * g⁻¹) := by group
  rw [e, kap_conj h1 h2 g hx hy, rcl (dn2 n) g h1 h2 hx hy]

#audit_axioms GroupApproximation.BooneHigman.Join.Prot_conj

theorem jPhi_Prot (c x y : List (Fin (n + 2))) :
    jPhi (n + 2) c (Prot x y) = Prot (c ++ x) (c ++ y) := by
  unfold Prot kap
  rw [map_mul, map_mul, jPhi_append, jPhi_jL, jPhi_jL, List.append_assoc]

#audit_axioms GroupApproximation.BooneHigman.Join.jPhi_Prot

theorem Prot_x {x y : List (Fin (n + 2))} (h1 : ¬ x <+: y) (h2 : ¬ y <+: x) :
    MapsCone (jperm (n + 2) (Prot x y)) x (x ++ [fc n 0]) := by
  unfold Prot kap
  exact dmc_mul (dmc_jL_left h1 h2) (dmc_mul (dmc_jL_right (dinc_append_left h1 h2 _)
    (dinc_append_right h2 h1 _)) (Kx_last x))

#audit_axioms GroupApproximation.BooneHigman.Join.Prot_x

theorem Prot_y {x y : List (Fin (n + 2))} (h1 : ¬ x <+: y) (h2 : ¬ y <+: x) {i : ℕ}
    (hi : i < n + 1) : MapsCone (jperm (n + 2) (Prot x y)) (y ++ [fc n i]) (x ++ [fc n (i + 1)]) := by
  unfold Prot kap
  have hne : fc n i ≠ tl n := fc_ne (by omega) (by omega) (by omega)
  refine dmc_mul ((dmc_jL_right h1 h2).append [fc n i]) (dmc_mul ?_ (Kx_maps x i))
  exact dmc_jL_fix (dinc_append_left h1 h2 _) (dinc_append_right h2 h1 _)
    (dinc_child x hne.symm) (dinc_child x hne) (dinc_append_right h2 h1 _)
    (dinc_append_left h1 h2 _)

#audit_axioms GroupApproximation.BooneHigman.Join.Prot_y

theorem Prot_yt {x y : List (Fin (n + 2))} (h1 : ¬ x <+: y) (h2 : ¬ y <+: x) :
    MapsCone (jperm (n + 2) (Prot x y)) (y ++ [tl n]) y := by
  unfold Prot kap
  exact dmc_mul ((dmc_jL_right h1 h2).append [tl n]) (dmc_mul (dmc_jL_left
    (dinc_append_left h1 h2 _) (dinc_append_right h2 h1 _)) (dmc_phi_fix x _ h1 h2))

#audit_axioms GroupApproximation.BooneHigman.Join.Prot_yt

theorem Prot_fix {x y z : List (Fin (n + 2))} (h1 : ¬ x <+: y) (h2 : ¬ y <+: x)
    (hxz : ¬ x <+: z) (hzx : ¬ z <+: x) (hyz : ¬ y <+: z) (hzy : ¬ z <+: y) :
    MapsCone (jperm (n + 2) (Prot x y)) z z := by
  unfold Prot kap
  exact dmc_mul (dmc_jL_fix h1 h2 hxz hzx hyz hzy) (dmc_mul (dmc_jL_fix
    (dinc_append_left h1 h2 _) (dinc_append_right h2 h1 _) (dinc_append_left hxz hzx _)
    (dinc_append_right hzx hxz _) hyz hzy) (dmc_phi_fix x _ hxz hzx))

#audit_axioms GroupApproximation.BooneHigman.Join.Prot_fix

/-- The second form `P(x, y) = ℓ(x, y) K_y ℓ(y t, x)`. -/
theorem Prot_alt {x y : List (Fin (n + 2))} (h1 : ¬ x <+: y) (h2 : ¬ y <+: x) :
    Prot x y = jL x y * jPhi (n + 2) y (K0 n) * jL (y ++ [tl n]) x := by
  have c1 := rcl (dn2 n) (jL x y) (dinc_append_left h1 h2 [tl n])
    (dinc_append_right h2 h1 [tl n]) ((dmc_jL_left h1 h2).append [tl n]) (dmc_jL_right h1 h2)
  have c2 := rcl_phi (dn2 n) (jL x y) (dmc_jL_right h1 h2) (K0 n)
  unfold Prot kap
  rw [← c1, ← c2, jL_inv]
  all_goals group

#audit_axioms GroupApproximation.BooneHigman.Join.Prot_alt

/-- `Lam p q k = ℓ(p, q0) ℓ(q0, q1) ⋯ ℓ(q(k-1), qk)`. -/
noncomputable def Lam (p q : List (Fin (n + 2))) : ℕ → higmanVCCommon_Q (n + 2)
  | 0 => jL p (q ++ [fc n 0])
  | k + 1 => Lam p q k * jL (q ++ [fc n k]) (q ++ [fc n (k + 1)])

#audit_axioms GroupApproximation.BooneHigman.Join.Lam

theorem Lam_maps {p q : List (Fin (n + 2))} (h1 : ¬ p <+: q) (h2 : ¬ q <+: p) :
    ∀ k, k ≤ n + 1 → MapsCone (jperm (n + 2) (Lam p q k)) (q ++ [fc n k]) p ∧
      ∀ j, k < j → j < n + 2 →
        MapsCone (jperm (n + 2) (Lam p q k)) (q ++ [fc n j]) (q ++ [fc n j])
  | 0, _ => by
    refine ⟨?_, fun j hj hj' => ?_⟩
    · show MapsCone (jperm (n + 2) (jL p (q ++ [fc n 0]))) _ _
      exact dmc_jL_right (dinc_append_right h1 h2 _) (dinc_append_left h2 h1 _)
    · show MapsCone (jperm (n + 2) (jL p (q ++ [fc n 0]))) _ _
      exact dmc_jL_fix (dinc_append_right h1 h2 _) (dinc_append_left h2 h1 _)
        (dinc_append_right h1 h2 _) (dinc_append_left h2 h1 _)
        (qinc q (by omega) hj' (by omega)) (qinc q hj' (by omega) (by omega))
  | k + 1, hk => by
    obtain ⟨ha, hb⟩ := Lam_maps h1 h2 k (by omega)
    have l1 : ¬ q ++ [fc n k] <+: q ++ [fc n (k + 1)] := qinc q (by omega) (by omega) (by omega)
    have l2 : ¬ q ++ [fc n (k + 1)] <+: q ++ [fc n k] := qinc q (by omega) (by omega) (by omega)
    refine ⟨?_, fun j hj hj' => ?_⟩
    · show MapsCone (jperm (n + 2) (Lam p q k * jL (q ++ [fc n k]) (q ++ [fc n (k + 1)]))) _ _
      exact dmc_mul (dmc_jL_right l1 l2) ha
    · show MapsCone (jperm (n + 2) (Lam p q k * jL (q ++ [fc n k]) (q ++ [fc n (k + 1)]))) _ _
      exact dmc_mul (dmc_jL_fix l1 l2 (qinc q (by omega) hj' (by omega))
        (qinc q hj' (by omega) (by omega)) (qinc q (by omega) hj' (by omega))
        (qinc q hj' (by omega) (by omega))) (hb j (by omega) hj')

#audit_axioms GroupApproximation.BooneHigman.Join.Lam_maps

theorem Lam_eq (p q : List (Fin (n + 2))) :
    ∀ k, Lam p q k = jL p (q ++ [fc n 0]) * jPhi (n + 2) q (Rch n k)
  | 0 => by
    show jL p (q ++ [fc n 0]) = jL p (q ++ [fc n 0]) * jPhi (n + 2) q 1
    rw [map_one, mul_one]
  | k + 1 => by
    show Lam p q k * jL (q ++ [fc n k]) (q ++ [fc n (k + 1)]) =
      jL p (q ++ [fc n 0]) * jPhi (n + 2) q (Rch n k * jL [fc n k] [fc n (k + 1)])
    rw [Lam_eq p q k, map_mul, jPhi_jL, mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Join.Lam_eq

theorem mirror_step {p q : List (Fin (n + 2))} (h1 : ¬ p <+: q) (h2 : ¬ q <+: p) :
    ∀ k, k ≤ n + 1 →
      Prot p (q ++ [fc n 0]) *
          ((List.range k).map fun m => Prot (q ++ [fc n m]) (q ++ [fc n (m + 1)])).prod =
        ((List.range (k + 1)).map fun m => kap p (q ++ [fc n m])).prod * Lam p q k
  | 0, _ => by
    show kap p (q ++ [fc n 0]) * jL p (q ++ [fc n 0]) * ([] : List _).prod =
      ([kap p (q ++ [fc n 0])]).prod * jL p (q ++ [fc n 0])
    rw [List.prod_nil, List.prod_singleton, mul_one]
  | k + 1, hk => by
    rw [List.range_succ k, List.map_append, List.prod_append, ← mul_assoc,
      mirror_step h1 h2 k (by omega), List.range_succ (k + 1), List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    obtain ⟨ha, hb⟩ := Lam_maps h1 h2 k (by omega)
    have l1 : ¬ q ++ [fc n k] <+: q ++ [fc n (k + 1)] := qinc q (by omega) (by omega) (by omega)
    have l2 : ¬ q ++ [fc n (k + 1)] <+: q ++ [fc n k] := qinc q (by omega) (by omega) (by omega)
    have hc := kap_conj l1 l2 (Lam p q k) ha (hb (k + 1) (by omega) (by omega))
    rw [← hc]
    show _ * Lam p q k * (kap (q ++ [fc n k]) (q ++ [fc n (k + 1)]) *
        jL (q ++ [fc n k]) (q ++ [fc n (k + 1)])) =
      _ * (Lam p q k * kap (q ++ [fc n k]) (q ++ [fc n (k + 1)]) * (Lam p q k)⁻¹) *
        (Lam p q k * jL (q ++ [fc n k]) (q ++ [fc n (k + 1)]))
    group

#audit_axioms GroupApproximation.BooneHigman.Join.mirror_step

/-- **The pentagon identity**: `P(p, q) = P(p, q 0) · ∏_{m ≤ n} P(q m, q (m+1))`. -/
theorem mirror {p q : List (Fin (n + 2))} (h1 : ¬ p <+: q) (h2 : ¬ q <+: p) :
    Prot p q = Prot p (q ++ [fc n 0]) *
      ((List.range (n + 1)).map fun m => Prot (q ++ [fc n m]) (q ++ [fc n (m + 1)])).prod := by
  rw [mirror_step h1 h2 (n + 1) le_rfl]
  have ht : ((List.range (n + 1 + 1)).map fun m => kap p (q ++ [fc n m])).prod = jL p q :=
    telescope_full h1 h2
  rw [ht, Prot_alt h1 h2, Lam_eq, show Rch n (n + 1) = K0 n from rfl]
  have hc := rcl (dn2 n) (jPhi (n + 2) q (K0 n)) (dinc_append_left h2 h1 [tl n])
    (dinc_append_right h1 h2 [tl n]) (Kx_last q) (dmc_phi_fix q _ h2 h1)
  rw [jL_symmD (dn2 n) (dinc_append_left h2 h1 [fc n 0]) (dinc_append_right h1 h2 [fc n 0])]
    at hc
  rw [← hc]
  group

#audit_axioms GroupApproximation.BooneHigman.Join.mirror

end GroupApproximation.BooneHigman.Join
