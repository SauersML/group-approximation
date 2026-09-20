import GroupApproximation.BooneHigman.Join.ThompsonLift

/-!
# The associativity identity and prefix-closure of the lift of `F` (lane bh-pal-met-join)

Write `ℓ(x, y) = jL x y` in `Q = higmanVCCommon_Q 2`, and `Φ = psi.range` for the lift of
Thompson's `F` (`ThompsonLift`).

* `assoc_of_relators`: in any group with involutions `ℓ(x, y)` satisfying the conjugation and
  split relators,
  `ℓ(000,001) ℓ(001,01) ℓ(00,01) · ℓ(010,011) ℓ(011,1) ℓ(01,1) = ℓ(00,01) ℓ(01,1) ℓ(0,1)`.
  The first factor is `jPhi [0] X0`, the second is `X0 · X1 · X0⁻¹`, and the right side is
  `X0`.  The derivation uses nine conjugations, one split, and two symmetries (`assoc_alg`).
* `jPhi_zero_X0`: hence `jPhi [0] X0 = X0 · X0 · X1⁻¹ · X0⁻¹`, i.e. Thompson's
  `loc₀(x₀) = x₀² x₁⁻¹ x₀⁻¹` holds in `Q`.
* `jPhi_mem_Phi`: every prefix endomorphism `jPhi w` maps `Φ` into `Φ`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace GroupApproximation.BooneHigman.Join

open GroupApproximation.BooneHigman.Metabelian.Envelope
open GroupApproximation.ThompsonOre

/-- The group-theoretic core of the associativity identity. -/
theorem assoc_alg {G : Type*} [Group G] {p a b c a' b' c' e e' f g s h k h' k' : G}
    (hp : ∀ x : G, p * (p * x) = x) (ha : ∀ x : G, a' * (a' * x) = x)
    (hc : ∀ x : G, c' * (c' * x) = x)
    (ea : a = p * a' * p) (eb : b = p * b' * p) (ec : c = p * c' * p) (ee : e = a' * e' * a')
    (ee' : e' = c' * f * c') (eb' : b' = c' * g * c') (es : s = h * k) (eh : h = p * h' * p)
    (ek : k = p * k' * p) (s1 : f = h') (s2 : g = k') :
    a' * e * p * (a * b * c) = p * c * s := by
  subst ea eb ec ee es eh ek
  subst ee' eb'
  subst s1 s2
  simp only [mul_assoc, hp, ha, hc]

#audit_axioms GroupApproximation.BooneHigman.Join.assoc_alg

/-- From `p · a · p⁻¹ = a'` and `p⁻¹ = p`, get `a = p · a' · p`. -/
theorem conj_eq_of {G : Type*} [Group G] {p a a' : G} (hpinv : p⁻¹ = p)
    (h : p * a * p⁻¹ = a') : a = p * a' * p := by
  have e : a = p⁻¹ * (p * a * p⁻¹) * p := by group
  rw [h, hpinv] at e
  exact e

#audit_axioms GroupApproximation.BooneHigman.Join.conj_eq_of

/-- **The associativity identity from the relator families.** -/
theorem assoc_of_relators {G : Type*} [Group G] (ℓ : List (Fin 2) → List (Fin 2) → G)
    (hsq : ∀ x y, ℓ x y * ℓ x y = 1)
    (hconj : ∀ {p q x y x' y' : List (Fin 2)} (hpq : ¬ p <+: q) (hqp : ¬ q <+: p),
      MapsCone (coneSwap p q hpq hqp) x x' → MapsCone (coneSwap p q hpq hqp) y y' →
      ¬ x <+: y → ¬ y <+: x → ¬ x' <+: y' → ¬ y' <+: x' →
      ℓ p q * ℓ x y * (ℓ p q)⁻¹ = ℓ x' y')
    (hsplit : ∀ {x y : List (Fin 2)}, ¬ x <+: y → ¬ y <+: x →
      ℓ x y = ℓ (x ++ [0]) (y ++ [0]) * ℓ (x ++ [1]) (y ++ [1])) :
    ℓ [0, 0, 0] [0, 0, 1] * ℓ [0, 0, 1] [0, 1] * ℓ [0, 0] [0, 1] *
        (ℓ [0, 1, 0] [0, 1, 1] * ℓ [0, 1, 1] [1] * ℓ [0, 1] [1]) =
      ℓ [0, 0] [0, 1] * ℓ [0, 1] [1] * ℓ [0] [1] := by
  have hinv : ∀ x y, (ℓ x y)⁻¹ = ℓ x y := fun x y => inv_eq_of_mul_eq_one_right (hsq x y)
  have hinvol : ∀ x y (z : G), ℓ x y * (ℓ x y * z) = z := fun x y z => by
    rw [← mul_assoc, hsq, one_mul]
  have hsymm : ∀ {x y : List (Fin 2)}, ¬ x <+: y → ¬ y <+: x → ℓ x y = ℓ y x := by
    intro x y h1 h2
    have h := hconj h1 h2 (mapsCone_coneSwap_left h1 h2) (mapsCone_coneSwap_right h1 h2)
      h1 h2 h2 h1
    rw [hinv, hsq, one_mul] at h
    exact h
  -- `p = (00 01)`: the conjugations of `(010, 011)`, `(011, 1)`, `(01, 1)`, `(00, 10)`, `(01, 11)`.
  have hp1 : ¬ ([0, 0] : List (Fin 2)) <+: [0, 1] := by decide
  have hp2 : ¬ ([0, 1] : List (Fin 2)) <+: [0, 0] := by decide
  have c1 : ℓ [0, 0] [0, 1] * ℓ [0, 1, 0] [0, 1, 1] * (ℓ [0, 0] [0, 1])⁻¹ = ℓ [0, 0, 0] [0, 0, 1] :=
    hconj hp1 hp2 ((mapsCone_coneSwap_right hp1 hp2).append [0])
      ((mapsCone_coneSwap_right hp1 hp2).append [1]) (by decide) (by decide) (by decide)
      (by decide)
  have c2 : ℓ [0, 0] [0, 1] * ℓ [0, 1, 1] [1] * (ℓ [0, 0] [0, 1])⁻¹ = ℓ [0, 0, 1] [1] :=
    hconj hp1 hp2 ((mapsCone_coneSwap_right hp1 hp2).append [1])
      (mapsCone_coneSwap_fix (x := [1]) hp1 hp2 (by decide) (by decide) (by decide) (by decide))
      (by decide) (by decide) (by decide) (by decide)
  have c3 : ℓ [0, 0] [0, 1] * ℓ [0, 1] [1] * (ℓ [0, 0] [0, 1])⁻¹ = ℓ [0, 0] [1] :=
    hconj hp1 hp2 (mapsCone_coneSwap_right hp1 hp2)
      (mapsCone_coneSwap_fix (x := [1]) hp1 hp2 (by decide) (by decide) (by decide) (by decide))
      (by decide) (by decide) (by decide) (by decide)
  have c8 : ℓ [0, 0] [0, 1] * ℓ [0, 0] [1, 0] * (ℓ [0, 0] [0, 1])⁻¹ = ℓ [0, 1] [1, 0] :=
    hconj hp1 hp2 (mapsCone_coneSwap_left hp1 hp2)
      (mapsCone_coneSwap_fix (x := [1, 0]) hp1 hp2 (by decide) (by decide) (by decide)
        (by decide))
      (by decide) (by decide) (by decide) (by decide)
  have c9 : ℓ [0, 0] [0, 1] * ℓ [0, 1] [1, 1] * (ℓ [0, 0] [0, 1])⁻¹ = ℓ [0, 0] [1, 1] :=
    hconj hp1 hp2 (mapsCone_coneSwap_right hp1 hp2)
      (mapsCone_coneSwap_fix (x := [1, 1]) hp1 hp2 (by decide) (by decide) (by decide)
        (by decide))
      (by decide) (by decide) (by decide) (by decide)
  -- `a' = (000 001)`: the conjugation of `(001, 01)`.
  have ha1 : ¬ ([0, 0, 0] : List (Fin 2)) <+: [0, 0, 1] := by decide
  have ha2 : ¬ ([0, 0, 1] : List (Fin 2)) <+: [0, 0, 0] := by decide
  have c4 : ℓ [0, 0, 0] [0, 0, 1] * ℓ [0, 0, 1] [0, 1] * (ℓ [0, 0, 0] [0, 0, 1])⁻¹ =
      ℓ [0, 0, 0] [0, 1] :=
    hconj ha1 ha2 (mapsCone_coneSwap_right ha1 ha2)
      (mapsCone_coneSwap_fix (x := [0, 1]) ha1 ha2 (by decide) (by decide) (by decide)
        (by decide))
      (by decide) (by decide) (by decide) (by decide)
  -- `c' = (00 1)`: the conjugations of `(000, 01)` and `(001, 1)`.
  have hc1 : ¬ ([0, 0] : List (Fin 2)) <+: [1] := by decide
  have hc2 : ¬ ([1] : List (Fin 2)) <+: [0, 0] := by decide
  have c5 : ℓ [0, 0] [1] * ℓ [0, 0, 0] [0, 1] * (ℓ [0, 0] [1])⁻¹ = ℓ [1, 0] [0, 1] :=
    hconj hc1 hc2 ((mapsCone_coneSwap_left hc1 hc2).append [0])
      (mapsCone_coneSwap_fix (x := [0, 1]) hc1 hc2 (by decide) (by decide) (by decide)
        (by decide))
      (by decide) (by decide) (by decide) (by decide)
  have c6 : ℓ [0, 0] [1] * ℓ [0, 0, 1] [1] * (ℓ [0, 0] [1])⁻¹ = ℓ [1, 1] [0, 0] :=
    hconj hc1 hc2 ((mapsCone_coneSwap_left hc1 hc2).append [1])
      (mapsCone_coneSwap_right hc1 hc2) (by decide) (by decide) (by decide) (by decide)
  have c7 : ℓ [0] [1] = ℓ [0, 0] [1, 0] * ℓ [0, 1] [1, 1] :=
    hsplit (x := [0]) (y := [1]) (by decide) (by decide)
  have s1 : ℓ [1, 0] [0, 1] = ℓ [0, 1] [1, 0] :=
    hsymm (x := [1, 0]) (y := [0, 1]) (by decide) (by decide)
  have s2 : ℓ [1, 1] [0, 0] = ℓ [0, 0] [1, 1] :=
    hsymm (x := [1, 1]) (y := [0, 0]) (by decide) (by decide)
  exact assoc_alg (hinvol _ _) (hinvol _ _) (hinvol _ _)
    (conj_eq_of (hinv _ _) c1) (conj_eq_of (hinv _ _) c2) (conj_eq_of (hinv _ _) c3)
    (conj_eq_of (hinv _ _) c4) (conj_eq_of (hinv _ _) c5) (conj_eq_of (hinv _ _) c6) c7
    (conj_eq_of (hinv _ _) c8) (conj_eq_of (hinv _ _) c9) s1 s2

#audit_axioms GroupApproximation.BooneHigman.Join.assoc_of_relators

/-- The conjugation relator in `Q`. -/
theorem jL_conj {d : ℕ} {p q x y x' y' : List (Fin d)} (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x) (hxy' : ¬ x' <+: y') (hyx' : ¬ y' <+: x') :
    jL p q * jL x y * (jL p q)⁻¹ = jL x' y' := by
  have h := higmanVCCommon_mk_rel (higmanVCCommon_conj_mem hpq hqp hmx hmy hxy hyx hxy' hyx')
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h
  exact mul_inv_eq_one.mp h

#audit_axioms GroupApproximation.BooneHigman.Join.jL_conj

/-- The split relator in `Q`, for `d = 2`. -/
theorem jL_split {x y : List (Fin 2)} (h1 : ¬ x <+: y) (h2 : ¬ y <+: x) :
    jL x y = jL (x ++ [0]) (y ++ [0]) * jL (x ++ [1]) (y ++ [1]) := by
  unfold jL
  rw [higmanVCCommon_mk_split h1 h2, higmanVC_splitAll]
  have hr : List.finRange 2 = [0, 1] := by decide
  rw [hr]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, map_mul]

#audit_axioms GroupApproximation.BooneHigman.Join.jL_split

theorem jPhi_zero_X0_letters :
    jPhi 2 [0] X0 = jL [0, 0, 0] [0, 0, 1] * jL [0, 0, 1] [0, 1] * jL [0, 0] [0, 1] := by
  unfold X0
  rw [map_mul, map_mul, jPhi_jL, jPhi_jL, jPhi_jL]
  all_goals rfl

#audit_axioms GroupApproximation.BooneHigman.Join.jPhi_zero_X0_letters

theorem Y_one_letters :
    Y 1 = jL [1, 0, 0] [1, 0, 1] * jL [1, 0, 1] [1, 1] * jL [1, 0] [1, 1] := by
  show jPhi 2 [1] X0 = _
  unfold X0
  rw [map_mul, map_mul, jPhi_jL, jPhi_jL, jPhi_jL]
  all_goals rfl

#audit_axioms GroupApproximation.BooneHigman.Join.Y_one_letters

theorem conj_X0_Y_one :
    X0 * Y 1 * X0⁻¹ = jL [0, 1, 0] [0, 1, 1] * jL [0, 1, 1] [1] * jL [0, 1] [1] := by
  rw [Y_one_letters]
  have m100 : MapsCone (jperm 2 X0) [1, 0, 0] [0, 1, 0] := mapsCone_X0_one_zero.append [0]
  have m101 : MapsCone (jperm 2 X0) [1, 0, 1] [0, 1, 1] := mapsCone_X0_one_zero.append [1]
  have e : ∀ u v w : higmanVCCommon_Q 2,
      X0 * (u * v * w) * X0⁻¹ = (X0 * u * X0⁻¹) * (X0 * v * X0⁻¹) * (X0 * w * X0⁻¹) :=
    fun u v w => by group
  rw [e, rcl jd2 X0 (by decide) (by decide) m100 m101,
    rcl jd2 X0 (by decide) (by decide) m101 mapsCone_X0_one_one,
    rcl jd2 X0 (by decide) (by decide) mapsCone_X0_one_zero mapsCone_X0_one_one]

#audit_axioms GroupApproximation.BooneHigman.Join.conj_X0_Y_one

/-- **`loc₀(x₀) = x₀² x₁⁻¹ x₀⁻¹` in `Q`.** -/
theorem jPhi_zero_X0 : jPhi 2 [0] X0 = X0 * X0 * (Y 1)⁻¹ * X0⁻¹ := by
  have h : jPhi 2 [0] X0 * (X0 * Y 1 * X0⁻¹) = X0 := by
    rw [jPhi_zero_X0_letters, conj_X0_Y_one]
    exact assoc_of_relators jL jL_sq jL_conj jL_split
  calc jPhi 2 [0] X0 = jPhi 2 [0] X0 * (X0 * Y 1 * X0⁻¹) * (X0 * Y 1 * X0⁻¹)⁻¹ := by group
    _ = X0 * X0 * (Y 1)⁻¹ * X0⁻¹ := by rw [h]; group

#audit_axioms GroupApproximation.BooneHigman.Join.jPhi_zero_X0

/-- The lift of `F`: the range of `psi`. -/
noncomputable def Phi : Subgroup (higmanVCCommon_Q 2) := psi.range

#audit_axioms GroupApproximation.BooneHigman.Join.Phi

theorem X0_mem_Phi : X0 ∈ Phi := ⟨x0, psi_x0⟩

#audit_axioms GroupApproximation.BooneHigman.Join.X0_mem_Phi

theorem Y_mem_Phi (n : ℕ) : Y n ∈ Phi := ⟨xn n, psi_xn n⟩

#audit_axioms GroupApproximation.BooneHigman.Join.Y_mem_Phi

theorem jPhi_one_mem_Phi {q : higmanVCCommon_Q 2} (hq : q ∈ Phi) : jPhi 2 [1] q ∈ Phi := by
  obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hq
  exact ⟨shift g, psi_shift g⟩

#audit_axioms GroupApproximation.BooneHigman.Join.jPhi_one_mem_Phi

theorem jPhi_zero_X0_mem : jPhi 2 [0] X0 ∈ Phi := by
  rw [jPhi_zero_X0]
  exact Phi.mul_mem (Phi.mul_mem (Phi.mul_mem X0_mem_Phi X0_mem_Phi)
    (Phi.inv_mem (Y_mem_Phi 1))) (Phi.inv_mem X0_mem_Phi)

#audit_axioms GroupApproximation.BooneHigman.Join.jPhi_zero_X0_mem

theorem jPhi_zero_Y_one_mem : jPhi 2 [0] (Y 1) ∈ Phi := by
  have h1 : jPhi 2 [0] (Y 1) = jPhi 2 [0, 1] X0 := by
    show jPhi 2 [0] (jPhi 2 [1] X0) = _
    rw [jPhi_append]
    all_goals rfl
  have h2 : X0 * jPhi 2 [1, 0] X0 * X0⁻¹ = jPhi 2 [0, 1] X0 :=
    rcl_phi jd2 X0 mapsCone_X0_one_zero X0
  have h3 : jPhi 2 [1, 0] X0 = jPhi 2 [1] (jPhi 2 [0] X0) := by
    rw [jPhi_append]
    all_goals rfl
  rw [h1, ← h2, h3]
  exact Phi.mul_mem (Phi.mul_mem X0_mem_Phi (jPhi_one_mem_Phi jPhi_zero_X0_mem))
    (Phi.inv_mem X0_mem_Phi)

#audit_axioms GroupApproximation.BooneHigman.Join.jPhi_zero_Y_one_mem

theorem jPhi_zero_mem_Phi {q : higmanVCCommon_Q 2} (hq : q ∈ Phi) : jPhi 2 [0] q ∈ Phi := by
  obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hq
  have hK : Subgroup.closure (Set.range (PresentedGroup.of (rels := thompsonRels))) ≤
      Phi.comap ((jPhi 2 [0]).comp psi) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    show jPhi 2 [0] (psi (PresentedGroup.of i)) ∈ Phi
    rw [← xn_of, psi_xn]
    rcases i with ⟨_ | _ | n, hn⟩
    · show jPhi 2 [0] (Y 0) ∈ Phi
      rw [Y_zero]
      exact jPhi_zero_X0_mem
    · show jPhi 2 [0] (Y 1) ∈ Phi
      exact jPhi_zero_Y_one_mem
    · omega
  rw [PresentedGroup.closure_range_of] at hK
  exact hK (Subgroup.mem_top g)

#audit_axioms GroupApproximation.BooneHigman.Join.jPhi_zero_mem_Phi

theorem jPhi_nil (q : higmanVCCommon_Q 2) : jPhi 2 [] q = q := by
  exact jPhi_nil' q

#audit_axioms GroupApproximation.BooneHigman.Join.jPhi_nil

/-- **Every prefix endomorphism preserves the lift of `F`.** -/
theorem jPhi_mem_Phi (w : List (Fin 2)) {q : higmanVCCommon_Q 2} (hq : q ∈ Phi) :
    jPhi 2 w q ∈ Phi := by
  induction w with
  | nil => rwa [jPhi_nil]
  | cons a w ih =>
    have e : jPhi 2 (a :: w) q = jPhi 2 [a] (jPhi 2 w q) := by
      rw [jPhi_append]
      all_goals rfl
    rw [e]
    rcases a with ⟨_ | _ | n, hn⟩
    · exact jPhi_zero_mem_Phi ih
    · exact jPhi_one_mem_Phi ih
    · omega

#audit_axioms GroupApproximation.BooneHigman.Join.jPhi_mem_Phi

end GroupApproximation.BooneHigman.Join
