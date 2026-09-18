import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauEqTwoKnown
import GroupApproximation.Meta.AxiomGuard

/-!
# Two decompositions of a conjugator (lane bh-met-91q)

Let `s := (p, q)` be short and `(s; A → B)` an instance, `A = (x, y)`, `B = (x', y')`.  Write
`ℓ_u := ψ(u)` for a short pair `u` and `τ_C := ψ(C)` for a pair `C`.  Fix a short pair
`a = (a1, a2)` and put `A1 := (a1 a2) A`.

* **Form `aba`** (`higmanVCTauEqTwo_Aba`, `higmanVCTauEqTwo_aba`).  `(a1 a2)` carries `s` to a
  short pair `b`, so `ℓ_a ℓ_s ℓ_a⁻¹ = ℓ_b` is an all-short relator.  With `A2 := (b1 b2) A1`,
  the instance follows from `(a; A → A1)`, `(b; A1 → A2)` and `(a; A2 → B)`.
* **Form `sas`** (`higmanVCTauEqTwo_Sas`, `higmanVCTauEqTwo_sas`).  `(p q)` carries `a` to a
  short pair `c`, so `ℓ_s ℓ_a ℓ_s⁻¹ = ℓ_c` is an all-short relator.  With `A2 := (p q) A1`,
  the instance follows from `(a; A → A1)`, `(s; A1 → A2)` and `(c; A2 → B)`.

The three sub-instances are required to be **known at level `n`**
(`higmanVCTauEqTwo_Known`).  Flexible A of lane bh-met-77m is the form `sas` with the first
and last sub-instances below level `n`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- Group identity of the form `aba`. -/
theorem higmanVCTauEqTwo_groupAba {H : Type*} [Group H] {L S M A A1 A2 B : H}
    (hL : L * L = 1) (hv : L * S * L⁻¹ = M) (e1 : L * A * L⁻¹ = A1)
    (e2 : M * A1 * M⁻¹ = A2) (e3 : L * A2 * L⁻¹ = B) : S * A * S⁻¹ = B := by
  have h := higmanVCTauShort_conj_prod hv e1 e2
  have h' := higmanVCTauShort_flip hL h
  exact h'.symm.trans e3

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqTwo_groupAba

/-- Group identity of the form `sas`. -/
theorem higmanVCTauEqTwo_groupSas {H : Type*} [Group H] {L S C A A1 A2 B : H}
    (hL : L * L = 1) (hv : S * L * S⁻¹ = C) (e1 : L * A * L⁻¹ = A1)
    (e2 : S * A1 * S⁻¹ = A2) (e3 : C * A2 * C⁻¹ = B) : S * A * S⁻¹ = B := by
  have hA := higmanVCTauShort_flip hL e1
  have h := higmanVCTauShort_conj_prod hv e2 e3
  rw [hA] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqTwo_groupSas

/-- **Form `aba`** of `(s; (x, y) → (x', y'))`, with known sub-instances at level `n`. -/
def higmanVCTauEqTwo_Aba (d n : ℕ) (p q x y x' y' : List (Fin d)) : Prop :=
  ∃ (a1 a2 b1 b2 X1 Y1 X2 Y2 : List (Fin d)) (ha : ¬ a1 <+: a2) (ha' : ¬ a2 <+: a1)
    (hb : ¬ b1 <+: b2) (hb' : ¬ b2 <+: b1),
    a1.length ≤ 3 ∧ a2.length ≤ 3 ∧ b1.length ≤ 3 ∧ b2.length ≤ 3 ∧
    MapsCone (coneSwap a1 a2 ha ha') p b1 ∧ MapsCone (coneSwap a1 a2 ha ha') q b2 ∧
    MapsCone (coneSwap a1 a2 ha ha') x X1 ∧ MapsCone (coneSwap a1 a2 ha ha') y Y1 ∧
    MapsCone (coneSwap b1 b2 hb hb') X1 X2 ∧ MapsCone (coneSwap b1 b2 hb hb') Y1 Y2 ∧
    MapsCone (coneSwap a1 a2 ha ha') X2 x' ∧ MapsCone (coneSwap a1 a2 ha ha') Y2 y' ∧
    higmanVCTauEqTwo_Known d n a1 a2 x y X1 Y1 ∧ higmanVCTauEqTwo_Known d n b1 b2 X1 Y1 X2 Y2 ∧
    higmanVCTauEqTwo_Known d n a1 a2 X2 Y2 x' y'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqTwo_Aba

/-- **Form `sas`** of `(s; (x, y) → (x', y'))`, with known sub-instances at level `n`. -/
def higmanVCTauEqTwo_Sas (d n : ℕ) (p q x y x' y' : List (Fin d)) (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) : Prop :=
  ∃ (a1 a2 c1 c2 X1 Y1 X2 Y2 : List (Fin d)) (ha : ¬ a1 <+: a2) (ha' : ¬ a2 <+: a1)
    (hc : ¬ c1 <+: c2) (hc' : ¬ c2 <+: c1),
    a1.length ≤ 3 ∧ a2.length ≤ 3 ∧ c1.length ≤ 3 ∧ c2.length ≤ 3 ∧
    MapsCone (coneSwap p q hpq hqp) a1 c1 ∧ MapsCone (coneSwap p q hpq hqp) a2 c2 ∧
    MapsCone (coneSwap a1 a2 ha ha') x X1 ∧ MapsCone (coneSwap a1 a2 ha ha') y Y1 ∧
    MapsCone (coneSwap p q hpq hqp) X1 X2 ∧ MapsCone (coneSwap p q hpq hqp) Y1 Y2 ∧
    MapsCone (coneSwap c1 c2 hc hc') X2 x' ∧ MapsCone (coneSwap c1 c2 hc hc') Y2 y' ∧
    higmanVCTauEqTwo_Known d n a1 a2 x y X1 Y1 ∧ higmanVCTauEqTwo_Known d n p q X1 Y1 X2 Y2 ∧
    higmanVCTauEqTwo_Known d n c1 c2 X2 Y2 x' y'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqTwo_Sas

/-- **The form `aba` closes the instance.** -/
theorem higmanVCTauEqTwo_aba {d : ℕ} (hd : 1 < d) {n : ℕ}
    (hB : higmanVCTauShort_Below d n) (hS : higmanVCTauShort_Shrink d n)
    {p q x y x' y' : List (Fin d)} (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hp : p.length ≤ 3) (hq : q.length ≤ 3) (hxy : ¬ x <+: y) (hyx : ¬ y <+: x)
    (hxy' : ¬ x' <+: y') (hyx' : ¬ y' <+: x') (h : higmanVCTauEqTwo_Aba d n p q x y x' y') :
    higmanVCTauShort_conjEq d p q x y x' y' := by
  obtain ⟨a1, a2, b1, b2, X1, Y1, X2, Y2, ha, ha', hb, hb', ha1, ha2, hb1, hb2, hap, haq,
    hax, hay, hbx, hby, hax', hay', k1, k2, k3⟩ := h
  have hX1 := higmanVCTauEqTwo_inc hd ha ha' hax hay hxy
  have hY1 := higmanVCTauEqTwo_inc hd ha ha' hay hax hyx
  have hX2 := higmanVCTauEqTwo_inc hd hb hb' hbx hby hX1
  have hY2 := higmanVCTauEqTwo_inc hd hb hb' hby hbx hY1
  have hv : higmanVCTauShort_conjEq d a1 a2 p q b1 b2 :=
    higmanVCTauShort_allShort hd ha ha' ha1 ha2 ⟨hp, hq, hb1, hb2⟩ hap haq hpq hqp hb hb'
  have e1 := higmanVCTauEqTwo_inst_of_known hd hB hS k1 ha ha' ha1 ha2 hax hay hxy hyx hX1
    hY1
  have e2 := higmanVCTauEqTwo_inst_of_known hd hB hS k2 hb hb' hb1 hb2 hbx hby hX1 hY1 hX2
    hY2
  have e3 := higmanVCTauEqTwo_inst_of_known hd hB hS k3 ha ha' ha1 ha2 hax' hay' hX2 hY2
    hxy' hyx'
  unfold higmanVCTauShort_conjEq at hv e1 e2 e3 ⊢
  exact higmanVCTauEqTwo_groupAba (higmanVCTauShort_psi_sq d ha1 ha2) hv e1 e2 e3

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqTwo_aba

/-- **The form `sas` closes the instance.** -/
theorem higmanVCTauEqTwo_sas {d : ℕ} (hd : 1 < d) {n : ℕ}
    (hB : higmanVCTauShort_Below d n) (hS : higmanVCTauShort_Shrink d n)
    {p q x y x' y' : List (Fin d)} (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hp : p.length ≤ 3) (hq : q.length ≤ 3) (hxy : ¬ x <+: y) (hyx : ¬ y <+: x)
    (hxy' : ¬ x' <+: y') (hyx' : ¬ y' <+: x')
    (h : higmanVCTauEqTwo_Sas d n p q x y x' y' hpq hqp) :
    higmanVCTauShort_conjEq d p q x y x' y' := by
  obtain ⟨a1, a2, c1, c2, X1, Y1, X2, Y2, ha, ha', hc, hc', ha1, ha2, hc1, hc2, hsa, hsa',
    hax, hay, hsx, hsy, hcx, hcy, k1, k2, k3⟩ := h
  have hX1 := higmanVCTauEqTwo_inc hd ha ha' hax hay hxy
  have hY1 := higmanVCTauEqTwo_inc hd ha ha' hay hax hyx
  have hX2 := higmanVCTauEqTwo_inc hd hpq hqp hsx hsy hX1
  have hY2 := higmanVCTauEqTwo_inc hd hpq hqp hsy hsx hY1
  have hv : higmanVCTauShort_conjEq d p q a1 a2 c1 c2 :=
    higmanVCTauShort_allShort hd hpq hqp hp hq ⟨ha1, ha2, hc1, hc2⟩ hsa hsa' ha ha' hc hc'
  have e1 := higmanVCTauEqTwo_inst_of_known hd hB hS k1 ha ha' ha1 ha2 hax hay hxy hyx hX1
    hY1
  have e2 := higmanVCTauEqTwo_inst_of_known hd hB hS k2 hpq hqp hp hq hsx hsy hX1 hY1 hX2
    hY2
  have e3 := higmanVCTauEqTwo_inst_of_known hd hB hS k3 hc hc' hc1 hc2 hcx hcy hX2 hY2
    hxy' hyx'
  unfold higmanVCTauShort_conjEq at hv e1 e2 e3 ⊢
  exact higmanVCTauEqTwo_groupSas (higmanVCTauShort_psi_sq d ha1 ha2) hv e1 e2 e3

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqTwo_sas

end GroupApproximation.BooneHigman.Metabelian.Envelope
