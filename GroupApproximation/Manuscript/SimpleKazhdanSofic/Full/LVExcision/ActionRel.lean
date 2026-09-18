import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVExcision.Action

/-!
# The generator automorphisms satisfy the Steinberg relations (lane LVExcision)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.  Stable `K₂`
excision (Suslin–Wodzicki, Ann. Math. 136 (1992), Thm A; Keune, J. Algebra 54 (1978); ABC
thm:skewyao, `yaoseq6.tex` l.558-640).

* `act_comm`: the actions of `x_{ij}(a)` and `x_{kl}(b)` commute for `j ≠ k`, `l ≠ i`;
* `act_adj`: the commutator of the actions of `x_{ij}(a)` and `x_{jk}(b)` is the action of
  `x_{ik}(ab)`.  On `small e` both sides are conjugations, by
  `⁅x_{ij}(phi E a), x_{jk}(phi E b)⁆ = x_{ik}(phi E a · phi E b)` and by `x_{ik}(phi E (ab))`;
  the quotient `x_{ik}(phi E a · phi E b - phi E (ab))` commutes with `small e` by Lemma C
  once `E` dominates `e`, `b e` and `e a` (`phi_mul_phi_sub_mul`, `mul_phi_mul_phi_sub`).
-/

namespace GroupApproximation.Full.LVExcision

open SteinbergGroup
open scoped commutatorElement

variable {R : Type*} [Ring R] {I : TwoSidedIdeal R} {A : Subring R} {N : ℕ}

/-- `(phi E a phi E b - phi E (ab)) f = 0` when `E` dominates `e` and is a left unit for `b e`,
and `e f = f`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem phi_mul_phi_sub_mul {e E f : R} (a b : R) (hEe : Dom E e) (hEb : E * (b * e) = b * e)
    (hef : e * f = f) : (phi E a * phi E b - phi E (a * b)) * f = 0 := by
  have hEf : E * f = f := hEe.left hef
  have hbf : E * (b * f) = b * f := by
    calc E * (b * f) = E * (b * e) * f := by rw [mul_assoc E, mul_assoc b, hef]
      _ = b * f := by rw [hEb, mul_assoc, hef]
  rw [sub_mul, mul_assoc, phi_mul_of hEf b, phi_mul_of hbf a, phi_mul_of hEf (a * b), mul_assoc,
    sub_self]

/-- `β (phi E a phi E b - phi E (ab)) = 0` when `E` dominates `e` and is a right unit for `e a`,
and `β e = β`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem mul_phi_mul_phi_sub {e E β : R} (a b : R) (hEe : Dom E e) (hEa : e * a * E = e * a)
    (hβe : β * e = β) : β * (phi E a * phi E b - phi E (a * b)) = 0 := by
  have hβE : β * E = β := hEe.right hβe
  have hβa : β * a * E = β * a := by
    calc β * a * E = β * e * a * E := by rw [hβe]
      _ = β * (e * a * E) := by simp only [mul_assoc]
      _ = β * a := by rw [hEa, ← mul_assoc, hβe]
  rw [mul_sub, ← mul_assoc, mul_phi_of hβE a, mul_phi_of hβa b, mul_phi_of hβE (a * b),
    ← mul_assoc, sub_self]

/-- Conjugations by commuting elements commute.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem conj_conj_of_mul_comm {G : Type*} [Group G] {p q : G} (h : p * q = q * p) (Y : G) :
    p * (q * Y * q⁻¹) * p⁻¹ = q * (p * Y * p⁻¹) * q⁻¹ := by
  calc p * (q * Y * q⁻¹) * p⁻¹ = p * q * Y * (p * q)⁻¹ := by group
    _ = q * p * Y * (q * p)⁻¹ := by rw [h]
    _ = q * (p * Y * p⁻¹) * q⁻¹ := by group

/-- The actions of `x_{ij}(a)` and `x_{kl}(b)` commute for `j ≠ k`, `l ≠ i`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem act_comm (hN : 3 ≤ N) (hI : IsSUnital I) (hIA : ∀ a ∈ I, a ∈ A) (i j k l : Fin N)
    (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i) (a b : R) (y : rel I A N) :
    act hI hIA i j hij a (act hI hIA k l hkl b y) =
      act hI hIA k l hkl b (act hI hIA i j hij a y) := by
  obtain ⟨E, hE, h⟩ := Ev.exists hI
    (Ev.and hI (Ev.and hI (act_ev hN hI hIA i j hij a (act hI hIA k l hkl b y))
        (act_ev hN hI hIA k l hkl b y))
      (Ev.and hI (act_ev hN hI hIA k l hkl b (act hI hIA i j hij a y))
        (act_ev hN hI hIA i j hij a y)))
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  have hc : xphi hIA i j hij hE a * xphi hIA k l hkl hE b =
      xphi hIA k l hkl hE b * xphi hIA i j hij hE a :=
    (x_commute_of_ne i j k l hij hkl hjk hli (⟨phi E a, hIA _ (phi_mem hE a)⟩ : A)
      (⟨phi E b, hIA _ (phi_mem hE b)⟩ : A)).eq
  apply Subtype.ext
  rw [h1 hE, h2 hE, h3 hE, h4 hE]
  exact conj_conj_of_mul_comm hc _

/-- The commutator of the actions of `x_{ij}(a)` and `x_{jk}(b)` is the action of `x_{ik}(ab)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem act_adj (hN : 3 ≤ N) (hI : IsSUnital I) (hIA : ∀ a ∈ I, a ∈ A) (i j k : Fin N)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) (y : rel I A N) :
    act hI hIA i j hij a (act hI hIA j k hjk b (act hI hIA i j hij (-a)
      (act hI hIA j k hjk (-b) y))) = act hI hIA i k hik (a * b) y := by
  obtain ⟨e, he, hye⟩ := Ev.exists hI (mem_small_ev hI y.2)
  have hbe : b * e ∈ I := I.mul_mem_left b e he
  have hea : e * a ∈ I := I.mul_mem_right e a he
  obtain ⟨E, hE, h⟩ := Ev.exists hI
    (Ev.and hI (Ev.and hI (ev_dom hI he) (Ev.and hI (ev_dom hI hbe) (ev_dom hI hea)))
      (Ev.and hI
        (Ev.and hI (act_ev hN hI hIA j k hjk (-b) y)
          (act_ev hN hI hIA i j hij (-a) (act hI hIA j k hjk (-b) y)))
        (Ev.and hI
          (Ev.and hI
            (act_ev hN hI hIA j k hjk b
              (act hI hIA i j hij (-a) (act hI hIA j k hjk (-b) y)))
            (act_ev hN hI hIA i j hij a (act hI hIA j k hjk b
              (act hI hIA i j hij (-a) (act hI hIA j k hjk (-b) y)))))
          (act_ev hN hI hIA i k hik (a * b) y))))
  obtain ⟨⟨hEe, hEb, hEa⟩, ⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := h
  have hdA : phi E a * phi E b - phi E (a * b) ∈ A :=
    A.sub_mem (A.mul_mem (hIA _ (phi_mem hE a)) (hIA _ (phi_mem hE b)))
      (hIA _ (phi_mem hE (a * b)))
  have hcomm := commute_small hN hIA hdA (e := e)
    (fun f hef => phi_mul_phi_sub_mul a b hEe hEb.1 hef)
    (fun β hβe => mul_phi_mul_phi_sub a b hEe hEa.2 hβe) i k hik hye
  have hsum : (⟨phi E a, hIA _ (phi_mem hE a)⟩ : A) * ⟨phi E b, hIA _ (phi_mem hE b)⟩ =
      (⟨phi E (a * b), hIA _ (phi_mem hE (a * b))⟩ : A) +
        ⟨phi E a * phi E b - phi E (a * b), hdA⟩ :=
    Subtype.ext
      (show phi E a * phi E b = phi E (a * b) + (phi E a * phi E b - phi E (a * b)) by abel)
  have hC : ⁅xphi hIA i j hij hE a, xphi hIA j k hjk hE b⁆ =
      xphi hIA i k hik hE (a * b) *
        x i k hik (⟨phi E a * phi E b - phi E (a * b), hdA⟩ : A) := by
    unfold xphi
    rw [x_commutator i j k hij hjk hik, x_mul, hsum]
  apply Subtype.ext
  rw [h4 hE, h3 hE, h2 hE, h1 hE, h5 hE, xphi_neg hIA i j hij hE a, xphi_neg hIA j k hjk hE b,
    ← conj_mul_of_commute (a := xphi hIA i k hik hE (a * b)) hcomm, ← hC,
    commutatorElement_def]
  group

end GroupApproximation.Full.LVExcision
