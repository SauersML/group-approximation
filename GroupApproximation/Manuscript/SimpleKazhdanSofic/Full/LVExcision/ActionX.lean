import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVExcision.ActionHom

/-!
# The action on explicit elements, and equivariance (lane LVExcision)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.  Stable `K₂`
excision (Suslin–Wodzicki, Ann. Math. 136 (1992), Thm A; Keune, J. Algebra 54 (1978); ABC
thm:skewyao, `yaoseq6.tex` l.558-640).

* `relX … k l hkl hc = x_{kl}(c) ∈ rel I A N` for `c ∈ I`;
* `act_relX_of_ne`, `act_relX_adj_left`, `act_relX_adj_right`: the action of `x_{ij}(t)`,
  `t ∈ R`, on `x_{kl}(c)` is given by the Steinberg commutator formulas, although `t ∉ A`;
* `act_eq_conj`: for `c ∈ A` the action of `x_{kl}(c)` is conjugation by `x_{kl}(c)`;
* `actHom_ringMap_subtype`: `St_N(A)` acts on `rel` through `St_N(A) → St_N(R)` by
  conjugation.
-/

namespace GroupApproximation.Full.LVExcision

noncomputable section

open SteinbergGroup

variable {R : Type*} [Ring R] {I : TwoSidedIdeal R} {A : Subring R} {N : ℕ}

/-- The element `x_{kl}(c)` of `rel I A N`, for `c ∈ I`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
def relX (hIA : ∀ a ∈ I, a ∈ A) (k l : Fin N) (hkl : k ≠ l) {c : R} (hc : c ∈ I) :
    rel I A N :=
  ⟨x k l hkl (⟨c, hIA c hc⟩ : A), x_mem_rel hkl (hIA c hc) hc⟩

/-- The underlying element of `relX`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem relX_val (hIA : ∀ a ∈ I, a ∈ A) (k l : Fin N) (hkl : k ≠ l) {c : R} (hc : c ∈ I) :
    (relX hIA k l hkl hc).1 = x k l hkl (⟨c, hIA c hc⟩ : A) :=
  rfl

/-- The action of `x_{ij}(t)` fixes `x_{kl}(c)` for `j ≠ k`, `l ≠ i` (this includes the root
`(k, l) = (i, j)`).
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem act_relX_of_ne (hN : 3 ≤ N) (hI : IsSUnital I) (hIA : ∀ a ∈ I, a ∈ A) (i j k l : Fin N)
    (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i) (t : R) {c : R} (hc : c ∈ I) :
    act hI hIA i j hij t (relX hIA k l hkl hc) = relX hIA k l hkl hc := by
  obtain ⟨E, hE, h⟩ := Ev.exists hI (act_ev hN hI hIA i j hij t (relX hIA k l hkl hc))
  apply Subtype.ext
  rw [h hE]
  exact (x_commute_of_ne i j k l hij hkl hjk hli (⟨phi E t, hIA _ (phi_mem hE t)⟩ : A)
    (⟨c, hIA c hc⟩ : A)).mul_inv_cancel

/-- The action of `x_{ij}(t)` on `x_{jk}(β)` is `x_{ik}(tβ) x_{jk}(β)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem act_relX_adj_left (hN : 3 ≤ N) (hI : IsSUnital I) (hIA : ∀ a ∈ I, a ∈ A)
    (i j k : Fin N) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (t : R) {β : R} (hβ : β ∈ I) :
    act hI hIA i j hij t (relX hIA j k hjk hβ) =
      relX hIA i k hik (I.mul_mem_left t β hβ) * relX hIA j k hjk hβ := by
  obtain ⟨E, hE, hEb, h⟩ := Ev.exists hI
    (Ev.and hI (ev_dom hI hβ) (act_ev hN hI hIA i j hij t (relX hIA j k hjk hβ)))
  have hprod : (⟨phi E t, hIA _ (phi_mem hE t)⟩ : A) * ⟨β, hIA β hβ⟩ =
      ⟨t * β, hIA _ (I.mul_mem_left t β hβ)⟩ :=
    Subtype.ext (phi_mul_of hEb.1 t)
  apply Subtype.ext
  rw [h hE, Subgroup.coe_mul]
  simp only [relX_val]
  unfold xphi
  rw [x_conj_adj_left i j k hij hjk hik, hprod]

/-- The action of `x_{jk}(t)` on `x_{ij}(β)` is `x_{ik}(-(βt)) x_{ij}(β)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem act_relX_adj_right (hN : 3 ≤ N) (hI : IsSUnital I) (hIA : ∀ a ∈ I, a ∈ A)
    (i j k : Fin N) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (t : R) {β : R} (hβ : β ∈ I) :
    act hI hIA j k hjk t (relX hIA i j hij hβ) =
      relX hIA i k hik (I.neg_mem (I.mul_mem_right β t hβ)) * relX hIA i j hij hβ := by
  obtain ⟨E, hE, hEb, h⟩ := Ev.exists hI
    (Ev.and hI (ev_dom hI hβ) (act_ev hN hI hIA j k hjk t (relX hIA i j hij hβ)))
  have hprod : -((⟨β, hIA β hβ⟩ : A) * ⟨phi E t, hIA _ (phi_mem hE t)⟩) =
      ⟨-(β * t), hIA _ (I.neg_mem (I.mul_mem_right β t hβ))⟩ :=
    Subtype.ext (show -(β * phi E t) = -(β * t) by rw [mul_phi_of hEb.2])
  apply Subtype.ext
  rw [h hE, Subgroup.coe_mul]
  simp only [relX_val]
  unfold xphi
  rw [x_conj_adj_right i j k hij hjk hik, hprod]

/-- For `c ∈ A`, the action of `x_{kl}(c)` is conjugation by `x_{kl}(c) ∈ St_N(A)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem act_eq_conj (hN : 3 ≤ N) (hI : IsSUnital I) (hIA : ∀ a ∈ I, a ∈ A) (k l : Fin N)
    (hkl : k ≠ l) (c : A) (y : rel I A N) :
    (act hI hIA k l hkl (c : R) y).1 = x k l hkl c * y.1 * (x k l hkl c)⁻¹ := by
  obtain ⟨e, he, hye⟩ := Ev.exists hI (mem_small_ev hI y.2)
  obtain ⟨E, hE, hEe, h⟩ := Ev.exists hI
    (Ev.and hI (ev_dom hI he) (act_ev hN hI hIA k l hkl (c : R) y))
  have hdA : (c : R) - phi E c ∈ A := A.sub_mem c.2 (hIA _ (phi_mem hE (c : R)))
  have hC := commute_small hN hIA hdA (e := e)
    (fun f hef => by rw [sub_mul, phi_mul_of (hEe.left hef), sub_self])
    (fun b hbe => by rw [mul_sub, mul_phi_of (hEe.right hbe), sub_self]) k l hkl hye
  have h' : (⟨phi E c, hIA _ (phi_mem hE (c : R))⟩ : A) + ⟨(c : R) - phi E c, hdA⟩ = c :=
    Subtype.ext (show phi E c + ((c : R) - phi E c) = (c : R) by abel)
  have hsplit : x k l hkl c =
      xphi hIA k l hkl hE (c : R) * x k l hkl (⟨(c : R) - phi E c, hdA⟩ : A) := by
    unfold xphi
    rw [x_mul, h']
  rw [h hE, hsplit, conj_mul_of_commute hC]

/-- `St_N(A)` acts on `rel` through `St_N(A) → St_N(R)` by conjugation.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem actHom_ringMap_subtype (hN : 3 ≤ N) (hI : IsSUnital I) (hIA : ∀ a ∈ I, a ∈ A)
    (g : SteinbergGroup (Fin N) A) (y : rel I A N) :
    (actHom hN hI hIA (ringMap A.subtype g) y).1 = g * y.1 * g⁻¹ := by
  have hg : g ∈ Subgroup.closure (Set.range
      (PresentedGroup.of : SteinbergGenerator (Fin N) A → SteinbergGroup (Fin N) A)) := by
    rw [PresentedGroup.closure_range_of]
    exact Subgroup.mem_top g
  revert y
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨⟨i, j, hij, a⟩, rfl⟩ := hg
    intro y
    change (actHom hN hI hIA (ringMap A.subtype (x i j hij a)) y).1 =
      x i j hij a * y.1 * (x i j hij a)⁻¹
    rw [ringMap_x, actHom_x_apply]
    exact act_eq_conj hN hI hIA i j hij a y
  | one =>
    intro y
    rw [map_one, map_one, MulAut.one_apply, one_mul, inv_one, mul_one]
  | mul g h _ _ ihg ihh =>
    intro y
    rw [map_mul, map_mul, MulAut.mul_apply, ihg, ihh]
    group
  | inv g _ ihg =>
    intro y
    have h := ihg ((actHom hN hI hIA (ringMap A.subtype g)).symm y)
    rw [MulEquiv.apply_symm_apply] at h
    rw [map_inv, map_inv, MulAut.inv_apply, h]
    group

end

end GroupApproximation.Full.LVExcision
