import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVExcision.Small

/-!
# The generator automorphisms of the relative Steinberg subgroup (lane LVExcision)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.  Stable `K₂`
excision (Suslin–Wodzicki, Ann. Math. 136 (1992), Thm A; Keune, J. Algebra 54 (1978); ABC
thm:skewyao, `yaoseq6.tex` l.558-640).  Let `I` be an s-unital ideal of `R` contained in a
subring `A`, and `N ≥ 3`.

For `r ∈ R` and a root `(k, l)` we define an automorphism `actAut … k l hkl r` of
`rel I A N = ⟨x_{ij}(b) : b ∈ I⟩ ≤ St_N(A)`: on an element `y ∈ small E` it is conjugation by
`x_{kl}(phi E r)`, which does not depend on the choice of `E` (`conj_eq_of_dom`).  This is the
formula `x_{kl}(r) · y = x_{kl}(r) y x_{kl}(r)⁻¹`, computed inside `St_N(A)` although
`r ∉ A` in general.
-/

namespace GroupApproximation.Full.LVExcision

noncomputable section

open SteinbergGroup

variable {R : Type*} [Ring R] {I : TwoSidedIdeal R} {A : Subring R} {N : ℕ}

/-- A chosen `E ∈ I` with `y ∈ small E`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
def unitOf (hI : IsSUnital I) (y : rel I A N) : R :=
  Classical.choose (Ev.exists hI (mem_small_ev hI y.2))

/-- `unitOf hI y ∈ I`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem unitOf_mem (hI : IsSUnital I) (y : rel I A N) : unitOf hI y ∈ I :=
  (Classical.choose_spec (Ev.exists hI (mem_small_ev hI y.2))).1

/-- `y ∈ small (unitOf hI y)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem mem_small_unitOf (hI : IsSUnital I) (y : rel I A N) :
    y.1 ∈ small I A N (unitOf hI y) :=
  (Classical.choose_spec (Ev.exists hI (mem_small_ev hI y.2))).2

/-- The element `x_{kl}(phi E r)` of `St_N(A)`, for `E ∈ I`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
def xphi (hIA : ∀ a ∈ I, a ∈ A) (k l : Fin N) (hkl : k ≠ l) {E : R} (hE : E ∈ I) (r : R) :
    SteinbergGroup (Fin N) A :=
  x k l hkl ⟨phi E r, hIA _ (phi_mem hE r)⟩

/-- `x_{kl}(phi E r) ∈ rel`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem xphi_mem (hIA : ∀ a ∈ I, a ∈ A) (k l : Fin N) (hkl : k ≠ l) {E : R} (hE : E ∈ I)
    (r : R) : xphi hIA k l hkl hE r ∈ rel I A N :=
  x_mem_rel hkl (hIA _ (phi_mem hE r)) (phi_mem hE r)

/-- `x_{kl}(phi E a) x_{kl}(phi E b) = x_{kl}(phi E (a + b))`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem xphi_add (hIA : ∀ a ∈ I, a ∈ A) (k l : Fin N) (hkl : k ≠ l) {E : R} (hE : E ∈ I)
    (a b : R) :
    xphi hIA k l hkl hE a * xphi hIA k l hkl hE b = xphi hIA k l hkl hE (a + b) := by
  have h : (⟨phi E a, hIA _ (phi_mem hE a)⟩ : A) + ⟨phi E b, hIA _ (phi_mem hE b)⟩ =
      ⟨phi E (a + b), hIA _ (phi_mem hE (a + b))⟩ := Subtype.ext (phi_add E a b).symm
  unfold xphi
  rw [x_mul, h]

/-- `x_{kl}(phi E 0) = 1`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem xphi_zero (hIA : ∀ a ∈ I, a ∈ A) (k l : Fin N) (hkl : k ≠ l) {E : R} (hE : E ∈ I) :
    xphi hIA k l hkl hE 0 = 1 := by
  have h : (⟨phi E 0, hIA _ (phi_mem hE 0)⟩ : A) = 0 := Subtype.ext (phi_zero E)
  unfold xphi
  rw [h, x_zero]

/-- `x_{kl}(phi E (-r)) = x_{kl}(phi E r)⁻¹`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem xphi_neg (hIA : ∀ a ∈ I, a ∈ A) (k l : Fin N) (hkl : k ≠ l) {E : R} (hE : E ∈ I)
    (r : R) : xphi hIA k l hkl hE (-r) = (xphi hIA k l hkl hE r)⁻¹ := by
  have h : (⟨phi E (-r), hIA _ (phi_mem hE (-r))⟩ : A) = -⟨phi E r, hIA _ (phi_mem hE r)⟩ :=
    Subtype.ext (phi_neg E r)
  unfold xphi
  rw [h, x_neg]

/-- The action of `x_{kl}(r)` on `rel`: conjugation by `x_{kl}(phi E r)` for `E = unitOf y`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
def act (hI : IsSUnital I) (hIA : ∀ a ∈ I, a ∈ A) (k l : Fin N) (hkl : k ≠ l) (r : R)
    (y : rel I A N) : rel I A N :=
  ⟨xphi hIA k l hkl (unitOf_mem hI y) r * y.1 * (xphi hIA k l hkl (unitOf_mem hI y) r)⁻¹,
    (rel I A N).mul_mem ((rel I A N).mul_mem (xphi_mem hIA k l hkl (unitOf_mem hI y) r) y.2)
      ((rel I A N).inv_mem (xphi_mem hIA k l hkl (unitOf_mem hI y) r))⟩

/-- On `y ∈ small E`, the action of `x_{kl}(r)` is conjugation by `x_{kl}(phi E r)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem act_spec (hN : 3 ≤ N) (hI : IsSUnital I) (hIA : ∀ a ∈ I, a ∈ A) (k l : Fin N)
    (hkl : k ≠ l) (r : R) (y : rel I A N) {E : R} (hE : E ∈ I) (hy : y.1 ∈ small I A N E) :
    (act hI hIA k l hkl r y).1 = xphi hIA k l hkl hE r * y.1 * (xphi hIA k l hkl hE r)⁻¹ := by
  obtain ⟨D, hD, hDu, hDE, -⟩ := exists_unit₃ hI (unitOf_mem hI y) hE hE
  exact (conj_eq_of_dom hN hIA (unitOf_mem hI y) hD hDu r k l hkl (mem_small_unitOf hI y)).trans
    (conj_eq_of_dom hN hIA hE hD hDE r k l hkl hy).symm

/-- Eventually in `E`, the action of `x_{kl}(r)` on `y` is conjugation by `x_{kl}(phi E r)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem act_ev (hN : 3 ≤ N) (hI : IsSUnital I) (hIA : ∀ a ∈ I, a ∈ A) (k l : Fin N)
    (hkl : k ≠ l) (r : R) (y : rel I A N) :
    Ev I (fun E => ∀ hE : E ∈ I,
      (act hI hIA k l hkl r y).1 = xphi hIA k l hkl hE r * y.1 * (xphi hIA k l hkl hE r)⁻¹) :=
  (mem_small_ev hI y.2).mono (fun _ _ hy hE => act_spec hN hI hIA k l hkl r y hE hy)

/-- The actions of `x_{kl}(a)` and `x_{kl}(b)` compose to that of `x_{kl}(a + b)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem act_add (hN : 3 ≤ N) (hI : IsSUnital I) (hIA : ∀ a ∈ I, a ∈ A) (k l : Fin N)
    (hkl : k ≠ l) (a b : R) (y : rel I A N) :
    act hI hIA k l hkl a (act hI hIA k l hkl b y) = act hI hIA k l hkl (a + b) y := by
  obtain ⟨E, hE, h⟩ := Ev.exists hI
    (Ev.and hI (act_ev hN hI hIA k l hkl a (act hI hIA k l hkl b y))
      (Ev.and hI (act_ev hN hI hIA k l hkl b y) (act_ev hN hI hIA k l hkl (a + b) y)))
  apply Subtype.ext
  rw [h.1 hE, h.2.1 hE, h.2.2 hE, ← xphi_add hIA k l hkl hE a b]
  group

/-- The action of `x_{kl}(0)` is trivial.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem act_zero (hN : 3 ≤ N) (hI : IsSUnital I) (hIA : ∀ a ∈ I, a ∈ A) (k l : Fin N)
    (hkl : k ≠ l) (y : rel I A N) : act hI hIA k l hkl 0 y = y := by
  obtain ⟨E, hE, h⟩ := Ev.exists hI (act_ev hN hI hIA k l hkl 0 y)
  apply Subtype.ext
  rw [h hE, xphi_zero, one_mul, inv_one, mul_one]

/-- The automorphism of `rel` given by `x_{kl}(r)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
def actAut (hN : 3 ≤ N) (hI : IsSUnital I) (hIA : ∀ a ∈ I, a ∈ A) (k l : Fin N)
    (hkl : k ≠ l) (r : R) : MulAut (rel I A N) where
  toFun := act hI hIA k l hkl r
  invFun := act hI hIA k l hkl (-r)
  left_inv y := by
    show act hI hIA k l hkl (-r) (act hI hIA k l hkl r y) = y
    rw [act_add hN hI hIA k l hkl, neg_add_cancel, act_zero hN hI hIA k l hkl]
  right_inv y := by
    show act hI hIA k l hkl r (act hI hIA k l hkl (-r) y) = y
    rw [act_add hN hI hIA k l hkl, add_neg_cancel, act_zero hN hI hIA k l hkl]
  map_mul' y z := by
    show act hI hIA k l hkl r (y * z) = act hI hIA k l hkl r y * act hI hIA k l hkl r z
    obtain ⟨E, hE, h⟩ := Ev.exists hI
      (Ev.and hI (act_ev hN hI hIA k l hkl r (y * z))
        (Ev.and hI (act_ev hN hI hIA k l hkl r y) (act_ev hN hI hIA k l hkl r z)))
    apply Subtype.ext
    rw [Subgroup.coe_mul, h.1 hE, h.2.1 hE, h.2.2 hE, Subgroup.coe_mul]
    group

/-- `actAut … r y` is `act … r y`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem actAut_apply (hN : 3 ≤ N) (hI : IsSUnital I) (hIA : ∀ a ∈ I, a ∈ A) (k l : Fin N)
    (hkl : k ≠ l) (r : R) (y : rel I A N) :
    actAut hN hI hIA k l hkl r y = act hI hIA k l hkl r y :=
  rfl

end

end GroupApproximation.Full.LVExcision
