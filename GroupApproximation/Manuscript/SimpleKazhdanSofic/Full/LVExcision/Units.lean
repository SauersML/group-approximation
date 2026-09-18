import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVExcision.Commute

/-!
# Local units in an s-unital ideal (lane LVExcision)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.  Ring-theoretic
bookkeeping for stable `K₂` excision (Suslin–Wodzicki, Ann. Math. 136 (1992), Thm A; Keune,
J. Algebra 54 (1978); ABC thm:skewyao, `yaoseq6.tex` l.558-640):

* `IsSUnital I`: every finite subset of `I` has a two-sided local unit in `I`;
* `phi e r = e r + r e - e r e`, an element of `I` when `e ∈ I`, which acts like `r` against
  elements for which `e` is a unit (`phi_mul_of`, `mul_phi_of`);
* `Dom E e`: `E` is a two-sided unit for `e`;
* `Ev I p`: `p E` holds for every `E ∈ I` dominating some fixed `e ∈ I` ("eventually in `E`");
  for s-unital `I` these statements are closed under conjunction and have witnesses.
-/

namespace GroupApproximation.Full.LVExcision

variable {R : Type*} [Ring R] (I : TwoSidedIdeal R)

/-- Every finite subset of `I` has a two-sided local unit in `I`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
def IsSUnital : Prop :=
  ∀ s : Finset R, (∀ a ∈ s, a ∈ I) → ∃ e ∈ I, ∀ a ∈ s, e * a = a ∧ a * e = a

/-- The element `e r + r e - e r e`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
def phi (e r : R) : R := e * r + r * e - e * r * e

variable {I}

/-- `phi e r ∈ I` for `e ∈ I`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem phi_mem {e : R} (he : e ∈ I) (r : R) : phi e r ∈ I :=
  I.sub_mem (I.add_mem (I.mul_mem_right e r he) (I.mul_mem_left r e he))
    (I.mul_mem_left (e * r) e he)

/-- `phi e r * f = r * f` when `e * f = f`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem phi_mul_of {e f : R} (hef : e * f = f) (r : R) : phi e r * f = r * f := by
  simp only [phi, sub_mul, add_mul, mul_assoc, hef]
  abel

/-- `b * phi e r = b * r` when `b * e = b`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem mul_phi_of {e b : R} (hbe : b * e = b) (r : R) : b * phi e r = b * r := by
  simp only [phi, mul_sub, mul_add, ← mul_assoc, hbe]
  abel

/-- `phi e` is additive.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem phi_add (e r s : R) : phi e (r + s) = phi e r + phi e s := by
  simp only [phi, mul_add, add_mul]
  abel

/-- `phi e 0 = 0`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem phi_zero (e : R) : phi e 0 = 0 := by
  simp [phi]

/-- `phi e (-r) = -phi e r`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem phi_neg (e r : R) : phi e (-r) = -phi e r := by
  simp only [phi, mul_neg, neg_mul]
  abel

/-- `E` is a two-sided unit for `e`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
def Dom (E e : R) : Prop := E * e = e ∧ e * E = e

/-- A unit for a unit of `x` is a left unit for `x`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem Dom.left {E e x : R} (h : Dom E e) (hx : e * x = x) : E * x = x := by
  rw [← hx, ← mul_assoc, h.1]

/-- A unit for a unit of `x` is a right unit for `x`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem Dom.right {E e x : R} (h : Dom E e) (hx : x * e = x) : x * E = x := by
  rw [← hx, mul_assoc, h.2]

/-- Domination is transitive.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem Dom.trans {E e x : R} (h : Dom E e) (hx : Dom e x) : Dom E x :=
  ⟨h.left hx.1, h.right hx.2⟩

/-- A common local unit for three elements of `I`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem exists_unit₃ (hI : IsSUnital I) {a b c : R} (ha : a ∈ I) (hb : b ∈ I) (hc : c ∈ I) :
    ∃ e ∈ I, Dom e a ∧ Dom e b ∧ Dom e c := by
  classical
  obtain ⟨e, he, h⟩ := hI {a, b, c} (by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> assumption)
  exact ⟨e, he, h a (by simp), h b (by simp), h c (by simp)⟩

variable (I)

/-- `p E` holds for all `E ∈ I` dominating some `e ∈ I`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
def Ev (p : R → Prop) : Prop := ∃ e ∈ I, ∀ E ∈ I, Dom E e → p E

variable {I}

/-- Monotonicity of `Ev`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem Ev.mono {p q : R → Prop} (h : Ev I p) (hpq : ∀ E ∈ I, p E → q E) : Ev I q := by
  obtain ⟨e, he, hp⟩ := h
  exact ⟨e, he, fun E hE hEe => hpq E hE (hp E hE hEe)⟩

/-- `Ev` is closed under conjunction.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem Ev.and (hI : IsSUnital I) {p q : R → Prop} (hp : Ev I p) (hq : Ev I q) :
    Ev I (fun E => p E ∧ q E) := by
  obtain ⟨e₁, he₁, h₁⟩ := hp
  obtain ⟨e₂, he₂, h₂⟩ := hq
  obtain ⟨e, he, hd₁, hd₂, -⟩ := exists_unit₃ hI he₁ he₂ he₁
  exact ⟨e, he, fun E hE hEe => ⟨h₁ E hE (hEe.trans hd₁), h₂ E hE (hEe.trans hd₂)⟩⟩

/-- An eventual statement has a witness.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem Ev.exists (hI : IsSUnital I) {p : R → Prop} (h : Ev I p) : ∃ E ∈ I, p E := by
  obtain ⟨e, he, hp⟩ := h
  obtain ⟨E, hE, hd, -, -⟩ := exists_unit₃ hI he he he
  exact ⟨E, hE, hp E hE hd⟩

/-- Eventually `E` is a two-sided unit for a given `x ∈ I`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem ev_dom (hI : IsSUnital I) {x : R} (hx : x ∈ I) : Ev I (fun E => Dom E x) := by
  obtain ⟨e, he, hd, -, -⟩ := exists_unit₃ hI hx hx hx
  exact ⟨e, he, fun _ _ hEe => hEe.trans hd⟩

end GroupApproximation.Full.LVExcision
