import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFieldK2.Stabilizer

/-!
# Coset representatives for the orbit of `e_p` in `St_N(𝔽₂)`

The Weyl element `wq p q` sends `e_p` to `e_q`. A vector `v` in the orbit of `e_p` under
`Blk A` gets the representatives `y · wq p q`, where `v_q = 1` and `y ∈ Col q A` moves `e_q` to
`v`. Conjugating by `wq p q` sends the roots `x_{ab}` with `b ≠ q` into `Hp p A`. These are the
transversal facts for the Schreier argument in Steinberg's proof of `K₂(𝔽₂) = 0`
(Steinberg 1962; Milnor, *Introduction to algebraic K-theory*, §9-10), towards
`simple_kazhdan_sofic_group.tex` l.733-735 (leaf T1b.iii).
-/

namespace GroupApproximation.Full.LVFieldK2

open SteinbergGroup

variable {N : ℕ}

theorem swap_mem {A : Finset (Fin N)} {a b x : Fin N} (ha : a ∈ A) (hb : b ∈ A) (hx : x ∈ A) :
    Equiv.swap a b x ∈ A := by
  rw [Equiv.swap_apply_def]
  split_ifs
  · exact hb
  · exact ha
  · exact hx

/-- The Weyl representative sending `e_p` to `e_q`. -/
def wq (p q : Fin N) : St N := if h : q = p then 1 else w q p h

theorem wq_self (p : Fin N) : wq p p = 1 := dif_pos rfl

theorem wq_of_ne {p q : Fin N} (h : q ≠ p) : wq p q = w q p h := dif_neg h

theorem wq_inv (p q : Fin N) : (wq p q)⁻¹ = wq p q := by
  by_cases h : q = p
  · rw [h, wq_self, inv_one]
  · rw [wq_of_ne h, w_inv]

theorem act_wq_e (p q : Fin N) : act (wq p q) (e p) = e q := by
  by_cases h : q = p
  · rw [h, wq_self, act_one]
  · rw [wq_of_ne h, act_w_e q p h]

/-- Conjugation by `wq p q` sends the roots `x_{ab}` (`a, b ∈ A`, `b ≠ q`) into `Hp p A`. -/
theorem conj_H (hN : 3 ≤ N) {p q : Fin N} {A : Finset (Fin N)} (hp : p ∈ A) (hq : q ∈ A) :
    ∀ r ∈ rootSub (fun a b => a ∈ A ∧ b ∈ A ∧ b ≠ q),
      (wq p q)⁻¹ * r * wq p q ∈ Hp p A := by
  have hgen : ∀ (a b : Fin N) (h : a ≠ b), (a ∈ A ∧ b ∈ A ∧ b ≠ q) →
      (wq p q)⁻¹ * X a b h * (wq p q)⁻¹⁻¹ ∈ Hp p A := by
    rintro a b h ⟨ha, hb, hbq⟩
    rw [inv_inv, wq_inv]
    by_cases hqp : q = p
    · rw [hqp, wq_self, one_mul, mul_one]
      exact X_mem_Hp a b h ha hb fun hbp => hbq (hbp.trans hqp.symm)
    · rw [wq_of_ne hqp, w_conj hN q p a b hqp h]
      refine X_mem_Hp _ _ _ (swap_mem hq hp ha) (swap_mem hq hp hb) ?_
      intro hbp
      exact hbq ((Equiv.swap_apply_eq_iff.mp hbp).trans (Equiv.swap_apply_right q p))
  intro r hr
  have key := rootSub_conj (Φ := fun a b => a ∈ A ∧ b ∈ A ∧ b ≠ q) (K := Hp p A)
    (wq p q)⁻¹ hgen r hr
  rwa [inv_inv] at key

/-- The transversal: representatives `y · wq p q` for the vector `v`. -/
def Trans (p : Fin N) (A : Finset (Fin N)) (v : Fin N → ZMod 2) : Set (St N) :=
  {t | ∃ q ∈ A, v q = 1 ∧ ∃ y ∈ Col q A, act y (e q) = v ∧ t = y * wq p q}

theorem one_mem_Trans {p : Fin N} {A : Finset (Fin N)} (hp : p ∈ A) :
    (1 : St N) ∈ Trans p A (e p) :=
  ⟨p, hp, e_self p, 1, (Col p A).one_mem, act_one _, by rw [wq_self, one_mul]⟩

theorem Trans_base (p : Fin N) (A : Finset (Fin N)) : Trans p A (e p) ⊆ Hp p A := by
  rintro t ⟨q, _, hq1, y, hy, hyv, rfl⟩
  have hqp : q = p := by
    by_contra hne
    rw [e_ne hne] at hq1
    exact absurd hq1 (by decide)
  subst hqp
  rw [Col_inj A y hy hyv, wq_self, one_mul]
  exact Subgroup.one_mem _

end GroupApproximation.Full.LVFieldK2
