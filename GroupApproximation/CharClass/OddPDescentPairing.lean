import GroupApproximation.CharClass.OddPDescentShift

/-!
# The basis pairing on `E^{⊗p}` and the adjoint of every operator of the descent

The descent computes an element of `E^{⊗p}` by applying `p−1` operators to the top word and
reading off one coefficient.  Read forwards its intermediate terms have no closed form —
`sp-design`'s run at `p = 13` has supports `1, 12, 11, 100, 81, 288, 196, …`.  Read
**backwards** against the pairing, the same number is the top coefficient of a sequence with
a two-line closed form (`OddPDescentDomino.lean`).  This file is the bridge.

```text
    ⟨∂_a u, v⟩ = ⟨u, ξ_a ∧ v⟩     ⟨T u, v⟩ = ⟨u, T^{p−1} v⟩     ⟨N u, v⟩ = ⟨u, N v⟩
```

`T` is an **isometry** of the pairing — it permutes the basis words with signs `±1` — which
is where its adjoint comes from, and is why `T^{p−1}` rather than a separately defined
inverse appears everywhere downstream: no second sign convention is introduced.  `N` is
self-adjoint because reversing the order of the powers permutes `{T^0, …, T^{p−1}}`.

The pairing is a plain `Finset` sum over the finitely many words, not a `Finsupp.sum`: each
operator is given by a matrix with at most one nonzero entry per column, so an adjunction is
one coefficient identity plus `Finset.sum_comm`.
-/

namespace GroupApproximation.CharClass

variable {p : ℕ} (K : Type) [CommRing K]

/-! ## 1. The pairing -/

/-- The pairing that makes the words an orthonormal basis. -/
noncomputable def ePair (u v : EMod K p) : K := ∑ w : EWord p, u w * v w

theorem ePair_comm (u v : EMod K p) : ePair K u v = ePair K v u :=
  Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem ePair_single_left (w : EWord p) (v : EMod K p) :
    ePair K (Finsupp.single w (1 : K)) v = v w := by
  classical
  rw [ePair, Finset.sum_eq_single w]
  · rw [Finsupp.single_eq_same, one_mul]
  · intro b _ hb
    rw [Finsupp.single_eq_of_ne hb, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem ePair_single_right (u : EMod K p) (w : EWord p) :
    ePair K u (Finsupp.single w (1 : K)) = u w := by
  rw [ePair_comm, ePair_single_left]

/-- Evaluating a `linearCombination` coefficientwise: the matrix-entry picture. -/
theorem eLC_coeff (F : EWord p → EMod K p) (u : EMod K p) (w' : EWord p) :
    (Finsupp.linearCombination K F u) w' = ∑ w : EWord p, u w * (F w) w' := by
  classical
  rw [Finsupp.linearCombination_apply,
    Finsupp.sum_fintype _ _ (by intro i; simp), Finsupp.finsetSum_apply]
  exact Finset.sum_congr rfl fun w _ => by rw [Finsupp.smul_apply, smul_eq_mul]

/-! ## 2. `eAdj`: the adjoint relation, and how it composes -/

/-- `L'` is the adjoint of `L` for the basis pairing. -/
def eAdj (L L' : EMod K p →ₗ[K] EMod K p) : Prop :=
  ∀ u v : EMod K p, ePair K (L u) v = ePair K u (L' v)

theorem eAdj_comp {L₁ L₁' L₂ L₂' : EMod K p →ₗ[K] EMod K p}
    (h₁ : eAdj K L₁ L₁') (h₂ : eAdj K L₂ L₂') :
    eAdj K (L₁.comp L₂) (L₂'.comp L₁') := by
  intro u v
  simp only [LinearMap.comp_apply]
  -- `eAdj` is a plain `def`, so `rw` cannot see the equation through it: apply it first
  rw [h₁ (L₂ u) v, h₂ u (L₁' v)]

theorem eAdj_id : eAdj K (LinearMap.id : EMod K p →ₗ[K] EMod K p) LinearMap.id :=
  fun _ _ => rfl

theorem ePair_sub_left (A B : EMod K p →ₗ[K] EMod K p) (x y : EMod K p) :
    ePair K ((A - B) x) y = ePair K (A x) y - ePair K (B x) y := by
  simp only [ePair, LinearMap.sub_apply, Finsupp.coe_sub, Pi.sub_apply, sub_mul,
    Finset.sum_sub_distrib]

theorem ePair_sub_right (A B : EMod K p →ₗ[K] EMod K p) (x y : EMod K p) :
    ePair K x ((A - B) y) = ePair K x (A y) - ePair K x (B y) := by
  simp only [ePair, LinearMap.sub_apply, Finsupp.coe_sub, Pi.sub_apply, mul_sub,
    Finset.sum_sub_distrib]

theorem eAdj_sub {L₁ L₁' L₂ L₂' : EMod K p →ₗ[K] EMod K p}
    (h₁ : eAdj K L₁ L₁') (h₂ : eAdj K L₂ L₂') : eAdj K (L₁ - L₂) (L₁' - L₂') := by
  intro u v
  rw [ePair_sub_left, ePair_sub_right, h₁ u v, h₂ u v]

/-! ## 3. The wedge and the partial derivative are adjoint -/

/-- The matrix of `ePart a` is the transpose of the matrix of `eWedge a`. -/
theorem ePartGen_coeff (a : Fin p) (w w' : EWord p) :
    (ePartGen K a w) w' = (eWedgeGen K a w') w := by
  classical
  by_cases hw : w a = true
  · by_cases hw' : w' a = true
    · have hne : Function.update w a false ≠ w' := by
        intro hcon
        have hval := congrFun hcon a
        rw [Function.update_self] at hval
        rw [← hval] at hw'
        exact absurd hw' (by simp)
      rw [eWedgeGen_of_true K hw', ePartGen_of_true K hw, Finsupp.coe_zero, Pi.zero_apply,
        Finsupp.smul_apply, Finsupp.single_apply, if_neg hne, smul_zero]
    · have hw'' : w' a = false := Bool.eq_false_of_not_eq_true hw'
      rw [ePartGen_of_true K hw, eWedgeGen_of_false K hw'', Finsupp.smul_apply,
        Finsupp.smul_apply, Finsupp.single_apply, Finsupp.single_apply, smul_eq_mul,
        smul_eq_mul, mul_ite, mul_ite, mul_one, mul_zero, mul_one, mul_zero]
      by_cases hup : Function.update w a false = w'
      · have hup' : Function.update w' a true = w := by
          rw [← hup, Function.update_idem, Function.update_eq_self_iff]
          exact hw.symm
        rw [if_pos hup, if_pos hup', ← hup, ePre_update_of_le w a false a le_rfl]
      · have hup' : Function.update w' a true ≠ w := by
          intro hcon
          apply hup
          rw [← hcon, Function.update_idem, Function.update_eq_self_iff]
          exact hw''.symm
        rw [if_neg hup, if_neg hup']
  · have hwf : w a = false := Bool.eq_false_of_not_eq_true hw
    rw [ePartGen_of_false K hwf, Finsupp.coe_zero, Pi.zero_apply]
    by_cases hw' : w' a = true
    · rw [eWedgeGen_of_true K hw', Finsupp.coe_zero, Pi.zero_apply]
    · have hw'' : w' a = false := Bool.eq_false_of_not_eq_true hw'
      have hne : Function.update w' a true ≠ w := by
        intro hcon
        have hval := congrFun hcon a
        rw [Function.update_self] at hval
        rw [← hval] at hwf
        exact absurd hwf (by simp)
      rw [eWedgeGen_of_false K hw'', Finsupp.smul_apply, Finsupp.single_apply, if_neg hne,
        smul_zero]

theorem eAdj_ePart_eWedge (a : Fin p) : eAdj K (ePart K a) (eWedge K a) := by
  intro u v
  have hL : ePair K (ePart K a u) v
      = ∑ w' : EWord p, ∑ w : EWord p, u w * (ePartGen K a w) w' * v w' := by
    rw [ePair]
    refine Finset.sum_congr rfl fun w' _ => ?_
    rw [show (ePart K a u) w' = ∑ w : EWord p, u w * (ePartGen K a w) w' from
      eLC_coeff K (ePartGen K a) u w', Finset.sum_mul]
  have hR : ePair K u (eWedge K a v)
      = ∑ w : EWord p, ∑ w' : EWord p, u w * (v w' * (eWedgeGen K a w') w) := by
    rw [ePair]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [show (eWedge K a v) w = ∑ w' : EWord p, v w' * (eWedgeGen K a w') w from
      eLC_coeff K (eWedgeGen K a) v w, Finset.mul_sum]
  rw [hL, hR, Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => ?_
  rw [ePartGen_coeff K a w w']
  ring

theorem eAdj_eWedge_ePart (a : Fin p) : eAdj K (eWedge K a) (ePart K a) := by
  intro u v
  exact (ePair_comm K _ _).trans ((eAdj_ePart_eWedge K a v u).symm.trans (ePair_comm K _ _))

/-! ## 4. `eT` is an isometry -/

/-- The rotation of words is a bijection. -/
def eRotEquiv [NeZero p] : EWord p ≃ EWord p where
  toFun := eRot
  invFun w := fun j => w (j - 1)
  left_inv w := by funext j; simp [eRot]
  right_inv w := by funext j; simp [eRot]

variable [NeZero p]

theorem eRot_injective : Function.Injective (eRot : EWord p → EWord p) :=
  (eRotEquiv (p := p)).injective

theorem eSgn_mul_self (w : EWord p) : eSgn K w * eSgn K w = 1 := by
  rw [eSgn, ← pow_add, ← two_mul, pow_mul]
  simp

theorem eT_coeff_eRot (u : EMod K p) (w : EWord p) :
    (eT K u) (eRot w) = u w * eSgn K w := by
  classical
  rw [show (eT K u) (eRot w) = ∑ z : EWord p, u z * (eTGen K z) (eRot w) from
    eLC_coeff K (eTGen K) u (eRot w)]
  rw [Finset.sum_eq_single w]
  · rw [eTGen, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
  · intro z _ hz
    rw [eTGen, Finsupp.smul_apply,
      Finsupp.single_eq_of_ne (fun hcon => hz (eRot_injective hcon).symm), smul_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem ePair_eT_eT (u v : EMod K p) : ePair K (eT K u) (eT K v) = ePair K u v := by
  rw [ePair, ePair]
  rw [← Equiv.sum_comp (eRotEquiv (p := p)) (fun w' => (eT K u) w' * (eT K v) w')]
  refine Finset.sum_congr rfl fun w _ => ?_
  show (eT K u) (eRot w) * (eT K v) (eRot w) = u w * v w
  rw [eT_coeff_eRot, eT_coeff_eRot]
  calc u w * eSgn K w * (v w * eSgn K w)
      = u w * v w * (eSgn K w * eSgn K w) := by ring
    _ = u w * v w := by rw [eSgn_mul_self, mul_one]

theorem ePair_eT_pow (k : ℕ) (u v : EMod K p) :
    ePair K ((eT K ^ k) u) ((eT K ^ k) v) = ePair K u v := by
  induction k generalizing u v with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ePair_eT_eT, ih]

/-- `T` is adjoint to `T^{p−1}`, which is its inverse. -/
theorem eAdj_eT_pow (k : ℕ) (hk : k ≤ p) :
    eAdj K ((eT K : EMod K p →ₗ[K] EMod K p) ^ k) ((eT K) ^ (p - k)) := by
  intro u v
  have hcomp : (eT K ^ k) ((eT K ^ (p - k)) v) = v := by
    rw [← Module.End.mul_apply, ← pow_add]
    have : k + (p - k) = p := by omega
    rw [this, eT_pow_card, Module.End.one_apply]
  calc ePair K ((eT K ^ k) u) v
      = ePair K ((eT K ^ k) u) ((eT K ^ k) ((eT K ^ (p - k)) v)) := by rw [hcomp]
    _ = ePair K u ((eT K ^ (p - k)) v) := ePair_eT_pow K k _ _

theorem eAdj_eT : eAdj K (eT K : EMod K p →ₗ[K] EMod K p) ((eT K) ^ (p - 1)) := by
  have h := eAdj_eT_pow K 1 (Nat.pos_of_ne_zero (NeZero.ne p))
  rwa [pow_one] at h

/-! ## 5. `eN` is self-adjoint -/

theorem eN_eq_sum_rev :
    (∑ k ∈ Finset.range p, (eT K : EMod K p →ₗ[K] EMod K p) ^ (p - k)) = eN K := by
  have hrefl := Finset.sum_range_reflect
    (fun j => (eT K : EMod K p →ₗ[K] EMod K p) ^ (p - j)) p
  have hterm : ∀ j ∈ Finset.range p,
      (eT K : EMod K p →ₗ[K] EMod K p) ^ (p - (p - 1 - j)) = (eT K) ^ (j + 1) := by
    intro j hj
    rw [Finset.mem_range] at hj
    congr 1
    omega
  rw [Finset.sum_congr rfl hterm] at hrefl
  rw [← hrefl, eN_sum_succ]

theorem eAdj_eN : eAdj K (eN K : EMod K p →ₗ[K] EMod K p) (eN K) := by
  intro u v
  have hL : ePair K (eN K u) v
      = ∑ k ∈ Finset.range p, ePair K ((eT K ^ k) u) v := by
    simp only [ePair, eN, LinearMap.sum_apply, Finsupp.finsetSum_apply, Finset.sum_mul]
    exact Finset.sum_comm
  have hR : ePair K u ((eN K) v)
      = ∑ k ∈ Finset.range p, ePair K u ((eT K ^ (p - k)) v) := by
    rw [← eN_eq_sum_rev K]
    simp only [ePair, LinearMap.sum_apply, Finsupp.finsetSum_apply, Finset.mul_sum]
    exact Finset.sum_comm
  rw [hL, hR]
  refine Finset.sum_congr rfl fun k hk => ?_
  exact eAdj_eT_pow K k (le_of_lt (Finset.mem_range.mp hk)) u v

end GroupApproximation.CharClass
