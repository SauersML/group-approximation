import GroupApproximation.KunThom.NormalizationFromCriterion

/-!
# Almost commutation spreads from generators to the generated subgroup

`SoficApproximation.AlmostCommutes A v g` says that the normalized Hamming
distance between `v n * A(g)` and `A(g) * v n` tends to zero.  The set of `g`
with this property contains `1` and is closed under products and inverses,
because approximate multiplicativity makes `A(g h)` close to `A(g) A(h)` and
`A(g⁻¹)` close to `A(g)⁻¹`.  Consequently almost commutation with a generating
set of a subgroup `Γ` gives almost commutation with every element of `Γ`
(`SoficApproximation.almostCommutes_of_generators`).

This is how a sequence built from cluster arrows that are equivariant for the
generator labels of `Γ` meets the hypothesis and the conclusion of
`HasSequentialCentralizerNormalization`, which quantify over all of `Γ`.
-/

namespace GroupApproximation

namespace SoficApproximation

variable {G : Type} [Group G] (A : SoficApproximation G)

/-- Every sequence almost commutes with the model of the identity. -/
theorem almostCommutes_one {v : ∀ n, Equiv.Perm (A.model n)} : A.AlmostCommutes v 1 := by
  unfold SoficApproximation.AlmostCommutes
  refine Vanishing.squeeze (fun _ ↦ hammingDistance_nonnegative _ _ _) (fun n ↦ ?_)
    (A.hamming_one_vanishing.const_mul 2)
  show hammingDistance (A.model n) (v n * A.map n 1) (A.map n 1 * v n) ≤
    2 * hammingDistance (A.model n) (A.map n 1) 1
  have h₁ := SequentialNormalization.hammingDistance_commutator_le_right (v n)
    (A.map n 1) 1
  have e : hammingDistance (A.model n) (v n * 1) (1 * v n) = 0 := by
    rw [mul_one, one_mul, hammingDistance_self]
  linarith

/-- Almost commutation is closed under products. -/
theorem almostCommutes_mul {v : ∀ n, Equiv.Perm (A.model n)} {g h : G}
    (hg : A.AlmostCommutes v g) (hh : A.AlmostCommutes v h) :
    A.AlmostCommutes v (g * h) := by
  unfold SoficApproximation.AlmostCommutes at hg hh ⊢
  refine Vanishing.squeeze (fun _ ↦ hammingDistance_nonnegative _ _ _) (fun n ↦ ?_)
    ((hg.add hh).add ((A.hamming_mul_vanishing g h).const_mul 2))
  show hammingDistance (A.model n) (v n * A.map n (g * h)) (A.map n (g * h) * v n) ≤
    hammingDistance (A.model n) (v n * A.map n g) (A.map n g * v n) +
      hammingDistance (A.model n) (v n * A.map n h) (A.map n h * v n) +
      2 * hammingDistance (A.model n) (A.map n (g * h)) (A.map n g * A.map n h)
  have h₁ := SequentialNormalization.hammingDistance_commutator_le_right (v n)
    (A.map n (g * h)) (A.map n g * A.map n h)
  have h₂ := hammingDistance_triangle (A.model n) (v n * (A.map n g * A.map n h))
    (A.map n g * v n * A.map n h) (A.map n g * A.map n h * v n)
  have e₁ : hammingDistance (A.model n) (v n * (A.map n g * A.map n h))
      (A.map n g * v n * A.map n h) =
      hammingDistance (A.model n) (v n * A.map n g) (A.map n g * v n) := by
    rw [← mul_assoc]
    exact hammingDistance_right_invariant _ _ _ _
  have e₂ : hammingDistance (A.model n) (A.map n g * v n * A.map n h)
      (A.map n g * A.map n h * v n) =
      hammingDistance (A.model n) (v n * A.map n h) (A.map n h * v n) := by
    rw [mul_assoc, mul_assoc]
    exact hammingDistance_left_invariant _ _ _ _
  linarith

/-- Almost commutation is closed under inverses. -/
theorem almostCommutes_inv {v : ∀ n, Equiv.Perm (A.model n)} {g : G}
    (hg : A.AlmostCommutes v g) : A.AlmostCommutes v g⁻¹ := by
  unfold SoficApproximation.AlmostCommutes at hg ⊢
  refine Vanishing.squeeze (fun _ ↦ hammingDistance_nonnegative _ _ _) (fun n ↦ ?_)
    (hg.add ((A.hamming_inv_vanishing g).const_mul 2))
  show hammingDistance (A.model n) (v n * A.map n g⁻¹) (A.map n g⁻¹ * v n) ≤
    hammingDistance (A.model n) (v n * A.map n g) (A.map n g * v n) +
      2 * hammingDistance (A.model n) (A.map n g⁻¹) (A.map n g)⁻¹
  have h₁ := SequentialNormalization.hammingDistance_commutator_le_right (v n)
    (A.map n g⁻¹) (A.map n g)⁻¹
  have e : hammingDistance (A.model n) (v n * (A.map n g)⁻¹) ((A.map n g)⁻¹ * v n) =
      hammingDistance (A.model n) (v n * A.map n g) (A.map n g * v n) := by
    have e₁ : hammingDistance (A.model n)
        (A.map n g * (v n * (A.map n g)⁻¹) * A.map n g)
        (A.map n g * ((A.map n g)⁻¹ * v n) * A.map n g) =
        hammingDistance (A.model n) (v n * (A.map n g)⁻¹) ((A.map n g)⁻¹ * v n) := by
      rw [hammingDistance_right_invariant, hammingDistance_left_invariant]
    have e₂ : A.map n g * (v n * (A.map n g)⁻¹) * A.map n g = A.map n g * v n := by
      group
    have e₃ : A.map n g * ((A.map n g)⁻¹ * v n) * A.map n g = v n * A.map n g := by
      group
    rw [e₂, e₃] at e₁
    rw [← e₁]
    exact hammingDistance_comm _ _ _
  linarith

/-- **Almost commutation with generators gives almost commutation with the
subgroup.**  If a sequence almost commutes with the model of every element of
a generating set of `Γ`, it almost commutes with the model of every element of
`Γ`. -/
theorem almostCommutes_of_generators {Γ : Subgroup G} {v : ∀ n, Equiv.Perm (A.model n)}
    (SΓ : Finset ↥Γ) (hgen : Subgroup.closure (SΓ : Set ↥Γ) = ⊤)
    (hS : ∀ s ∈ SΓ, A.AlmostCommutes v (s : G)) :
    ∀ γ ∈ Γ, A.AlmostCommutes v γ := by
  intro γ hγ
  have hx : (⟨γ, hγ⟩ : ↥Γ) ∈ Subgroup.closure (SΓ : Set ↥Γ) := by
    rw [hgen]
    exact Subgroup.mem_top _
  have key : ∀ x : ↥Γ, x ∈ Subgroup.closure (SΓ : Set ↥Γ) →
      A.AlmostCommutes v (x : G) := by
    intro x hx'
    induction hx' using Subgroup.closure_induction with
    | mem y hy => exact hS y (Finset.mem_coe.mp hy)
    | one => exact A.almostCommutes_one
    | mul y z _ _ hy hz => exact A.almostCommutes_mul hy hz
    | inv y _ hy => exact A.almostCommutes_inv hy
  exact key ⟨γ, hγ⟩ hx

end SoficApproximation

end GroupApproximation
