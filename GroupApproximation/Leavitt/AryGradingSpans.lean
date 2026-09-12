import GroupApproximation.Leavitt.AryDegreeZeroUnits
import GroupApproximation.Meta.AxiomGuard

/-!
# Graded spans and the elementary corner move at arbitrary arity

`Leavitt/LeavittGradingSpans.lean` is the groundwork for the Laurent half of the
rose-graph `K₁` computation, over a **binary** Leavitt family.  This module is
the same groundwork over a `CompleteMatrixFamily A ι`:

* `levelMonomialSet_eq` --- the balanced monomials in length form;
* `span_levelMonomialSet_mono` --- padding by `1 = ∑ᵢ sᵢtᵢ` embeds depth `m` in
  depth `n` for `m ≤ n`;
* `monomial_factor_left` / `monomial_factor_right` --- a monomial sheds one
  letter off either end;
* `exists_corner_move` --- the elementary corner move inside the unit group.

## The one place the arity is visible, and how it is handled

The binary proof of the corner move writes the complementary projection
`1 - s₀t₀` as `s₁t₁`, which is true only when there are exactly two indices.
Nothing in the argument needs that identification: every step uses only

* `t_{i₁} (1 - s_{i₀} t_{i₀}) = t_{i₁}`  and  `(1 - s_{i₀} t_{i₀}) s_{i₁} = s_{i₁}`,

which follow from `t_{i₁} s_{i₀} = 0` and `t_{i₀} s_{i₁} = 0` at any arity.  So
the complementary projection is kept abstract, and the conclusion carries
`1 - s_{i₀} t_{i₀}` where the binary one carries `s₁t₁`.

## What is deliberately **not** ported

`LeavittBalancedUnits.centralClassGroup_le_stableUnits` --- central units are
stably elementary --- is **false at arity `d ≥ 3`**, and so is
`mem_stableUnits_of_val_mem_levelSpan`.  The binary proof writes a central `c`
as a product of *two* corner insertions, each congruent to `c`, so `[c] = [c]²`
and `[c] = 1`.  At arity `d` the same argument gives `[c] = [c]^d`, i.e.
`[c]^{d-1} = 1` and no more --- which is exactly
`AlgebraicK.kappa_central_pow_card_sub_one`, and exactly why
`K₁(L_k(1,d)) = k^×/(k^×)^{d-1}` is nontrivial.  The correct receptacle at
arity `d` is `centralClassGroup`, which is what
`AryDegreeZeroUnits.mem_centralClassGroup_of_val_mem_levelSpan` lands in.
-/

namespace GroupApproximation
namespace CompleteMatrixFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : CompleteMatrixFamily A ι)

/-! ### Balanced spans in length form -/

/-- Length-based description of the balanced monomials. -/
theorem levelMonomialSet_eq (n : ℕ) :
    F.levelMonomialSet n = {x | ∃ a b : List ι,
      a.length = n ∧ b.length = n ∧ x = F.wordS a * F.wordT b} := by
  ext x
  constructor
  · rintro ⟨f, g, rfl⟩
    exact ⟨List.ofFn f, List.ofFn g, by simp, by simp, rfl⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    subst ha
    refine ⟨fun i ↦ a[i], fun i ↦ b[i]'(by rw [hb]; exact i.isLt), ?_⟩
    have hofa : List.ofFn (fun i : Fin a.length ↦ a[i]) = a := by
      apply List.ext_getElem <;> simp
    have hofb : List.ofFn (fun i : Fin a.length ↦
        b[i]'(by rw [hb]; exact i.isLt)) = b := by
      apply List.ext_getElem
      · simp [hb]
      · intro i h1 h2
        simp
    rw [hofa, hofb]

section Scalars

variable {k : Type*} [CommRing k] [Algebra k A]

/-- Balanced monomials are balanced values. -/
theorem monomial_mem_span_levelMonomialSet (n : ℕ) {a b : List ι}
    (ha : a.length = n) (hb : b.length = n) :
    F.wordS a * F.wordT b ∈ Submodule.span k (F.levelMonomialSet n) := by
  refine Submodule.subset_span ?_
  rw [levelMonomialSet_eq]
  exact ⟨a, b, ha, hb, rfl⟩

/-- Padding: the balanced span at depth `n` sits inside depth `n + 1`, by
inserting `1 = ∑ᵢ sᵢtᵢ` between the words. -/
theorem span_levelMonomialSet_le_succ (n : ℕ) :
    Submodule.span k (F.levelMonomialSet n) ≤
      Submodule.span k (F.levelMonomialSet (n + 1)) := by
  rw [Submodule.span_le]
  intro x hx
  rw [levelMonomialSet_eq] at hx
  obtain ⟨a, b, ha, hb, rfl⟩ := hx
  rw [F.wordS_mul_wordT_split a b]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  exact F.monomial_mem_span_levelMonomialSet (k := k) (n + 1)
    (by simp [ha]) (by simp [hb])

theorem span_levelMonomialSet_mono {m n : ℕ} (h : m ≤ n) :
    Submodule.span k (F.levelMonomialSet m) ≤
      Submodule.span k (F.levelMonomialSet n) := by
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact ih.trans (F.span_levelMonomialSet_le_succ n)

/-- The identity is a balanced value at every depth. -/
theorem one_mem_span_levelMonomialSet (n : ℕ) :
    (1 : A) ∈ Submodule.span k (F.levelMonomialSet n) := by
  rw [← F.sum_cylinder_ofFn n]
  refine Submodule.sum_mem _ fun f _ ↦ Submodule.subset_span ?_
  exact ⟨f, f, rfl⟩

end Scalars

/-! ### Shedding a letter -/

/-- A monomial sheds one `s_{i₀}` on the right:
`s_α t_β = (s_α t_{i₀::β}) · s_{i₀}`. -/
theorem monomial_factor_left (i₀ : ι) (a b : List ι) :
    F.wordS a * F.wordT b = (F.wordS a * F.wordT (i₀ :: b)) * F.left i₀ := by
  rw [F.wordT_cons]
  have ht : F.wordT b * F.right i₀ * F.left i₀ = F.wordT b := by
    rw [mul_assoc, F.orthogonal i₀ i₀, if_pos rfl, mul_one]
  rw [mul_assoc, mul_assoc, ← mul_assoc (F.wordT b), ht]

/-- A monomial sheds one `t_{i₀}` on the left:
`s_α t_β = t_{i₀} · (s_{i₀::α} t_β)`. -/
theorem monomial_factor_right (i₀ : ι) (a b : List ι) :
    F.wordS a * F.wordT b = F.right i₀ * (F.wordS (i₀ :: a) * F.wordT b) := by
  rw [F.wordS_cons, ← mul_assoc, ← mul_assoc, F.orthogonal i₀ i₀,
    if_pos rfl, one_mul]

/-! ### The elementary corner move -/

/-- **The elementary corner move inside the unit group**, at arbitrary arity:
for every unit `u`, all `v, w` and any two distinct indices, the element

`s_{i₀}(u + vw)t_{i₀} + s_{i₀}v t_{i₁} + s_{i₁}w t_{i₀} + (1 - s_{i₀}t_{i₀})`

is a unit congruent to `u` modulo the stably elementary units.  It is the
depth-one corner picture of `[[1,v],[0,1]] · diag(u,1) · [[1,0],[w,1]]`, with
the complementary corner left as the projection `1 - s_{i₀}t_{i₀}` rather than
identified with a single cylinder. -/
theorem exists_corner_move [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    {i₀ i₁ : ι} (hne : i₀ ≠ i₁) (u : Aˣ) (v w : A) :
    ∃ u' : Aˣ, (u' : A) =
      F.left i₀ * ((u : A) + v * w) * F.right i₀ +
        F.left i₀ * v * F.right i₁ + F.left i₁ * w * F.right i₀ +
        (1 - F.left i₀ * F.right i₀) ∧
      u' * u⁻¹ ∈ stableUnits A := by
  have hts : F.right i₀ * F.left i₀ = 1 := by
    rw [F.orthogonal i₀ i₀, if_pos rfl]
  have ht1s0 : F.right i₁ * F.left i₀ = 0 := by
    rw [F.orthogonal i₁ i₀, if_neg (Ne.symm hne)]
  have ht0s1 : F.right i₀ * F.left i₁ = 0 := by
    rw [F.orthogonal i₀ i₁, if_neg hne]
  have ht1s1 : F.right i₁ * F.left i₁ = 1 := by
    rw [F.orthogonal i₁ i₁, if_pos rfl]
  -- the complementary projection, kept abstract
  have hpt1 : F.right i₁ * (1 - F.left i₀ * F.right i₀) = F.right i₁ := by
    rw [mul_sub, mul_one, ← mul_assoc, ht1s0, zero_mul, sub_zero]
  have hps1 : (1 - F.left i₀ * F.right i₀) * F.left i₁ = F.left i₁ := by
    rw [sub_mul, one_mul, mul_assoc, ht0s1, mul_zero, sub_zero]
  have hzX : F.left i₀ * v * F.right i₁ * (F.left i₀ * v * F.right i₁) = 0 := by
    rw [show F.left i₀ * v * F.right i₁ * (F.left i₀ * v * F.right i₁) =
      F.left i₀ * v * (F.right i₁ * F.left i₀) * (v * F.right i₁) from by
        noncomm_ring, ht1s0]
    noncomm_ring
  have hzY : F.left i₁ * w * F.right i₀ * (F.left i₁ * w * F.right i₀) = 0 := by
    rw [show F.left i₁ * w * F.right i₀ * (F.left i₁ * w * F.right i₀) =
      F.left i₁ * w * (F.right i₀ * F.left i₁) * (w * F.right i₀) from by
        noncomm_ring, ht0s1]
    noncomm_ring
  let X : Aˣ :=
    ⟨1 + F.left i₀ * v * F.right i₁, 1 - F.left i₀ * v * F.right i₁,
      by
        calc (1 + F.left i₀ * v * F.right i₁) *
              (1 - F.left i₀ * v * F.right i₁)
            = 1 - F.left i₀ * v * F.right i₁ *
                (F.left i₀ * v * F.right i₁) := by noncomm_ring
          _ = 1 := by rw [hzX, sub_zero],
      by
        calc (1 - F.left i₀ * v * F.right i₁) *
              (1 + F.left i₀ * v * F.right i₁)
            = 1 - F.left i₀ * v * F.right i₁ *
                (F.left i₀ * v * F.right i₁) := by noncomm_ring
          _ = 1 := by rw [hzX, sub_zero]⟩
  let Y : Aˣ :=
    ⟨1 + F.left i₁ * w * F.right i₀, 1 - F.left i₁ * w * F.right i₀,
      by
        calc (1 + F.left i₁ * w * F.right i₀) *
              (1 - F.left i₁ * w * F.right i₀)
            = 1 - F.left i₁ * w * F.right i₀ *
                (F.left i₁ * w * F.right i₀) := by noncomm_ring
          _ = 1 := by rw [hzY, sub_zero],
      by
        calc (1 - F.left i₁ * w * F.right i₀) *
              (1 + F.left i₁ * w * F.right i₀)
            = 1 - F.left i₁ * w * F.right i₀ *
                (F.left i₁ * w * F.right i₀) := by noncomm_ring
          _ = 1 := by rw [hzY, sub_zero]⟩
  set κ : Aˣ := pairKappaUnit (F.left i₀) (F.right i₀) hts u with hκ
  refine ⟨X * κ * Y, ?_, ?_⟩
  · have hκval : (κ : A) =
        F.left i₀ * (u : A) * F.right i₀ +
          (1 - F.left i₀ * F.right i₀) := by
      rw [hκ, pairKappaUnit_val]
    have h1 : F.left i₀ * v * F.right i₁ *
        (F.left i₀ * (u : A) * F.right i₀) = 0 := by
      rw [show F.left i₀ * v * F.right i₁ *
          (F.left i₀ * (u : A) * F.right i₀) =
        F.left i₀ * v * (F.right i₁ * F.left i₀) *
          ((u : A) * F.right i₀) from by noncomm_ring, ht1s0]
      noncomm_ring
    have h2 : F.left i₀ * v * F.right i₁ * (1 - F.left i₀ * F.right i₀) =
        F.left i₀ * v * F.right i₁ := by
      rw [show F.left i₀ * v * F.right i₁ * (1 - F.left i₀ * F.right i₀) =
        F.left i₀ * v * (F.right i₁ * (1 - F.left i₀ * F.right i₀)) from by
          noncomm_ring, hpt1]
    have h3 : F.left i₀ * (u : A) * F.right i₀ *
        (F.left i₁ * w * F.right i₀) = 0 := by
      rw [show F.left i₀ * (u : A) * F.right i₀ *
          (F.left i₁ * w * F.right i₀) =
        F.left i₀ * (u : A) * (F.right i₀ * F.left i₁) *
          (w * F.right i₀) from by noncomm_ring, ht0s1]
      noncomm_ring
    have h4 : (1 - F.left i₀ * F.right i₀) * (F.left i₁ * w * F.right i₀) =
        F.left i₁ * w * F.right i₀ := by
      rw [← mul_assoc, ← mul_assoc, hps1]
    have h5 : F.left i₀ * v * F.right i₁ * (F.left i₁ * w * F.right i₀) =
        F.left i₀ * (v * w) * F.right i₀ := by
      rw [show F.left i₀ * v * F.right i₁ * (F.left i₁ * w * F.right i₀) =
        F.left i₀ * v * (F.right i₁ * F.left i₁) * (w * F.right i₀) from by
          noncomm_ring, ht1s1]
      noncomm_ring
    show ((X : A) * (κ : A)) * (Y : A) = _
    rw [hκval]
    calc ((1 + F.left i₀ * v * F.right i₁) *
          (F.left i₀ * (u : A) * F.right i₀ +
            (1 - F.left i₀ * F.right i₀))) *
          (1 + F.left i₁ * w * F.right i₀)
        = (F.left i₀ * (u : A) * F.right i₀ +
            (1 - F.left i₀ * F.right i₀) +
            (F.left i₀ * v * F.right i₁ *
                (F.left i₀ * (u : A) * F.right i₀) +
              F.left i₀ * v * F.right i₁ *
                (1 - F.left i₀ * F.right i₀))) *
            (1 + F.left i₁ * w * F.right i₀) := by noncomm_ring
      _ = (F.left i₀ * (u : A) * F.right i₀ +
            (1 - F.left i₀ * F.right i₀) + F.left i₀ * v * F.right i₁) *
            (1 + F.left i₁ * w * F.right i₀) := by rw [h1, h2, zero_add]
      _ = F.left i₀ * (u : A) * F.right i₀ +
            (1 - F.left i₀ * F.right i₀) + F.left i₀ * v * F.right i₁ +
            (F.left i₀ * (u : A) * F.right i₀ *
                (F.left i₁ * w * F.right i₀) +
              ((1 - F.left i₀ * F.right i₀) *
                  (F.left i₁ * w * F.right i₀) +
                F.left i₀ * v * F.right i₁ *
                  (F.left i₁ * w * F.right i₀))) := by noncomm_ring
      _ = F.left i₀ * (u : A) * F.right i₀ +
            (1 - F.left i₀ * F.right i₀) + F.left i₀ * v * F.right i₁ +
            (0 + (F.left i₁ * w * F.right i₀ +
              F.left i₀ * (v * w) * F.right i₀)) := by rw [h3, h4, h5]
      _ = F.left i₀ * ((u : A) + v * w) * F.right i₀ +
            F.left i₀ * v * F.right i₁ + F.left i₁ * w * F.right i₀ +
            (1 - F.left i₀ * F.right i₀) := by noncomm_ring
  · have hXm : X ∈ stableUnits A :=
      mem_stableUnits_of_val_unipotent (F.left i₀ * v) (F.right i₁)
        (by rw [← mul_assoc, ht1s0, zero_mul])
        (by show (1 : A) + F.left i₀ * v * F.right i₁ = 1 + _; rw [mul_assoc])
    have hYm : Y ∈ stableUnits A :=
      mem_stableUnits_of_val_unipotent (F.left i₁ * w) (F.right i₀)
        (by rw [← mul_assoc, ht0s1, zero_mul])
        (by show (1 : A) + F.left i₁ * w * F.right i₀ = 1 + _; rw [mul_assoc])
    have hκm : κ * u⁻¹ ∈ stableUnits A :=
      pairKappaUnit_mul_inv_mem_stableUnits (F.left i₀) (F.right i₀) hts hdiv u
    have hconj : (u * Y * u⁻¹ : Aˣ) ∈ stableUnits A :=
      (stableUnits_normal (R := A)).conj_mem Y hYm u
    have hrw : X * κ * Y * u⁻¹ = X * ((κ * u⁻¹) * (u * Y * u⁻¹)) := by group
    rw [hrw]
    exact mul_mem hXm (mul_mem hκm hconj)

end CompleteMatrixFamily
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.CompleteMatrixFamily.levelMonomialSet_eq
#audit_axioms GroupApproximation.CompleteMatrixFamily.span_levelMonomialSet_mono
#audit_axioms GroupApproximation.CompleteMatrixFamily.one_mem_span_levelMonomialSet
#audit_axioms GroupApproximation.CompleteMatrixFamily.monomial_factor_left
#audit_axioms GroupApproximation.CompleteMatrixFamily.monomial_factor_right
#audit_axioms GroupApproximation.CompleteMatrixFamily.exists_corner_move
