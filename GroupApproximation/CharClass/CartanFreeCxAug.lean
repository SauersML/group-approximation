import GroupApproximation.CharClass.CartanFreeCx

/-!
# Augmented contractions, and the contraction of a tensor product

A complex is acyclic in positive degrees exactly when it carries a contracting
homotopy, and over a field one always can be chosen.  What the tensor product
needs is slightly more than that: the degree-zero identity has to be recorded
too, with an idempotent `π` in place of the naive augmentation, because the
degree-zero residue of the tensor is the product of the two residues.

This file sets up that data and the operator it induces on the tensor.  The
formula is the classical `s ⊗ 1 + π ⊗ s`, with the second summand present only
in first-factor degree zero.

## Main results

* `AugContraction` — the data: `s`, `π`, and the three identities.
* `tsB` — the induced operator on a decomposable element.
* `tsL` — the induced operator, linearly.
* `tsL_tenElt` — `tsL` on a decomposable element, in closed form.
-/

namespace GroupApproximation.CharClass

noncomputable section

/-! ## 1. The data -/

/-- **An augmented contraction** of a free `F₂`-complex: a contracting homotopy
in positive degrees, together with the degree-zero residue `π`.  In
characteristic two `1 - π` and `1 + π` agree, which is why the identities read
with a plus. -/
structure AugContraction (A : FreeCx) where
  /-- The contracting operator. -/
  s : ∀ k : ℕ, (A.ι k →₀ ZMod 2) →ₗ[ZMod 2] (A.ι (k + 1) →₀ ZMod 2)
  /-- The degree-zero residue. -/
  π : (A.ι 0 →₀ ZMod 2) →ₗ[ZMod 2] (A.ι 0 →₀ ZMod 2)
  /-- The contraction identity in positive degrees. -/
  succ : ∀ (k : ℕ) (u : A.ι (k + 1) →₀ ZMod 2),
    A.d (k + 1) (s (k + 1) u) + s k (A.d k u) = u
  /-- The contraction identity in degree zero. -/
  zero : ∀ u : A.ι 0 →₀ ZMod 2, A.d 0 (s 0 u) = u + π u
  /-- The residue kills the boundaries. -/
  pi_d : ∀ u : A.ι 1 →₀ ZMod 2, π (A.d 0 u) = 0

/-! ## 2. The induced operator on decomposables -/

variable {A B : FreeCx}

/-- The tensor contraction on a decomposable element: `s ⊗ 1` always, plus
`π ⊗ s` when the first degree is zero. -/
noncomputable def tsB (cA : AugContraction A) (cB : AugContraction B) (k : ℕ) :
    ∀ (a b : ℕ), a + b = k → (A.ι a →₀ ZMod 2) → (B.ι b →₀ ZMod 2) →
      (TensorIdx A B (k + 1) →₀ ZMod 2)
  | 0, b, h, u, v =>
      tenElt A B (⟨(1, b), by omega⟩ : Steenrod.PairDeg (k + 1)) (cA.s 0 u) v
        + tenElt A B (⟨(0, b + 1), by omega⟩ : Steenrod.PairDeg (k + 1))
            (cA.π u) (cB.s b v)
  | a' + 1, b, h, u, v =>
      tenElt A B (⟨(a' + 2, b), by omega⟩ : Steenrod.PairDeg (k + 1))
        (cA.s (a' + 1) u) v

variable (cA : AugContraction A) (cB : AugContraction B)

theorem tsB_zero (k b : ℕ) (h : 0 + b = k) (u : A.ι 0 →₀ ZMod 2) (v : B.ι b →₀ ZMod 2) :
    tsB cA cB k 0 b h u v
      = tenElt A B (⟨(1, b), by omega⟩ : Steenrod.PairDeg (k + 1)) (cA.s 0 u) v
        + tenElt A B (⟨(0, b + 1), by omega⟩ : Steenrod.PairDeg (k + 1))
            (cA.π u) (cB.s b v) := rfl

theorem tsB_succ (k a' b : ℕ) (h : a' + 1 + b = k) (u : A.ι (a' + 1) →₀ ZMod 2)
    (v : B.ι b →₀ ZMod 2) :
    tsB cA cB k (a' + 1) b h u v
      = tenElt A B (⟨(a' + 2, b), by omega⟩ : Steenrod.PairDeg (k + 1))
          (cA.s (a' + 1) u) v := rfl

/-! ### Bilinearity -/

theorem tsB_zero_left (k a b : ℕ) (h : a + b = k) (v : B.ι b →₀ ZMod 2) :
    tsB cA cB k a b h 0 v = 0 := by
  cases a with
  | zero => rw [tsB_zero, map_zero, map_zero, tenElt_zero_left, tenElt_zero_left, add_zero]
  | succ a' => rw [tsB_succ, map_zero, tenElt_zero_left]

theorem tsB_add_left (k a b : ℕ) (h : a + b = k) (u u' : A.ι a →₀ ZMod 2)
    (v : B.ι b →₀ ZMod 2) :
    tsB cA cB k a b h (u + u') v = tsB cA cB k a b h u v + tsB cA cB k a b h u' v := by
  cases a with
  | zero =>
      rw [tsB_zero, tsB_zero, tsB_zero, map_add, map_add, tenElt_add_left, tenElt_add_left]
      abel
  | succ a' => rw [tsB_succ, tsB_succ, tsB_succ, map_add, tenElt_add_left]

theorem tsB_smul_left (k a b : ℕ) (h : a + b = k) (c : ZMod 2) (u : A.ι a →₀ ZMod 2)
    (v : B.ι b →₀ ZMod 2) :
    tsB cA cB k a b h (c • u) v = c • tsB cA cB k a b h u v := by
  cases a with
  | zero =>
      rw [tsB_zero, tsB_zero, map_smul, map_smul, tenElt_smul_left, tenElt_smul_left,
        smul_add]
  | succ a' => rw [tsB_succ, tsB_succ, map_smul, tenElt_smul_left]

theorem tsB_zero_right (k a b : ℕ) (h : a + b = k) (u : A.ι a →₀ ZMod 2) :
    tsB cA cB k a b h u 0 = 0 := by
  cases a with
  | zero =>
      rw [tsB_zero, tenElt_zero_right, map_zero, tenElt_zero_right, add_zero]
  | succ a' => rw [tsB_succ, tenElt_zero_right]

theorem tsB_add_right (k a b : ℕ) (h : a + b = k) (u : A.ι a →₀ ZMod 2)
    (v v' : B.ι b →₀ ZMod 2) :
    tsB cA cB k a b h u (v + v') = tsB cA cB k a b h u v + tsB cA cB k a b h u v' := by
  cases a with
  | zero =>
      rw [tsB_zero, tsB_zero, tsB_zero, tenElt_add_right, map_add, tenElt_add_right]
      abel
  | succ a' => rw [tsB_succ, tsB_succ, tsB_succ, tenElt_add_right]

theorem tsB_smul_right (k a b : ℕ) (h : a + b = k) (c : ZMod 2) (u : A.ι a →₀ ZMod 2)
    (v : B.ι b →₀ ZMod 2) :
    tsB cA cB k a b h u (c • v) = c • tsB cA cB k a b h u v := by
  cases a with
  | zero =>
      rw [tsB_zero, tsB_zero, tenElt_smul_right, map_smul, tenElt_smul_right, smul_add]
  | succ a' => rw [tsB_succ, tsB_succ, tenElt_smul_right]

/-! ## 3. The induced operator -/

/-- The tensor contraction on a basis element. -/
noncomputable def tsGen (k : ℕ) (q : TensorIdx A B k) : TensorIdx A B (k + 1) →₀ ZMod 2 :=
  tsB cA cB k q.1.val.1 q.1.val.2 q.1.property
    (Finsupp.single q.2.1 1) (Finsupp.single q.2.2 1)

/-- **The tensor contraction.** -/
noncomputable def tsL (k : ℕ) :
    (TensorIdx A B k →₀ ZMod 2) →ₗ[ZMod 2] (TensorIdx A B (k + 1) →₀ ZMod 2) :=
  Finsupp.linearCombination (ZMod 2) (tsGen cA cB k)

@[simp] theorem tsL_single (k : ℕ) (q : TensorIdx A B k) (c : ZMod 2) :
    tsL cA cB k (Finsupp.single q c) = c • tsGen cA cB k q := by
  unfold tsL
  rw [Finsupp.linearCombination_single]

/-- **The tensor contraction on a decomposable element**, in closed form. -/
theorem tsL_tenElt (k a b : ℕ) (h : a + b = k)
    (u : A.ι a →₀ ZMod 2) (v : B.ι b →₀ ZMod 2) :
    tsL cA cB k (tenElt A B (⟨(a, b), h⟩ : Steenrod.PairDeg k) u v)
      = tsB cA cB k a b h u v := by
  induction u using Finsupp.induction_linear with
  | zero => rw [tenElt_zero_left, map_zero, tsB_zero_left]
  | add f g hf hg =>
      rw [tenElt_add_left, map_add, hf, hg, tsB_add_left]
  | single x c =>
      induction v using Finsupp.induction_linear with
      | zero => rw [tenElt_zero_right, map_zero, tsB_zero_right]
      | add f g hf hg =>
          rw [tenElt_add_right, map_add, hf, hg, tsB_add_right]
      | single y e =>
          have hq : tsGen cA cB k (⟨⟨(a, b), h⟩, (x, y)⟩ : TensorIdx A B k)
              = tsB cA cB k a b h (Finsupp.single x 1) (Finsupp.single y 1) := rfl
          have hc : (Finsupp.single x c : A.ι a →₀ ZMod 2)
              = c • Finsupp.single x (1 : ZMod 2) := by
            rw [Finsupp.smul_single, smul_eq_mul, mul_one]
          have he : (Finsupp.single y e : B.ι b →₀ ZMod 2)
              = e • Finsupp.single y (1 : ZMod 2) := by
            rw [Finsupp.smul_single, smul_eq_mul, mul_one]
          rw [hc, he, tenElt_smul_left, tenElt_smul_right, tenElt_single_single,
            map_smul, map_smul, tsL_single, one_smul, hq,
            tsB_smul_left, tsB_smul_right]

end

end GroupApproximation.CharClass
