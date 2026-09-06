import GroupApproximation.CharClass.CartanFreeCxAug

/-!
# The tensor product of two contractible complexes is contractible

This is the engine of the acyclicity half of the Cartan comparison.  Given
augmented contractions of `A` and of `B`, the operator `s ⊗ 1 + π ⊗ s` of
`CartanFreeCxAug.lean` contracts `A ⊗ B`.

Two cancellations carry the proof, and both are characteristic two.  In
first-factor degree at least one, the term `s x ⊗ ∂ y` appears once from
`∂ ∘ S` and once from `S ∘ ∂`, and they add to zero.  In first-factor degree
zero the same happens, and in addition the residue `π x ⊗ s ∂ y` appears twice.
Nothing here is a sign cancellation: over `F₂` there are no signs to begin with.

Because the tensor is again a complex of free `F₂`-modules with a degreewise
index, the construction iterates.  The fourfold object of the Cartan comparison
is the tensor of the pair with itself, and its contraction is this theorem
applied twice.

## Main results

* `tensorFreeCx` — the tensor product, as a `FreeCx`.
* `tensorAug` — **an augmented contraction of the tensor product.**
* `tensorD_exists_preimage` — positive-degree cycles are boundaries.
-/

namespace GroupApproximation.CharClass

noncomputable section

variable {A B : FreeCx} (cA : AugContraction A) (cB : AugContraction B)

/-! ## 1. Characteristic-two bookkeeping -/

theorem eq_add_of_add_eq_zmod2 {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    {x y w : M} (h : x + y = w) : x = w + y := by
  calc x = x + (y + y) := by rw [add_self_eq_zero_zmod2, add_zero]
    _ = x + y + y := by abel
    _ = w + y := by rw [h]

theorem add_shuffle_cancel {M : Type} [AddCommGroup M] [Module (ZMod 2) M] (T P X : M) :
    T + X + P + X = T + P := by
  have h : T + X + P + X = T + P + (X + X) := by abel
  rw [h, add_self_eq_zero_zmod2, add_zero]

theorem add_shuffle_cancel_two {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (T P Q : M) : T + P + (P + Q) = T + Q := by
  have h : T + P + (P + Q) = T + (P + P) + Q := by abel
  rw [h, add_self_eq_zero_zmod2, add_zero]

theorem add_shuffle_cancel_four {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (T P E G : M) : T + P + E + (0 + (P + G)) + 0 + (E + G) = T := by
  have h : T + P + E + (0 + (P + G)) + 0 + (E + G) = T + (P + P) + (E + E) + (G + G) := by
    abel
  rw [h, add_self_eq_zero_zmod2, add_self_eq_zero_zmod2, add_self_eq_zero_zmod2,
    add_zero, add_zero, add_zero]

/-! ## 2. The contraction identity -/

/-- **The contraction identity on a decomposable element.** -/
theorem tensorD_tsB_add (k a b : ℕ) (h : a + b = k + 1)
    (u : A.ι a →₀ ZMod 2) (v : B.ι b →₀ ZMod 2) :
    tensorD A B (k + 1) (tsB cA cB (k + 1) a b h u v)
      + tsL cA cB k (tdL A B k a b h u v)
      + tsL cA cB k (tdR A B k a b h u v)
      = tenElt A B (⟨(a, b), h⟩ : Steenrod.PairDeg (k + 1)) u v := by
  cases a with
  | succ a' =>
      have hP : a' + 1 + b = k + 1 := h
      have e1 : tensorD A B (k + 1) (tsB cA cB (k + 1) (a' + 1) b h u v)
          = tenElt A B (⟨(a' + 1, b), hP⟩ : Steenrod.PairDeg (k + 1))
              (A.d (a' + 1) (cA.s (a' + 1) u)) v
            + tdR A B (k + 1) (a' + 2) b (by omega) (cA.s (a' + 1) u) v := by
        rw [tsB_succ, tensorD_tenElt, tdL_succ]
      have e2 : tsL cA cB k (tdL A B k (a' + 1) b h u v)
          = tenElt A B (⟨(a' + 1, b), hP⟩ : Steenrod.PairDeg (k + 1))
              (cA.s a' (A.d a' u)) v := by
        rw [tdL_succ, tsL_tenElt]
        cases a' with
        | zero =>
            rw [tsB_zero, cA.pi_d, tenElt_zero_left]
            exact add_zero _
        | succ a'' => exact tsB_succ cA cB k a'' b (by omega) (A.d (a'' + 1) u) v
      have e3 : tsL cA cB k (tdR A B k (a' + 1) b h u v)
          = tdR A B (k + 1) (a' + 2) b (by omega) (cA.s (a' + 1) u) v := by
        cases b with
        | zero => rw [tdR_zero, map_zero, tdR_zero]
        | succ b' => rw [tdR_succ, tsL_tenElt, tsB_succ, tdR_succ]
      have hcomb := tenElt_add_left A B (⟨(a' + 1, b), hP⟩ : Steenrod.PairDeg (k + 1))
        (A.d (a' + 1) (cA.s (a' + 1) u)) (cA.s a' (A.d a' u)) v
      rw [cA.succ a' u] at hcomb
      rw [e1, e2, e3]
      exact (add_shuffle_cancel _ _ _).trans hcomb.symm
  | zero =>
      cases b with
      | zero => exact absurd h (by omega)
      | succ b' =>
          have hP : 0 + (b' + 1) = k + 1 := h
          have e1 : tensorD A B (k + 1) (tsB cA cB (k + 1) 0 (b' + 1) h u v)
              = tenElt A B (⟨(0, b' + 1), hP⟩ : Steenrod.PairDeg (k + 1))
                    (A.d 0 (cA.s 0 u)) v
                + tenElt A B (⟨(1, b'), by omega⟩ : Steenrod.PairDeg (k + 1))
                    (cA.s 0 u) (B.d b' v)
                + (0 + tenElt A B (⟨(0, b' + 1), hP⟩ : Steenrod.PairDeg (k + 1))
                    (cA.π u) (B.d (b' + 1) (cB.s (b' + 1) v))) := by
            rw [tsB_zero, map_add, tensorD_tenElt, tensorD_tenElt, tdL_succ, tdR_succ,
              tdL_zero, tdR_succ]
          have e2 : tsL cA cB k (tdL A B k 0 (b' + 1) h u v) = 0 := by
            rw [tdL_zero, map_zero]
          have e3 : tsL cA cB k (tdR A B k 0 (b' + 1) h u v)
              = tenElt A B (⟨(1, b'), by omega⟩ : Steenrod.PairDeg (k + 1))
                    (cA.s 0 u) (B.d b' v)
                + tenElt A B (⟨(0, b' + 1), hP⟩ : Steenrod.PairDeg (k + 1))
                    (cA.π u) (cB.s b' (B.d b' v)) := by
            rw [tdR_succ, tsL_tenElt, tsB_zero]
          have hB : B.d (b' + 1) (cB.s (b' + 1) v) = v + cB.s b' (B.d b' v) :=
            eq_add_of_add_eq_zmod2 (cB.succ b' v)
          have hD : tenElt A B (⟨(0, b' + 1), hP⟩ : Steenrod.PairDeg (k + 1))
                (A.d 0 (cA.s 0 u)) v
              = tenElt A B (⟨(0, b' + 1), hP⟩ : Steenrod.PairDeg (k + 1)) u v
                + tenElt A B (⟨(0, b' + 1), hP⟩ : Steenrod.PairDeg (k + 1)) (cA.π u) v := by
            rw [cA.zero u, tenElt_add_left]
          have hF : tenElt A B (⟨(0, b' + 1), hP⟩ : Steenrod.PairDeg (k + 1))
                (cA.π u) (B.d (b' + 1) (cB.s (b' + 1) v))
              = tenElt A B (⟨(0, b' + 1), hP⟩ : Steenrod.PairDeg (k + 1)) (cA.π u) v
                + tenElt A B (⟨(0, b' + 1), hP⟩ : Steenrod.PairDeg (k + 1))
                    (cA.π u) (cB.s b' (B.d b' v)) := by
            rw [hB, tenElt_add_right]
          rw [e1, e2, e3, hD, hF]
          exact add_shuffle_cancel_four _ _ _ _

/-! ## 3. The contraction -/

/-- The tensor product, as a complex of free `F₂`-modules. -/
noncomputable abbrev tensorFreeCx (A B : FreeCx) : FreeCx where
  ι := TensorIdx A B
  d := tensorD A B
  d_d := tensorD_tensorD A B

/-- The residue of the tensor contraction in degree zero, on a decomposable
element: the product of the two residues. -/
noncomputable def tsPiB : ∀ (a b : ℕ), a + b = 0 → (A.ι a →₀ ZMod 2) → (B.ι b →₀ ZMod 2) →
    (TensorIdx A B 0 →₀ ZMod 2)
  | 0, 0, h, u, v => tenElt A B (⟨(0, 0), h⟩ : Steenrod.PairDeg 0) (cA.π u) (cB.π v)
  | 0, _ + 1, h, _, _ => absurd h (by omega)
  | _ + 1, _, h, _, _ => absurd h (by omega)

theorem tsPiB_zero_zero (h : 0 + 0 = 0) (u : A.ι 0 →₀ ZMod 2) (v : B.ι 0 →₀ ZMod 2) :
    tsPiB cA cB 0 0 h u v
      = tenElt A B (⟨(0, 0), h⟩ : Steenrod.PairDeg 0) (cA.π u) (cB.π v) := rfl

theorem tsPiB_zero_left (a b : ℕ) (h : a + b = 0) (v : B.ι b →₀ ZMod 2) :
    tsPiB cA cB a b h 0 v = 0 := by
  have ha : a = 0 := by omega
  have hb : b = 0 := by omega
  subst ha
  subst hb
  rw [tsPiB_zero_zero, map_zero, tenElt_zero_left]

theorem tsPiB_add_left (a b : ℕ) (h : a + b = 0) (u u' : A.ι a →₀ ZMod 2)
    (v : B.ι b →₀ ZMod 2) :
    tsPiB cA cB a b h (u + u') v = tsPiB cA cB a b h u v + tsPiB cA cB a b h u' v := by
  have ha : a = 0 := by omega
  have hb : b = 0 := by omega
  subst ha
  subst hb
  rw [tsPiB_zero_zero, tsPiB_zero_zero, tsPiB_zero_zero, map_add,
      tenElt_add_left]

theorem tsPiB_smul_left (a b : ℕ) (h : a + b = 0) (c : ZMod 2) (u : A.ι a →₀ ZMod 2)
    (v : B.ι b →₀ ZMod 2) :
    tsPiB cA cB a b h (c • u) v = c • tsPiB cA cB a b h u v := by
  have ha : a = 0 := by omega
  have hb : b = 0 := by omega
  subst ha
  subst hb
  rw [tsPiB_zero_zero, tsPiB_zero_zero, map_smul, tenElt_smul_left]

theorem tsPiB_zero_right (a b : ℕ) (h : a + b = 0) (u : A.ι a →₀ ZMod 2) :
    tsPiB cA cB a b h u 0 = 0 := by
  have ha : a = 0 := by omega
  have hb : b = 0 := by omega
  subst ha
  subst hb
  rw [tsPiB_zero_zero, map_zero, tenElt_zero_right]

theorem tsPiB_add_right (a b : ℕ) (h : a + b = 0) (u : A.ι a →₀ ZMod 2)
    (v v' : B.ι b →₀ ZMod 2) :
    tsPiB cA cB a b h u (v + v') = tsPiB cA cB a b h u v + tsPiB cA cB a b h u v' := by
  have ha : a = 0 := by omega
  have hb : b = 0 := by omega
  subst ha
  subst hb
  rw [tsPiB_zero_zero, tsPiB_zero_zero, tsPiB_zero_zero, map_add,
      tenElt_add_right]

theorem tsPiB_smul_right (a b : ℕ) (h : a + b = 0) (c : ZMod 2) (u : A.ι a →₀ ZMod 2)
    (v : B.ι b →₀ ZMod 2) :
    tsPiB cA cB a b h u (c • v) = c • tsPiB cA cB a b h u v := by
  have ha : a = 0 := by omega
  have hb : b = 0 := by omega
  subst ha
  subst hb
  rw [tsPiB_zero_zero, tsPiB_zero_zero, map_smul, tenElt_smul_right]

/-- The residue of the tensor contraction. -/
noncomputable def tsPi : (TensorIdx A B 0 →₀ ZMod 2) →ₗ[ZMod 2] (TensorIdx A B 0 →₀ ZMod 2) :=
  Finsupp.linearCombination (ZMod 2) (fun q =>
    tsPiB cA cB q.1.val.1 q.1.val.2 q.1.property
      (Finsupp.single q.2.1 1) (Finsupp.single q.2.2 1))

@[simp] theorem tsPi_single (q : TensorIdx A B 0) (c : ZMod 2) :
    tsPi cA cB (Finsupp.single q c)
      = c • tsPiB cA cB q.1.val.1 q.1.val.2 q.1.property
          (Finsupp.single q.2.1 1) (Finsupp.single q.2.2 1) := by
  unfold tsPi
  rw [Finsupp.linearCombination_single]

theorem tsPi_tenElt (a b : ℕ) (h : a + b = 0) (u : A.ι a →₀ ZMod 2) (v : B.ι b →₀ ZMod 2) :
    tsPi cA cB (tenElt A B (⟨(a, b), h⟩ : Steenrod.PairDeg 0) u v)
      = tsPiB cA cB a b h u v := by
  induction u using Finsupp.induction_linear with
  | zero => rw [tenElt_zero_left, map_zero, tsPiB_zero_left]
  | add f g hf hg => rw [tenElt_add_left, map_add, hf, hg, tsPiB_add_left]
  | single x c =>
      induction v using Finsupp.induction_linear with
      | zero => rw [tenElt_zero_right, map_zero, tsPiB_zero_right]
      | add f g hf hg => rw [tenElt_add_right, map_add, hf, hg, tsPiB_add_right]
      | single y e =>
          have hc : (Finsupp.single x c : A.ι a →₀ ZMod 2)
              = c • Finsupp.single x (1 : ZMod 2) := by
            rw [Finsupp.smul_single, smul_eq_mul, mul_one]
          have he : (Finsupp.single y e : B.ι b →₀ ZMod 2)
              = e • Finsupp.single y (1 : ZMod 2) := by
            rw [Finsupp.smul_single, smul_eq_mul, mul_one]
          rw [hc, he, tenElt_smul_left, tenElt_smul_right, tenElt_single_single,
            map_smul, map_smul, tsPi_single, one_smul,
            tsPiB_smul_left, tsPiB_smul_right]

/-- The contraction identity in degree zero, on a decomposable element. -/
theorem tensorD_tsB_zero (a b : ℕ) (h : a + b = 0)
    (u : A.ι a →₀ ZMod 2) (v : B.ι b →₀ ZMod 2) :
    tensorD A B 0 (tsB cA cB 0 a b h u v)
      = tenElt A B (⟨(a, b), h⟩ : Steenrod.PairDeg 0) u v + tsPiB cA cB a b h u v := by
  have ha : a = 0 := by omega
  have hb : b = 0 := by omega
  subst ha
  subst hb
  have e1 : tensorD A B 0 (tsB cA cB 0 0 0 h u v)
          = (tenElt A B (⟨(0, 0), h⟩ : Steenrod.PairDeg 0) (A.d 0 (cA.s 0 u)) v + 0)
            + (0 + tenElt A B (⟨(0, 0), h⟩ : Steenrod.PairDeg 0)
                (cA.π u) (B.d 0 (cB.s 0 v))) := by
        rw [tsB_zero, map_add, tensorD_tenElt, tensorD_tenElt, tdL_succ, tdR_zero,
          tdL_zero, tdR_succ]
  rw [e1, cA.zero u, cB.zero v, tenElt_add_left, tenElt_add_right,
    tsPiB_zero_zero, add_zero, zero_add]
  exact add_shuffle_cancel_two _ _ _

/-! ## 4. The three identities, and the contraction -/

/-- **The contraction identity in positive degrees.** -/
theorem tensorD_tsL_add (k : ℕ) (z : TensorIdx A B (k + 1) →₀ ZMod 2) :
    tensorD A B (k + 1) (tsL cA cB (k + 1) z) + tsL cA cB k (tensorD A B k z) = z := by
  induction z using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero, map_zero, add_zero]
  | add f g hf hg =>
      rw [map_add, map_add, map_add, map_add,
        show tensorD A B (k + 1) (tsL cA cB (k + 1) f)
              + tensorD A B (k + 1) (tsL cA cB (k + 1) g)
              + (tsL cA cB k (tensorD A B k f) + tsL cA cB k (tensorD A B k g))
            = (tensorD A B (k + 1) (tsL cA cB (k + 1) f) + tsL cA cB k (tensorD A B k f))
              + (tensorD A B (k + 1) (tsL cA cB (k + 1) g)
                + tsL cA cB k (tensorD A B k g)) from by abel, hf, hg]
  | single q c =>
      obtain ⟨⟨⟨a, b⟩, hab⟩, x, y⟩ := q
      have hsingle : (Finsupp.single (⟨⟨(a, b), hab⟩, (x, y)⟩ : TensorIdx A B (k + 1)) c)
          = c • tenElt A B (⟨(a, b), hab⟩ : Steenrod.PairDeg (k + 1))
              (Finsupp.single x 1) (Finsupp.single y 1) := by
        rw [tenElt_single_single, Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hsingle, map_smul, map_smul, map_smul, map_smul, tsL_tenElt,
        tensorD_tenElt, map_add, ← smul_add, ← add_assoc,
        tensorD_tsB_add cA cB k a b hab (Finsupp.single x 1) (Finsupp.single y 1)]

/-- **The contraction identity in degree zero.** -/
theorem tensorD_tsL_zero (z : TensorIdx A B 0 →₀ ZMod 2) :
    tensorD A B 0 (tsL cA cB 0 z) = z + tsPi cA cB z := by
  induction z using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero, add_zero]
  | add f g hf hg =>
      rw [map_add, map_add, map_add, hf, hg]
      abel
  | single q c =>
      obtain ⟨⟨⟨a, b⟩, hab⟩, x, y⟩ := q
      have hsingle : (Finsupp.single (⟨⟨(a, b), hab⟩, (x, y)⟩ : TensorIdx A B 0) c)
          = c • tenElt A B (⟨(a, b), hab⟩ : Steenrod.PairDeg 0)
              (Finsupp.single x 1) (Finsupp.single y 1) := by
        rw [tenElt_single_single, Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hsingle, map_smul, map_smul, map_smul, tsL_tenElt, tsPi_tenElt,
        tensorD_tsB_zero cA cB a b hab (Finsupp.single x 1) (Finsupp.single y 1),
        smul_add]

/-- **The residue kills the boundaries.** -/
theorem tsPi_tensorD (z : TensorIdx A B 1 →₀ ZMod 2) :
    tsPi cA cB (tensorD A B 0 z) = 0 := by
  induction z using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add f g hf hg => rw [map_add, map_add, hf, hg, add_zero]
  | single q c =>
      obtain ⟨⟨⟨a, b⟩, hab⟩, x, y⟩ := q
      have hsingle : (Finsupp.single (⟨⟨(a, b), hab⟩, (x, y)⟩ : TensorIdx A B 1) c)
          = c • tenElt A B (⟨(a, b), hab⟩ : Steenrod.PairDeg 1)
              (Finsupp.single x 1) (Finsupp.single y 1) := by
        rw [tenElt_single_single, Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hsingle, map_smul, map_smul, tensorD_tenElt, map_add]
      have hab' : a + b = 1 := hab
      have hcase : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by omega
      rcases hcase with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · subst ha
        subst hb
        rw [tdL_zero, tdR_succ, map_zero, zero_add, tsPi_tenElt, tsPiB_zero_zero,
          cB.pi_d, tenElt_zero_right, smul_zero]
      · subst ha
        subst hb
        rw [tdR_zero, tdL_succ, map_zero, add_zero, tsPi_tenElt, tsPiB_zero_zero,
          cA.pi_d, tenElt_zero_left, smul_zero]

/-- **An augmented contraction of the tensor product.** -/
noncomputable def tensorAug (cA : AugContraction A) (cB : AugContraction B) :
    AugContraction (tensorFreeCx A B) where
  s k := tsL cA cB k
  π := tsPi cA cB
  succ k z := tensorD_tsL_add cA cB k z
  zero z := tensorD_tsL_zero cA cB z
  pi_d z := tsPi_tensorD cA cB z

/-! ## 5. Acyclicity -/

/-- **Positive-degree cycles in the tensor product are boundaries.** -/
theorem tensorD_exists_preimage (cA : AugContraction A) (cB : AugContraction B)
    (k : ℕ) (y : TensorIdx A B (k + 1) →₀ ZMod 2) (hy : tensorD A B k y = 0) :
    ∃ z : TensorIdx A B (k + 2) →₀ ZMod 2, tensorD A B (k + 1) z = y := by
  refine ⟨tsL cA cB (k + 1) y, ?_⟩
  have h2 := tensorD_tsL_add cA cB k y
  rw [hy, map_zero, add_zero] at h2
  exact h2

end

end GroupApproximation.CharClass
