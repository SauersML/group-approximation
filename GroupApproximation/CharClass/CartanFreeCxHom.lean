import GroupApproximation.CharClass.CartanFreeCxSwap

/-!
# Chain maps of free `F₂`-complexes, and their tensor product

The two composites of the internal Cartan comparison are built from tensor
products of chain maps: `Φ₀ ⊗ Φ₀` on the outside of one and `Φ ⊗ Φ` inside the
other.  This file supplies the operation once, for the degreewise-indexed
complexes of `CartanFreeCx.lean`.

The construction is easier than the differential was, because no dependent match
is needed: on a basis element of the tensor the map is `φ` applied in the first
degree and `ψ` in the second, and the degrees themselves do not move.

## Main results

* `FreeCxHom` — a chain map, degreewise, over `F₂`.
* `tenHom` — the tensor product of two chain maps.
* `tenHom_tensorD` — **the tensor of two chain maps is a chain map.**
* `tenHom_id`, `tenHom_comp` — functoriality.
* `tenHom_tenSwap` — the tensor of a chain map with itself commutes with the
  factor swap, so it is linear over the group ring.
-/

namespace GroupApproximation.CharClass

noncomputable section

/-! ## 1. Chain maps -/

/-- A chain map of complexes of free `F₂`-modules. -/
structure FreeCxHom (A B : FreeCx) where
  /-- The degreewise components. -/
  f : ∀ k : ℕ, (A.ι k →₀ ZMod 2) →ₗ[ZMod 2] (B.ι k →₀ ZMod 2)
  /-- Compatibility with the differentials. -/
  comm : ∀ (k : ℕ) (u : A.ι (k + 1) →₀ ZMod 2), f k (A.d k u) = B.d k (f (k + 1) u)

/-- The identity chain map. -/
def FreeCxHom.id (A : FreeCx) : FreeCxHom A A where
  f _ := LinearMap.id
  comm _ _ := rfl

/-- Composition of chain maps. -/
def FreeCxHom.comp {A B C : FreeCx} (ψ : FreeCxHom B C) (φ : FreeCxHom A B) :
    FreeCxHom A C where
  f k := (ψ.f k).comp (φ.f k)
  comm k u := by
    show ψ.f k (φ.f k (A.d k u)) = C.d k (ψ.f (k + 1) (φ.f (k + 1) u))
    rw [φ.comm k u, ψ.comm k (φ.f (k + 1) u)]

/-! ## 2. The tensor product of two chain maps -/

variable {A A' B B' : FreeCx} (φ : FreeCxHom A B) (ψ : FreeCxHom A' B')

/-- The tensor product on a basis element. -/
noncomputable def tenHomGen (k : ℕ) (q : TensorIdx A A' k) : TensorIdx B B' k →₀ ZMod 2 :=
  tenElt B B' q.1 (φ.f q.1.val.1 (Finsupp.single q.2.1 1))
    (ψ.f q.1.val.2 (Finsupp.single q.2.2 1))

/-- **The tensor product of two chain maps.** -/
noncomputable def tenHom (k : ℕ) :
    (TensorIdx A A' k →₀ ZMod 2) →ₗ[ZMod 2] (TensorIdx B B' k →₀ ZMod 2) :=
  Finsupp.linearCombination (ZMod 2) (tenHomGen φ ψ k)

@[simp] theorem tenHom_single (k : ℕ) (q : TensorIdx A A' k) (c : ZMod 2) :
    tenHom φ ψ k (Finsupp.single q c) = c • tenHomGen φ ψ k q := by
  unfold tenHom
  rw [Finsupp.linearCombination_single]

/-- **The tensor product on a decomposable element.** -/
theorem tenHom_tenElt (k a b : ℕ) (h : a + b = k)
    (u : A.ι a →₀ ZMod 2) (v : A'.ι b →₀ ZMod 2) :
    tenHom φ ψ k (tenElt A A' (⟨(a, b), h⟩ : Steenrod.PairDeg k) u v)
      = tenElt B B' (⟨(a, b), h⟩ : Steenrod.PairDeg k) (φ.f a u) (ψ.f b v) := by
  induction u using Finsupp.induction_linear with
  | zero => rw [tenElt_zero_left, map_zero, map_zero, tenElt_zero_left]
  | add p q hp hq =>
      rw [tenElt_add_left, map_add, hp, hq, map_add, tenElt_add_left]
  | single x c =>
      induction v using Finsupp.induction_linear with
      | zero => rw [tenElt_zero_right, map_zero, map_zero, tenElt_zero_right]
      | add p q hp hq =>
          rw [tenElt_add_right, map_add, hp, hq, map_add, tenElt_add_right]
      | single y e =>
          have hq : tenHomGen φ ψ k (⟨⟨(a, b), h⟩, (x, y)⟩ : TensorIdx A A' k)
              = tenElt B B' (⟨(a, b), h⟩ : Steenrod.PairDeg k)
                  (φ.f a (Finsupp.single x 1)) (ψ.f b (Finsupp.single y 1)) := rfl
          have hc : (Finsupp.single x c : A.ι a →₀ ZMod 2)
              = c • Finsupp.single x (1 : ZMod 2) := by
            rw [Finsupp.smul_single, smul_eq_mul, mul_one]
          have he : (Finsupp.single y e : A'.ι b →₀ ZMod 2)
              = e • Finsupp.single y (1 : ZMod 2) := by
            rw [Finsupp.smul_single, smul_eq_mul, mul_one]
          rw [hc, he, tenElt_smul_left, tenElt_smul_right, tenElt_single_single,
            map_smul, map_smul, tenHom_single, one_smul, hq,
            map_smul, map_smul, tenElt_smul_left, tenElt_smul_right]

/-! ## 3. The tensor of two chain maps is a chain map -/

theorem tenHom_tdL (k a b : ℕ) (h : a + b = k + 1)
    (u : A.ι a →₀ ZMod 2) (v : A'.ι b →₀ ZMod 2) :
    tenHom φ ψ k (tdL A A' k a b h u v) = tdL B B' k a b h (φ.f a u) (ψ.f b v) := by
  cases a with
  | zero => rw [tdL_zero, tdL_zero, map_zero]
  | succ a' =>
      rw [tdL_succ, tdL_succ, tenHom_tenElt, φ.comm]

theorem tenHom_tdR (k a b : ℕ) (h : a + b = k + 1)
    (u : A.ι a →₀ ZMod 2) (v : A'.ι b →₀ ZMod 2) :
    tenHom φ ψ k (tdR A A' k a b h u v) = tdR B B' k a b h (φ.f a u) (ψ.f b v) := by
  cases b with
  | zero => rw [tdR_zero, tdR_zero, map_zero]
  | succ b' =>
      rw [tdR_succ, tdR_succ, tenHom_tenElt, ψ.comm]

/-- **The tensor of two chain maps is a chain map.** -/
theorem tenHom_tensorD (k : ℕ) (y : TensorIdx A A' (k + 1) →₀ ZMod 2) :
    tenHom φ ψ k (tensorD A A' k y) = tensorD B B' k (tenHom φ ψ (k + 1) y) := by
  induction y using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]
  | single q c =>
      obtain ⟨⟨⟨a, b⟩, hab⟩, x, y⟩ := q
      have hs : (Finsupp.single (⟨⟨(a, b), hab⟩, (x, y)⟩ : TensorIdx A A' (k + 1)) c)
          = c • tenElt A A' (⟨(a, b), hab⟩ : Steenrod.PairDeg (k + 1))
              (Finsupp.single x 1) (Finsupp.single y 1) := by
        rw [tenElt_single_single, Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hs, map_smul, map_smul, map_smul, map_smul, tensorD_tenElt, map_add,
        tenHom_tdL, tenHom_tdR, tenHom_tenElt, tensorD_tenElt]

/-! ## 4. Functoriality -/

theorem tenHom_id (A A' : FreeCx) (k : ℕ) (y : TensorIdx A A' k →₀ ZMod 2) :
    tenHom (FreeCxHom.id A) (FreeCxHom.id A') k y = y := by
  induction y using Finsupp.induction_linear with
  | zero => rw [map_zero]
  | add p q hp hq => rw [map_add, hp, hq]
  | single q c =>
      obtain ⟨p, x, y⟩ := q
      rw [tenHom_single]
      show c • tenElt A A' p (Finsupp.single x 1) (Finsupp.single y 1) = _
      rw [tenElt_single_single, Finsupp.smul_single, smul_eq_mul, mul_one]

theorem tenHom_comp {C C' : FreeCx} (φ' : FreeCxHom B C) (ψ' : FreeCxHom B' C')
    (k : ℕ) (y : TensorIdx A A' k →₀ ZMod 2) :
    tenHom (φ'.comp φ) (ψ'.comp ψ) k y = tenHom φ' ψ' k (tenHom φ ψ k y) := by
  induction y using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | single q c =>
      obtain ⟨⟨⟨a, b⟩, hab⟩, x, y⟩ := q
      have hs : (Finsupp.single (⟨⟨(a, b), hab⟩, (x, y)⟩ : TensorIdx A A' k) c)
          = c • tenElt A A' (⟨(a, b), hab⟩ : Steenrod.PairDeg k)
              (Finsupp.single x 1) (Finsupp.single y 1) := by
        rw [tenElt_single_single, Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hs, map_smul, map_smul, map_smul, tenHom_tenElt, tenHom_tenElt,
        tenHom_tenElt]
      rfl

/-! ## 5. Compatibility with the swap -/

/-- **The tensor of a chain map with itself commutes with the factor swap.** -/
theorem tenHom_tenSwap {A B : FreeCx} (φ : FreeCxHom A B) (k : ℕ)
    (y : TensorIdx A A k →₀ ZMod 2) :
    tenHom φ φ k (tenSwap A k y) = tenSwap B k (tenHom φ φ k y) := by
  induction y using Finsupp.induction_linear with
  | zero => rfl
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]
  | single q c =>
      obtain ⟨⟨⟨a, b⟩, hab⟩, x, y⟩ := q
      have hs : (Finsupp.single (⟨⟨(a, b), hab⟩, (x, y)⟩ : TensorIdx A A k) c)
          = c • tenElt A A (⟨(a, b), hab⟩ : Steenrod.PairDeg k)
              (Finsupp.single x 1) (Finsupp.single y 1) := by
        rw [tenElt_single_single, Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hs, map_smul, map_smul, map_smul, map_smul, tenHom_tenElt,
        tenSwap_tenElt A k a b hab (by omega), tenHom_tenElt,
        tenSwap_tenElt B k a b hab (by omega)]

end

end GroupApproximation.CharClass
