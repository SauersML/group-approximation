import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Order.Basic

/-!
# Sequential colimits of towers of groups

Topological `K_1` of a unital C-star algebra is a colimit

    K_1(A) = colim_n U(M_n(A)) / U_0(M_n(A))

along the block inclusions `u ↦ diag (u, 1)`.  Mathlib has direct limits of modules and of
commutative rings, but nothing for a tower of (possibly non-abelian) groups, so this file
supplies exactly that much: a `GroupTower` is a functor from the poset of natural numbers into
groups, and `Colim` is its colimit, built as the quotient of the disjoint union of the levels
by eventual agreement.

The construction is deliberately small.  The only facts about `Colim` used downstream are

* `GroupTower.instGroup`: it is a group;
* `GroupTower.iota`: each level maps into it;
* `GroupTower.iota_map`: those maps are compatible with the tower;
* `GroupTower.exists_mkAt`: every element comes from some level;
* `GroupTower.commGroup_of_forall_commute`: level-wise eventual commutativity makes it abelian.

Nothing here is specific to C-star algebras.
-/

namespace GroupApproximation

universe u

/-- A tower of groups indexed by the natural numbers: a group at each level, together with
transition homomorphisms `map h : G n → G m` for `h : n ≤ m` which compose correctly.  This is a
functor from the poset `ℕ` into groups, written out by hand so that no category theory is
needed. -/
structure GroupTower (G : ℕ → Type u) [∀ n, Group (G n)] where
  /-- The transition homomorphism from level `n` to level `m`. -/
  map : ∀ {n m : ℕ}, n ≤ m → G n →* G m
  /-- The transition homomorphism from a level to itself is the identity. -/
  map_self : ∀ {n : ℕ} (h : n ≤ n) (x : G n), map h x = x
  /-- Transition homomorphisms compose. -/
  map_trans : ∀ {n m k : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ k) (x : G n),
      map h₂ (map h₁ x) = map (h₁.trans h₂) x

namespace GroupTower

variable {G : ℕ → Type u} [∀ n, Group (G n)] (T : GroupTower G)

/-- Two elements of the disjoint union of the levels are related when they already agree at
some common later level. -/
def Rel (x y : Σ n, G n) : Prop :=
  ∃ (k : ℕ) (hx : x.1 ≤ k) (hy : y.1 ≤ k), T.map hx x.2 = T.map hy y.2

variable {T}

/-- Agreement at one level propagates to every later level. -/
theorem agree_mono {x y : Σ n, G n} {k l : ℕ} (hx : x.1 ≤ k) (hy : y.1 ≤ k)
    (h : T.map hx x.2 = T.map hy y.2) (hkl : k ≤ l) (hx' : x.1 ≤ l) (hy' : y.1 ≤ l) :
    T.map hx' x.2 = T.map hy' y.2 := by
  have e₁ : T.map hx' x.2 = T.map hkl (T.map hx x.2) := (T.map_trans hx hkl x.2).symm
  have e₂ : T.map hy' y.2 = T.map hkl (T.map hy y.2) := (T.map_trans hy hkl y.2).symm
  rw [e₁, e₂, h]

theorem rel_refl (x : Σ n, G n) : T.Rel x x := ⟨x.1, le_rfl, le_rfl, rfl⟩

theorem rel_symm {x y : Σ n, G n} (h : T.Rel x y) : T.Rel y x := by
  obtain ⟨k, hx, hy, e⟩ := h
  exact ⟨k, hy, hx, e.symm⟩

theorem rel_trans {x y z : Σ n, G n} (h₁ : T.Rel x y) (h₂ : T.Rel y z) : T.Rel x z := by
  obtain ⟨k, hx, hy, e⟩ := h₁
  obtain ⟨l, hy', hz, e'⟩ := h₂
  refine ⟨max k l, hx.trans (le_max_left k l), hz.trans (le_max_right k l), ?_⟩
  have E := agree_mono hx hy e (le_max_left k l)
    (hx.trans (le_max_left k l)) (hy.trans (le_max_left k l))
  have E' := agree_mono hy' hz e' (le_max_right k l)
    (hy'.trans (le_max_right k l)) (hz.trans (le_max_right k l))
  exact E.trans E'

variable (T)

/-- The eventual-agreement setoid on the disjoint union of the levels. -/
def setoid : Setoid (Σ n, G n) where
  r := T.Rel
  iseqv := ⟨fun x => rel_refl x, fun h => rel_symm h, fun h₁ h₂ => rel_trans h₁ h₂⟩

/-- The colimit of a tower of groups. -/
def Colim : Type u := Quotient T.setoid

/-- The class in the colimit of an element of level `n`. -/
def mkAt (n : ℕ) (x : G n) : T.Colim := Quotient.mk T.setoid ⟨n, x⟩

theorem mkAt_eq_mkAt {n m k : ℕ} {x : G n} {y : G m} (hx : n ≤ k) (hy : m ≤ k)
    (h : T.map hx x = T.map hy y) : T.mkAt n x = T.mkAt m y :=
  Quotient.sound ⟨k, hx, hy, h⟩

@[simp] theorem mkAt_map {n m : ℕ} (h : n ≤ m) (x : G n) :
    T.mkAt m (T.map h x) = T.mkAt n x :=
  T.mkAt_eq_mkAt le_rfl h (T.map_self le_rfl _)

theorem exists_mkAt (a : T.Colim) : ∃ (n : ℕ) (x : G n), a = T.mkAt n x :=
  Quotient.inductionOn a fun x => ⟨x.1, x.2, rfl⟩

/-- Multiplication of representatives, carried out at the larger of the two levels. -/
def mulAux (x y : Σ n, G n) : Σ n, G n :=
  ⟨max x.1 y.1, T.map (le_max_left x.1 y.1) x.2 * T.map (le_max_right x.1 y.1) y.2⟩

variable {T}

theorem mulAux_rel {x x' y y' : Σ n, G n} (hx : T.Rel x x') (hy : T.Rel y y') :
    T.Rel (T.mulAux x y) (T.mulAux x' y') := by
  obtain ⟨k, hxk, hxk', ex⟩ := hx
  obtain ⟨l, hyl, hyl', ey⟩ := hy
  obtain ⟨K, hkK, hlK, hxK, hyK, hxK', hyK'⟩ :
      ∃ K : ℕ, k ≤ K ∧ l ≤ K ∧ x.1 ≤ K ∧ y.1 ≤ K ∧ x'.1 ≤ K ∧ y'.1 ≤ K :=
    ⟨k + l + x.1 + y.1 + x'.1 + y'.1,
      by omega, by omega, by omega, by omega, by omega, by omega⟩
  have Ex : T.map ((le_max_left x.1 y.1).trans (max_le hxK hyK)) x.2
      = T.map ((le_max_left x'.1 y'.1).trans (max_le hxK' hyK')) x'.2 :=
    agree_mono hxk hxk' ex hkK _ _
  have Ey : T.map ((le_max_right x.1 y.1).trans (max_le hxK hyK)) y.2
      = T.map ((le_max_right x'.1 y'.1).trans (max_le hxK' hyK')) y'.2 :=
    agree_mono hyl hyl' ey hlK _ _
  refine ⟨K, max_le hxK hyK, max_le hxK' hyK', ?_⟩
  show T.map (max_le hxK hyK)
        (T.map (le_max_left x.1 y.1) x.2 * T.map (le_max_right x.1 y.1) y.2)
      = T.map (max_le hxK' hyK')
        (T.map (le_max_left x'.1 y'.1) x'.2 * T.map (le_max_right x'.1 y'.1) y'.2)
  rw [map_mul, map_mul, T.map_trans, T.map_trans, T.map_trans, T.map_trans, Ex, Ey]

variable (T)

instance instMul : Mul T.Colim :=
  ⟨fun a b => Quotient.liftOn₂ a b (fun x y => Quotient.mk T.setoid (T.mulAux x y))
    (fun _ _ _ _ h₁ h₂ => Quotient.sound (mulAux_rel h₁ h₂))⟩

instance instOne : One T.Colim := ⟨T.mkAt 0 1⟩

instance instInv : Inv T.Colim :=
  ⟨fun a => Quotient.liftOn a (fun x => Quotient.mk T.setoid ⟨x.1, x.2⁻¹⟩)
    (fun _ _ h => Quotient.sound (by
      obtain ⟨k, hx, hy, e⟩ := h
      exact ⟨k, hx, hy, by simpa only [map_inv] using congrArg (·⁻¹) e⟩))⟩

/-- Multiplication in the colimit may be computed at any common level. -/
theorem mkAt_mul_mkAt {n m k : ℕ} (x : G n) (y : G m) (hx : n ≤ k) (hy : m ≤ k) :
    T.mkAt n x * T.mkAt m y = T.mkAt k (T.map hx x * T.map hy y) := by
  show Quotient.mk T.setoid (T.mulAux ⟨n, x⟩ ⟨m, y⟩) = T.mkAt k (T.map hx x * T.map hy y)
  refine Quotient.sound ⟨k, max_le hx hy, le_rfl, ?_⟩
  show T.map (max_le hx hy) (T.map (le_max_left n m) x * T.map (le_max_right n m) y)
      = T.map le_rfl (T.map hx x * T.map hy y)
  simp only [map_mul, T.map_trans, T.map_self]

@[simp] theorem mkAt_one (n : ℕ) : T.mkAt n (1 : G n) = 1 :=
  T.mkAt_eq_mkAt (k := n) le_rfl (Nat.zero_le n) (by rw [map_one, map_one])

@[simp] theorem mkAt_inv (n : ℕ) (x : G n) : (T.mkAt n x)⁻¹ = T.mkAt n x⁻¹ := rfl

instance instGroup : Group T.Colim where
  mul := (· * ·)
  one := 1
  inv := (·⁻¹)
  mul_assoc a b c := by
    obtain ⟨n, x, rfl⟩ := T.exists_mkAt a
    obtain ⟨m, y, rfl⟩ := T.exists_mkAt b
    obtain ⟨p, z, rfl⟩ := T.exists_mkAt c
    have hn : n ≤ max (max n m) p := (le_max_left n m).trans (le_max_left _ _)
    have hm : m ≤ max (max n m) p := (le_max_right n m).trans (le_max_left _ _)
    have hp : p ≤ max (max n m) p := le_max_right _ _
    rw [T.mkAt_mul_mkAt x y hn hm, T.mkAt_mul_mkAt _ z le_rfl hp, T.mkAt_mul_mkAt y z hm hp,
      T.mkAt_mul_mkAt x _ hn le_rfl, T.map_self, T.map_self, mul_assoc]
  one_mul a := by
    obtain ⟨n, x, rfl⟩ := T.exists_mkAt a
    show T.mkAt 0 1 * T.mkAt n x = _
    rw [T.mkAt_mul_mkAt (1 : G 0) x (Nat.zero_le n) le_rfl, map_one, T.map_self, one_mul]
  mul_one a := by
    obtain ⟨n, x, rfl⟩ := T.exists_mkAt a
    show T.mkAt n x * T.mkAt 0 1 = _
    rw [T.mkAt_mul_mkAt x (1 : G 0) le_rfl (Nat.zero_le n), map_one, T.map_self, mul_one]
  inv_mul_cancel a := by
    obtain ⟨n, x, rfl⟩ := T.exists_mkAt a
    rw [T.mkAt_inv, T.mkAt_mul_mkAt x⁻¹ x le_rfl le_rfl, T.map_self, T.map_self,
      inv_mul_cancel, T.mkAt_one]

/-- The canonical homomorphism from level `n` into the colimit. -/
def iota (n : ℕ) : G n →* T.Colim where
  toFun := T.mkAt n
  map_one' := T.mkAt_one n
  map_mul' x y := by rw [T.mkAt_mul_mkAt x y le_rfl le_rfl, T.map_self, T.map_self]

@[simp] theorem iota_apply (n : ℕ) (x : G n) : T.iota n x = T.mkAt n x := rfl

@[simp] theorem iota_map {n m : ℕ} (h : n ≤ m) (x : G n) : T.iota m (T.map h x) = T.iota n x :=
  T.mkAt_map h x

theorem exists_iota (a : T.Colim) : ∃ (n : ℕ) (x : G n), a = T.iota n x := T.exists_mkAt a

/-- If, at every level, the images of `x * y` and `y * x` already agree in the colimit, then the
colimit is commutative. -/
theorem commGroup_of_forall_commute
    (h : ∀ (n : ℕ) (x y : G n), T.iota n (x * y) = T.iota n (y * x)) :
    ∀ a b : T.Colim, a * b = b * a := by
  intro a b
  obtain ⟨n, x, rfl⟩ := T.exists_mkAt a
  obtain ⟨m, y, rfl⟩ := T.exists_mkAt b
  have hn : n ≤ max n m := le_max_left n m
  have hm : m ≤ max n m := le_max_right n m
  rw [T.mkAt_mul_mkAt x y hn hm, T.mkAt_mul_mkAt y x hm hn]
  exact h (max n m) (T.map hn x) (T.map hm y)

end GroupTower

end GroupApproximation
