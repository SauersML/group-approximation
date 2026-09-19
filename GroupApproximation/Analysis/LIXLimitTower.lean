import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

/-!
# The algebraic colimit of a tower of C⋆-algebras

A **tower** of unital C⋆-algebras is a sequence `A 0, A 1, A 2, …` together with unital
⋆-homomorphisms `A n →⋆ₐ[ℂ] A (n+1)` which are *isometric* — equivalently, by
`NonUnitalStarAlgHom.norm_map`, injective.  This file builds the colimit of such a tower as a
**pre-C⋆-algebra**: the algebraic direct limit, carrying the norm `‖[a]‖ := ‖a‖`, which is well
defined and definite precisely because the connecting maps are isometric.  Completing it (in
`Analysis/LIXLimitCompletion`) produces the C⋆-algebra of the inductive system.

Mathlib has direct limits of modules and of commutative rings, and the repository has
`Analysis/SequentialGroupColimit` for towers of groups; none of them carries a norm or an
involution, so the construction is done here from scratch, following the group file's shape.

## The construction

`T.climb i k : A k → A i` is the composite of the connecting maps, defined by recursion on the
*target* index `i` so that it is a total function of `i` and `k` (junk `0` when `k > i`) in which
no proof of `k ≤ i` appears.  That is what keeps the colimit free of dependent-proof rewriting
traps: `T.climb i k` never has to be transported along a proof.

`T.Colim` is the quotient of `Σ n, A n` by "the two representatives agree after climbing to a
common level".  Every operation is computed at the larger of the two levels, and every algebraic
law is proved by moving both (or all three) arguments to one common level — `T.ind`, `T.ind₂`,
`T.ind₃` — where it becomes the corresponding law inside a single `A i`.

The main results are the instances `CStarTower.instRing`, `instNormedRing`, `instStarRing`,
`instNormedStarGroup`, `instCStarRing`, `instAlgebra`, `instNormedAlgebra`, `instStarModule` on
`T.Colim`, and the isometric unital ⋆-homomorphisms `T.iota k : A k →⋆ₐ[ℂ] T.Colim` with
`T.iota_climb : T.iota i (T.climb i k a) = T.iota k a` and `T.exists_mkAt`, which says that every
element of the colimit comes from some level.
-/

namespace GroupApproximation

namespace LIX

universe u

/-- A tower of unital C⋆-algebras: an algebra at each level and an isometric unital
⋆-homomorphism from each level to the next.  Isometry is the honest hypothesis (it is what the
colimit norm needs); `CStarTower.ofInjective` builds it from injectivity, which for
⋆-homomorphisms of C⋆-algebras is equivalent. -/
structure CStarTower (A : ℕ → Type u) [∀ n, CStarAlgebra (A n)] where
  /-- The connecting ⋆-homomorphism from one level to the next. -/
  succHom : ∀ n : ℕ, A n →⋆ₐ[ℂ] A (n + 1)
  /-- The connecting homomorphisms are isometric. -/
  norm_succHom : ∀ (n : ℕ) (a : A n), ‖succHom n a‖ = ‖a‖

namespace CStarTower

noncomputable section

variable {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)]

/-- A tower from injective connecting maps: an injective ⋆-homomorphism of C⋆-algebras is
isometric. -/
def ofInjective (φ : ∀ n : ℕ, A n →⋆ₐ[ℂ] A (n + 1))
    (hφ : ∀ n, Function.Injective (φ n)) : CStarTower A where
  succHom := φ
  norm_succHom n a := NonUnitalStarAlgHom.norm_map (φ n) (hφ n) a

/-! ### Climbing the tower -/

/-- `T.climb i k a` is the image of `a : A k` at level `i`, obtained by applying the connecting
maps `i - k` times; it is `0` when `k > i`.  Recursion is on the target index, so this is a total
function carrying no `k ≤ i` proof. -/
def climb (T : CStarTower A) : (i k : ℕ) → A k → A i
  | 0, k, a => if h : k = 0 then cast (congrArg A h) a else 0
  | i + 1, k, a =>
      if h : k = i + 1 then cast (congrArg A h) a else T.succHom i (climb T i k a)

variable (T : CStarTower A)

theorem climb_zero_eq (k : ℕ) (a : A k) :
    T.climb 0 k a = if h : k = 0 then cast (congrArg A h) a else 0 := rfl

theorem climb_succ_eq (i k : ℕ) (a : A k) :
    T.climb (i + 1) k a =
      if h : k = i + 1 then cast (congrArg A h) a else T.succHom i (T.climb i k a) := rfl

@[simp] theorem climb_self (k : ℕ) (a : A k) : T.climb k k a = a := by
  cases k with
  | zero => exact dif_pos rfl
  | succ n => exact dif_pos rfl

theorem climb_succ {i k : ℕ} (h : k ≤ i) (a : A k) :
    T.climb (i + 1) k a = T.succHom i (T.climb i k a) :=
  dif_neg (by omega)

@[simp] theorem climb_succ_self (i : ℕ) (a : A i) : T.climb (i + 1) i a = T.succHom i a := by
  rw [T.climb_succ (le_refl i), T.climb_self]

theorem climb_trans {k i j : ℕ} (hki : k ≤ i) (hij : i ≤ j) (a : A k) :
    T.climb j i (T.climb i k a) = T.climb j k a := by
  induction j, hij using Nat.le_induction with
  | base => exact T.climb_self i _
  | succ j hij ih => rw [T.climb_succ hij, ih, T.climb_succ (hki.trans hij)]

theorem climb_one {k i : ℕ} (h : k ≤ i) : T.climb i k (1 : A k) = 1 := by
  induction i, h using Nat.le_induction with
  | base => simp only [T.climb_self]
  | succ i h ih => rw [T.climb_succ h, ih, map_one]

theorem climb_zero {k i : ℕ} (h : k ≤ i) : T.climb i k (0 : A k) = 0 := by
  induction i, h using Nat.le_induction with
  | base => simp only [T.climb_self]
  | succ i h ih => rw [T.climb_succ h, ih, map_zero]

theorem climb_mul {k i : ℕ} (h : k ≤ i) (a b : A k) :
    T.climb i k (a * b) = T.climb i k a * T.climb i k b := by
  induction i, h using Nat.le_induction with
  | base => simp only [T.climb_self]
  | succ i h ih => simp only [T.climb_succ h]; rw [ih, map_mul]

theorem climb_add {k i : ℕ} (h : k ≤ i) (a b : A k) :
    T.climb i k (a + b) = T.climb i k a + T.climb i k b := by
  induction i, h using Nat.le_induction with
  | base => simp only [T.climb_self]
  | succ i h ih => simp only [T.climb_succ h]; rw [ih, map_add]

theorem climb_neg {k i : ℕ} (h : k ≤ i) (a : A k) : T.climb i k (-a) = -T.climb i k a := by
  induction i, h using Nat.le_induction with
  | base => simp only [T.climb_self]
  | succ i h ih => simp only [T.climb_succ h]; rw [ih, map_neg]

theorem climb_star {k i : ℕ} (h : k ≤ i) (a : A k) :
    T.climb i k (star a) = star (T.climb i k a) := by
  induction i, h using Nat.le_induction with
  | base => simp only [T.climb_self]
  | succ i h ih => simp only [T.climb_succ h]; rw [ih, map_star]

theorem climb_smul {k i : ℕ} (h : k ≤ i) (r : ℂ) (a : A k) :
    T.climb i k (r • a) = r • T.climb i k a := by
  induction i, h using Nat.le_induction with
  | base => simp only [T.climb_self]
  | succ i h ih => simp only [T.climb_succ h]; rw [ih, map_smul]

theorem climb_algebraMap {k i : ℕ} (h : k ≤ i) (r : ℂ) :
    T.climb i k (algebraMap ℂ (A k) r) = algebraMap ℂ (A i) r := by
  induction i, h using Nat.le_induction with
  | base => simp only [T.climb_self]
  | succ i h ih => rw [T.climb_succ h, ih, AlgHomClass.commutes]

theorem climb_norm {k i : ℕ} (h : k ≤ i) (a : A k) : ‖T.climb i k a‖ = ‖a‖ := by
  induction i, h using Nat.le_induction with
  | base => rw [T.climb_self]
  | succ i h ih => rw [T.climb_succ h, T.norm_succHom, ih]

theorem climb_injective {k i : ℕ} (h : k ≤ i) : Function.Injective (T.climb i k) := by
  intro a b hab
  have h0 : T.climb i k (a - b) = 0 := by
    rw [sub_eq_add_neg, T.climb_add h, T.climb_neg h, hab, add_neg_cancel]
  have h1 : ‖a - b‖ = 0 := by rw [← T.climb_norm h (a - b), h0, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp h1)

/-- The connecting map from level `k` to level `i`, bundled as a unital ⋆-homomorphism. -/
def climbHom {k i : ℕ} (h : k ≤ i) : A k →⋆ₐ[ℂ] A i where
  toFun := T.climb i k
  map_one' := T.climb_one h
  map_mul' := T.climb_mul h
  map_zero' := T.climb_zero h
  map_add' := T.climb_add h
  commutes' := T.climb_algebraMap h
  map_star' := T.climb_star h

@[simp] theorem climbHom_apply {k i : ℕ} (h : k ≤ i) (a : A k) :
    T.climbHom h a = T.climb i k a := rfl

/-! ### The colimit as a set -/

/-- Two representatives are related when they agree after climbing to a common level. -/
def Rel (x y : Σ n, A n) : Prop :=
  ∃ k : ℕ, x.1 ≤ k ∧ y.1 ≤ k ∧ T.climb k x.1 x.2 = T.climb k y.1 y.2

variable {T}

/-- Agreement at one level propagates to every later level. -/
theorem climb_eq_mono {x y : Σ n, A n} {k l : ℕ} (hx : x.1 ≤ k) (hy : y.1 ≤ k) (hkl : k ≤ l)
    (h : T.climb k x.1 x.2 = T.climb k y.1 y.2) :
    T.climb l x.1 x.2 = T.climb l y.1 y.2 := by
  rw [← T.climb_trans hx hkl, ← T.climb_trans hy hkl, h]

theorem rel_refl (x : Σ n, A n) : T.Rel x x := ⟨x.1, le_rfl, le_rfl, rfl⟩

theorem rel_symm {x y : Σ n, A n} (h : T.Rel x y) : T.Rel y x := by
  obtain ⟨k, hx, hy, e⟩ := h
  exact ⟨k, hy, hx, e.symm⟩

theorem rel_trans {x y z : Σ n, A n} (h₁ : T.Rel x y) (h₂ : T.Rel y z) : T.Rel x z := by
  obtain ⟨k, hx, hy, e⟩ := h₁
  obtain ⟨l, hy', hz, e'⟩ := h₂
  refine ⟨max k l, hx.trans (le_max_left k l), hz.trans (le_max_right k l), ?_⟩
  exact (climb_eq_mono hx hy (le_max_left k l) e).trans
    (climb_eq_mono hy' hz (le_max_right k l) e')

variable (T)

/-- The eventual-agreement setoid on the disjoint union of the levels. -/
def setoid : Setoid (Σ n, A n) where
  r := T.Rel
  iseqv := ⟨rel_refl, rel_symm, rel_trans⟩

/-- The algebraic colimit of a tower of C⋆-algebras. -/
def Colim : Type u := Quotient T.setoid

/-- The class in the colimit of an element of level `i`. -/
def mkAt (i : ℕ) (a : A i) : T.Colim := Quotient.mk T.setoid ⟨i, a⟩

theorem mkAt_eq_mk {i j k : ℕ} {a : A i} {b : A j} (hi : i ≤ k) (hj : j ≤ k)
    (h : T.climb k i a = T.climb k j b) : T.mkAt i a = T.mkAt j b :=
  Quotient.sound ⟨k, hi, hj, h⟩

@[simp] theorem mkAt_climb {k i : ℕ} (h : k ≤ i) (a : A k) : T.mkAt i (T.climb i k a) = T.mkAt k a :=
  T.mkAt_eq_mk le_rfl h (T.climb_self i _)

theorem exists_mkAt (z : T.Colim) : ∃ (i : ℕ) (a : A i), z = T.mkAt i a :=
  Quotient.inductionOn z fun x => ⟨x.1, x.2, rfl⟩

theorem ind {p : T.Colim → Prop} (h : ∀ (i : ℕ) (a : A i), p (T.mkAt i a)) : ∀ z, p z := by
  intro z
  obtain ⟨i, a, rfl⟩ := T.exists_mkAt z
  exact h i a

theorem ind₂ {p : T.Colim → T.Colim → Prop}
    (h : ∀ (i : ℕ) (a b : A i), p (T.mkAt i a) (T.mkAt i b)) : ∀ z w, p z w := by
  intro z w
  obtain ⟨i, a, rfl⟩ := T.exists_mkAt z
  obtain ⟨j, b, rfl⟩ := T.exists_mkAt w
  obtain ⟨K, hi, hj⟩ : ∃ K : ℕ, i ≤ K ∧ j ≤ K := ⟨i + j, by omega, by omega⟩
  have ha : T.mkAt i a = T.mkAt K (T.climb K i a) := (T.mkAt_climb hi a).symm
  have hb : T.mkAt j b = T.mkAt K (T.climb K j b) := (T.mkAt_climb hj b).symm
  rw [ha, hb]
  exact h _ _ _

theorem ind₃ {p : T.Colim → T.Colim → T.Colim → Prop}
    (h : ∀ (i : ℕ) (a b c : A i), p (T.mkAt i a) (T.mkAt i b) (T.mkAt i c)) : ∀ z w v, p z w v := by
  intro z w v
  obtain ⟨i, a, rfl⟩ := T.exists_mkAt z
  obtain ⟨j, b, rfl⟩ := T.exists_mkAt w
  obtain ⟨l, c, rfl⟩ := T.exists_mkAt v
  obtain ⟨K, hi, hj, hl⟩ : ∃ K : ℕ, i ≤ K ∧ j ≤ K ∧ l ≤ K :=
    ⟨i + j + l, by omega, by omega, by omega⟩
  have ha : T.mkAt i a = T.mkAt K (T.climb K i a) := (T.mkAt_climb hi a).symm
  have hb : T.mkAt j b = T.mkAt K (T.climb K j b) := (T.mkAt_climb hj b).symm
  have hc : T.mkAt l c = T.mkAt K (T.climb K l c) := (T.mkAt_climb hl c).symm
  rw [ha, hb, hc]
  exact h _ _ _ _

/-! ### Operations on representatives -/

/-- A binary operation on representatives, computed at the larger of the two levels. -/
def binAux (op : ∀ n : ℕ, A n → A n → A n) (x y : Σ n, A n) : Σ n, A n :=
  ⟨max x.1 y.1,
    op (max x.1 y.1) (T.climb (max x.1 y.1) x.1 x.2) (T.climb (max x.1 y.1) y.1 y.2)⟩

/-- A unary operation on representatives, computed at the level of the representative. -/
def unAux (op : ∀ n : ℕ, A n → A n) (x : Σ n, A n) : Σ n, A n := ⟨x.1, op x.1 x.2⟩

variable {T}

theorem binAux_rel (op : ∀ n : ℕ, A n → A n → A n)
    (hop : ∀ {k i : ℕ}, k ≤ i → ∀ a b : A k,
      T.climb i k (op k a b) = op i (T.climb i k a) (T.climb i k b))
    {x x' y y' : Σ n, A n} (hx : T.Rel x x') (hy : T.Rel y y') :
    T.Rel (T.binAux op x y) (T.binAux op x' y') := by
  obtain ⟨k, hxk, hxk', ex⟩ := hx
  obtain ⟨l, hyl, hyl', ey⟩ := hy
  obtain ⟨K, hkK, hlK, hxK, hyK, hxK', hyK'⟩ :
      ∃ K : ℕ, k ≤ K ∧ l ≤ K ∧ x.1 ≤ K ∧ y.1 ≤ K ∧ x'.1 ≤ K ∧ y'.1 ≤ K :=
    ⟨k + l + x.1 + y.1 + x'.1 + y'.1, by omega, by omega, by omega, by omega, by omega, by omega⟩
  refine ⟨K, max_le hxK hyK, max_le hxK' hyK', ?_⟩
  simp only [binAux]
  rw [hop (max_le hxK hyK), hop (max_le hxK' hyK'),
    T.climb_trans (le_max_left x.1 y.1) (max_le hxK hyK),
    T.climb_trans (le_max_right x.1 y.1) (max_le hxK hyK),
    T.climb_trans (le_max_left x'.1 y'.1) (max_le hxK' hyK'),
    T.climb_trans (le_max_right x'.1 y'.1) (max_le hxK' hyK'),
    climb_eq_mono hxk hxk' hkK ex, climb_eq_mono hyl hyl' hlK ey]

theorem unAux_rel (op : ∀ n : ℕ, A n → A n)
    (hop : ∀ {k i : ℕ}, k ≤ i → ∀ a : A k, T.climb i k (op k a) = op i (T.climb i k a))
    {x y : Σ n, A n} (h : T.Rel x y) : T.Rel (unAux op x) (unAux op y) := by
  obtain ⟨k, hx, hy, e⟩ := h
  refine ⟨k, hx, hy, ?_⟩
  show T.climb k x.1 (op x.1 x.2) = T.climb k y.1 (op y.1 y.2)
  rw [hop hx, hop hy, e]

variable (T)

/-! ### The algebraic structure -/

instance instMul : Mul T.Colim :=
  ⟨fun z w => Quotient.liftOn₂ z w
    (fun x y => Quotient.mk T.setoid (T.binAux (fun n => (· * · : A n → A n → A n)) x y))
    fun _ _ _ _ h₁ h₂ => Quotient.sound (binAux_rel _ (fun h a b => T.climb_mul h a b) h₁ h₂)⟩

instance instAdd : Add T.Colim :=
  ⟨fun z w => Quotient.liftOn₂ z w
    (fun x y => Quotient.mk T.setoid (T.binAux (fun n => (· + · : A n → A n → A n)) x y))
    fun _ _ _ _ h₁ h₂ => Quotient.sound (binAux_rel _ (fun h a b => T.climb_add h a b) h₁ h₂)⟩

instance instNeg : Neg T.Colim :=
  ⟨fun z => Quotient.liftOn z
    (fun x => Quotient.mk T.setoid (unAux (fun n => (- · : A n → A n)) x))
    fun _ _ h => Quotient.sound (unAux_rel _ (fun h a => T.climb_neg h a) h)⟩

instance instStar : Star T.Colim :=
  ⟨fun z => Quotient.liftOn z
    (fun x => Quotient.mk T.setoid (unAux (fun n => (star · : A n → A n)) x))
    fun _ _ h => Quotient.sound (unAux_rel _ (fun h a => T.climb_star h a) h)⟩

instance instSMul : SMul ℂ T.Colim :=
  ⟨fun r z => Quotient.liftOn z
    (fun x => Quotient.mk T.setoid (unAux (fun n => (r • · : A n → A n)) x))
    fun _ _ h => Quotient.sound (unAux_rel _ (fun h a => T.climb_smul h r a) h)⟩

instance instZero : Zero T.Colim := ⟨T.mkAt 0 0⟩

instance instOne : One T.Colim := ⟨T.mkAt 0 1⟩

theorem mkAt_mul_mk {i j k : ℕ} (a : A i) (b : A j) (hi : i ≤ k) (hj : j ≤ k) :
    T.mkAt i a * T.mkAt j b = T.mkAt k (T.climb k i a * T.climb k j b) := by
  have hmax : T.mkAt i a * T.mkAt j b
      = T.mkAt (max i j) (T.climb (max i j) i a * T.climb (max i j) j b) := rfl
  rw [hmax]
  refine T.mkAt_eq_mk (max_le hi hj) le_rfl ?_
  rw [T.climb_mul (max_le hi hj), T.climb_trans (le_max_left i j) (max_le hi hj),
    T.climb_trans (le_max_right i j) (max_le hi hj)]
  simp only [T.climb_self]

theorem mkAt_add_mk {i j k : ℕ} (a : A i) (b : A j) (hi : i ≤ k) (hj : j ≤ k) :
    T.mkAt i a + T.mkAt j b = T.mkAt k (T.climb k i a + T.climb k j b) := by
  have hmax : T.mkAt i a + T.mkAt j b
      = T.mkAt (max i j) (T.climb (max i j) i a + T.climb (max i j) j b) := rfl
  rw [hmax]
  refine T.mkAt_eq_mk (max_le hi hj) le_rfl ?_
  rw [T.climb_add (max_le hi hj), T.climb_trans (le_max_left i j) (max_le hi hj),
    T.climb_trans (le_max_right i j) (max_le hi hj)]
  simp only [T.climb_self]

@[simp] theorem mkAt_mul {i : ℕ} (a b : A i) : T.mkAt i a * T.mkAt i b = T.mkAt i (a * b) := by
  rw [T.mkAt_mul_mk a b (le_refl i) (le_refl i)]
  simp only [T.climb_self]

@[simp] theorem mkAt_add {i : ℕ} (a b : A i) : T.mkAt i a + T.mkAt i b = T.mkAt i (a + b) := by
  rw [T.mkAt_add_mk a b (le_refl i) (le_refl i)]
  simp only [T.climb_self]

@[simp] theorem mkAt_neg {i : ℕ} (a : A i) : -T.mkAt i a = T.mkAt i (-a) := rfl

@[simp] theorem mkAt_star {i : ℕ} (a : A i) : star (T.mkAt i a) = T.mkAt i (star a) := rfl

@[simp] theorem mkAt_smul {i : ℕ} (r : ℂ) (a : A i) : r • T.mkAt i a = T.mkAt i (r • a) := rfl

@[simp] theorem mkAt_zero (i : ℕ) : T.mkAt i (0 : A i) = 0 :=
  T.mkAt_eq_mk (le_refl i) (Nat.zero_le i)
    (by rw [T.climb_zero (Nat.zero_le i)]; simp only [T.climb_self])

@[simp] theorem mkAt_one (i : ℕ) : T.mkAt i (1 : A i) = 1 :=
  T.mkAt_eq_mk (le_refl i) (Nat.zero_le i)
    (by rw [T.climb_one (Nat.zero_le i)]; simp only [T.climb_self])

instance instAddCommGroup : AddCommGroup T.Colim where
  add := (· + ·)
  zero := 0
  neg := (- ·)
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := T.ind₃ fun _ a b c => by
    show T.mkAt _ a + T.mkAt _ b + T.mkAt _ c = T.mkAt _ a + (T.mkAt _ b + T.mkAt _ c)
    simp only [T.mkAt_add, add_assoc]
  zero_add := T.ind fun i a => by
    show T.mkAt 0 (0 : A 0) + T.mkAt i a = T.mkAt i a
    rw [T.mkAt_add_mk _ a (Nat.zero_le i) (le_refl i), T.climb_zero (Nat.zero_le i)]
    simp only [T.climb_self, zero_add]
  add_zero := T.ind fun i a => by
    show T.mkAt i a + T.mkAt 0 (0 : A 0) = T.mkAt i a
    rw [T.mkAt_add_mk a _ (le_refl i) (Nat.zero_le i), T.climb_zero (Nat.zero_le i)]
    simp only [T.climb_self, add_zero]
  neg_add_cancel := T.ind fun i a => by
    show -T.mkAt i a + T.mkAt i a = T.mkAt 0 (0 : A 0)
    rw [T.mkAt_neg, T.mkAt_add, neg_add_cancel]
    exact T.mkAt_zero i
  add_comm := T.ind₂ fun _ a b => by
    show T.mkAt _ a + T.mkAt _ b = T.mkAt _ b + T.mkAt _ a
    simp only [T.mkAt_add, add_comm]

instance instRing : Ring T.Colim where
  __ := T.instAddCommGroup
  mul := (· * ·)
  one := 1
  mul_assoc := T.ind₃ fun _ a b c => by
    show T.mkAt _ a * T.mkAt _ b * T.mkAt _ c = T.mkAt _ a * (T.mkAt _ b * T.mkAt _ c)
    simp only [T.mkAt_mul, mul_assoc]
  one_mul := T.ind fun i a => by
    show T.mkAt 0 (1 : A 0) * T.mkAt i a = T.mkAt i a
    rw [T.mkAt_mul_mk _ a (Nat.zero_le i) (le_refl i), T.climb_one (Nat.zero_le i)]
    simp only [T.climb_self, one_mul]
  mul_one := T.ind fun i a => by
    show T.mkAt i a * T.mkAt 0 (1 : A 0) = T.mkAt i a
    rw [T.mkAt_mul_mk a _ (le_refl i) (Nat.zero_le i), T.climb_one (Nat.zero_le i)]
    simp only [T.climb_self, mul_one]
  left_distrib := T.ind₃ fun _ a b c => by
    show T.mkAt _ a * (T.mkAt _ b + T.mkAt _ c) = T.mkAt _ a * T.mkAt _ b + T.mkAt _ a * T.mkAt _ c
    simp only [T.mkAt_add, T.mkAt_mul, left_distrib]
  right_distrib := T.ind₃ fun _ a b c => by
    show (T.mkAt _ a + T.mkAt _ b) * T.mkAt _ c = T.mkAt _ a * T.mkAt _ c + T.mkAt _ b * T.mkAt _ c
    simp only [T.mkAt_add, T.mkAt_mul, right_distrib]
  zero_mul := T.ind fun i a => by
    show T.mkAt 0 (0 : A 0) * T.mkAt i a = T.mkAt 0 (0 : A 0)
    rw [T.mkAt_mul_mk _ a (Nat.zero_le i) (le_refl i), T.climb_zero (Nat.zero_le i)]
    simp only [T.climb_self, zero_mul]
    exact T.mkAt_zero i
  mul_zero := T.ind fun i a => by
    show T.mkAt i a * T.mkAt 0 (0 : A 0) = T.mkAt 0 (0 : A 0)
    rw [T.mkAt_mul_mk a _ (le_refl i) (Nat.zero_le i), T.climb_zero (Nat.zero_le i)]
    simp only [T.climb_self, mul_zero]
    exact T.mkAt_zero i

instance instStarRing : StarRing T.Colim where
  star := (star ·)
  star_involutive := T.ind fun _ a => by
    show star (star (T.mkAt _ a)) = T.mkAt _ a
    simp only [T.mkAt_star, star_star]
  star_mul := T.ind₂ fun _ a b => by
    show star (T.mkAt _ a * T.mkAt _ b) = star (T.mkAt _ b) * star (T.mkAt _ a)
    simp only [T.mkAt_mul, T.mkAt_star, star_mul]
  star_add := T.ind₂ fun _ a b => by
    show star (T.mkAt _ a + T.mkAt _ b) = star (T.mkAt _ a) + star (T.mkAt _ b)
    simp only [T.mkAt_add, T.mkAt_star, star_add]

instance instAlgebra : Algebra ℂ T.Colim where
  smul := (· • ·)
  algebraMap :=
    { toFun := fun r => T.mkAt 0 (algebraMap ℂ (A 0) r)
      map_one' := by rw [map_one, T.mkAt_one]
      map_mul' := fun r s => by rw [map_mul, T.mkAt_mul]
      map_zero' := by rw [map_zero, T.mkAt_zero]
      map_add' := fun r s => by rw [map_add, T.mkAt_add] }
  commutes' := fun r => T.ind fun i a => by
    show T.mkAt 0 (algebraMap ℂ (A 0) r) * T.mkAt i a = T.mkAt i a * T.mkAt 0 (algebraMap ℂ (A 0) r)
    rw [T.mkAt_mul_mk _ a (Nat.zero_le i) (le_refl i),
      T.mkAt_mul_mk a _ (le_refl i) (Nat.zero_le i), T.climb_algebraMap (Nat.zero_le i)]
    simp only [T.climb_self, Algebra.commutes]
  smul_def' := fun r => T.ind fun i a => by
    show r • T.mkAt i a = T.mkAt 0 (algebraMap ℂ (A 0) r) * T.mkAt i a
    rw [T.mkAt_smul, T.mkAt_mul_mk _ a (Nat.zero_le i) (le_refl i),
      T.climb_algebraMap (Nat.zero_le i)]
    simp only [T.climb_self]
    rw [Algebra.smul_def]

instance instStarModule : StarModule ℂ T.Colim where
  star_smul := fun r => T.ind fun _ a => by
    show star (r • T.mkAt _ a) = star r • star (T.mkAt _ a)
    simp only [T.mkAt_smul, T.mkAt_star, star_smul]

/-! ### The colimit norm -/

/-- The colimit norm on representatives: the norm of the representative, which is independent of
the level because the connecting maps are isometric. -/
def normFun : T.Colim → ℝ :=
  Quotient.lift (fun x : Σ n, A n => ‖x.2‖) (by
    rintro x y ⟨k, hx, hy, e⟩
    have he := congrArg (fun z : A k => ‖z‖) e
    simpa only [T.climb_norm hx, T.climb_norm hy] using he)

@[simp] theorem normFun_mkAt (i : ℕ) (a : A i) : T.normFun (T.mkAt i a) = ‖a‖ := rfl

/-- The colimit norm, packaged as a `RingNorm` so that Mathlib supplies the metric. -/
def colimRingNorm : RingNorm T.Colim where
  toFun := T.normFun
  map_zero' := by
    show T.normFun (T.mkAt 0 (0 : A 0)) = 0
    rw [T.normFun_mkAt, norm_zero]
  add_le' := T.ind₂ fun _ a b => by
    show T.normFun (T.mkAt _ a + T.mkAt _ b) ≤ T.normFun (T.mkAt _ a) + T.normFun (T.mkAt _ b)
    simp only [T.mkAt_add, T.normFun_mkAt]
    exact norm_add_le a b
  neg' := T.ind fun _ a => by
    show T.normFun (-T.mkAt _ a) = T.normFun (T.mkAt _ a)
    simp only [T.mkAt_neg, T.normFun_mkAt, norm_neg]
  mul_le' := T.ind₂ fun _ a b => by
    show T.normFun (T.mkAt _ a * T.mkAt _ b) ≤ T.normFun (T.mkAt _ a) * T.normFun (T.mkAt _ b)
    simp only [T.mkAt_mul, T.normFun_mkAt]
    exact norm_mul_le a b
  eq_zero_of_map_eq_zero' := T.ind fun i a => by
    intro h
    rw [T.normFun_mkAt] at h
    rw [norm_eq_zero.mp h, T.mkAt_zero]

instance instNormedRing : NormedRing T.Colim := T.colimRingNorm.toNormedRing

@[simp] theorem norm_mkAt (i : ℕ) (a : A i) : ‖T.mkAt i a‖ = ‖a‖ := rfl

instance instNormedStarGroup : NormedStarGroup T.Colim where
  norm_star_le := T.ind fun _ a => by
    simp only [T.mkAt_star, T.norm_mkAt, norm_star, le_refl]

instance instCStarRing : CStarRing T.Colim where
  norm_mul_self_le := T.ind fun _ a => by
    simp only [T.mkAt_star, T.mkAt_mul, T.norm_mkAt]
    exact CStarRing.norm_mul_self_le a

instance instNormedAlgebra : NormedAlgebra ℂ T.Colim where
  __ := T.instAlgebra
  norm_smul_le := fun r => T.ind fun _ a => by
    simp only [T.mkAt_smul, T.norm_mkAt]
    exact norm_smul_le r a

/-! ### The canonical maps from the levels -/

/-- The canonical unital ⋆-homomorphism from level `i` into the colimit. -/
def iota (i : ℕ) : A i →⋆ₐ[ℂ] T.Colim where
  toFun := T.mkAt i
  map_one' := T.mkAt_one i
  map_mul' a b := (T.mkAt_mul a b).symm
  map_zero' := T.mkAt_zero i
  map_add' a b := (T.mkAt_add a b).symm
  commutes' r :=
    (T.mkAt_eq_mk (Nat.zero_le i) (le_refl i)
      (by rw [T.climb_algebraMap (Nat.zero_le i)]; simp only [T.climb_self])).symm
  map_star' a := (T.mkAt_star a).symm

@[simp] theorem iota_apply (i : ℕ) (a : A i) : T.iota i a = T.mkAt i a := rfl

@[simp] theorem norm_iota (i : ℕ) (a : A i) : ‖T.iota i a‖ = ‖a‖ := rfl

theorem iota_isometry (i : ℕ) : Isometry (T.iota i) :=
  AddMonoidHomClass.isometry_of_norm _ (T.norm_iota i)

theorem iota_injective (i : ℕ) : Function.Injective (T.iota i) :=
  (T.iota_isometry i).injective

@[simp] theorem iota_climb {k i : ℕ} (h : k ≤ i) (a : A k) :
    T.iota i (T.climb i k a) = T.iota k a :=
  T.mkAt_climb h a

@[simp] theorem iota_succHom (i : ℕ) (a : A i) : T.iota (i + 1) (T.succHom i a) = T.iota i a := by
  rw [← T.climb_succ_self i a, T.iota_climb (Nat.le_succ i)]

theorem iota_climbHom {k i : ℕ} (h : k ≤ i) (a : A k) :
    T.iota i (T.climbHom h a) = T.iota k a :=
  T.mkAt_climb h a

theorem exists_iota (z : T.Colim) : ∃ (i : ℕ) (a : A i), z = T.iota i a := T.exists_mkAt z

instance instNontrivial [Nontrivial (A 0)] : Nontrivial T.Colim :=
  (T.iota_injective 0).nontrivial

end

end CStarTower

end LIX

end GroupApproximation
