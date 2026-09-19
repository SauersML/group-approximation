import GroupApproximation.Steinberg.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Steinberg groups of homotopes: the inverse system behind the Steinberg pro-group

Lane `fix-bh-a`, EXC Step 1 foundations (board `k2-poly.md`).  Source: Lavrenov–Sinchuk–Voronetsky,
*Centrality of K₂ for Chevalley groups: a pro-group approach*, arXiv:2009.03999, §2.3–2.4 (type
`A` here).

For a commutative ring `R` and `s ∈ R`, the `s`-homotope `R^{(s)}` is `R` with the product
`a ∘ b = a s b` (a ring without unit).  Its Steinberg group has generators `x_ij(a)`, `a ∈ R`, and
the three Steinberg relation families with `ab` replaced by `a s b`.  None of the Steinberg
relations uses a unit, so this is the usual presentation over the rng `R^{(s)}`.

We index by powers of a fixed `h ∈ R`: `HSt I h t = St_I(R^{(h^t)})`.

* `div` (`a ↦ a h^k`): the structure maps `St_I(R^{(h^m)}) → St_I(R^{(h^t)})` for `t + k = m`.
  Together they form the inverse system whose formal limit is the pro-group `St^{(∞)}_I(R)`.
  `div_div` and `div_self` are functoriality.
* `toSt` (`a ↦ h^t a`): `St_I(R^{(h^t)}) → St_I(R)`, the map induced by `R^{(h^t)} → h^t R`, with
  `toSt_div` (compatibility).
* `ofSt` and `ofSt_toSt` / `toSt_ofSt`: `St_I(R^{(1)}) ≅ St_I(R)` at `t = 0`.
* `map`: functoriality in ring maps `f : R → R'`, with `h ↦ f h`.

Division by `h` (`div`) is why homotopes are used rather than the ideals `h^t R`: it exists even
when `h` is a zero divisor (LSV 2009.03999, Remark 2.5).
-/

namespace GroupApproximation.K2Excision

open GroupApproximation
open scoped commutatorElement

variable {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommRing R]

/-- The Steinberg relators of the homotope `R^{(s)}`. -/
inductive IsHRelation (s : R) : FreeGroup (SteinbergGenerator I R) → Prop
  | add (i j : I) (hij : i ≠ j) (a b : R) :
      IsHRelation s
        (FreeGroup.of (⟨i, j, hij, a⟩ : SteinbergGenerator I R) *
          FreeGroup.of (⟨i, j, hij, b⟩ : SteinbergGenerator I R) *
          (FreeGroup.of (⟨i, j, hij, a + b⟩ : SteinbergGenerator I R))⁻¹)
  | commute (i j k l : I) (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i) (a b : R) :
      IsHRelation s
        ⁅FreeGroup.of (⟨i, j, hij, a⟩ : SteinbergGenerator I R),
          FreeGroup.of (⟨k, l, hkl, b⟩ : SteinbergGenerator I R)⁆
  | adjacent (i j k : I) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
      IsHRelation s
        (⁅FreeGroup.of (⟨i, j, hij, a⟩ : SteinbergGenerator I R),
            FreeGroup.of (⟨j, k, hjk, b⟩ : SteinbergGenerator I R)⁆ *
          (FreeGroup.of (⟨i, k, hik, a * s * b⟩ : SteinbergGenerator I R))⁻¹)

#audit_axioms GroupApproximation.K2Excision.IsHRelation

/-- The relator set of `St_I(R^{(s)})`. -/
def hRelations (s : R) : Set (FreeGroup (SteinbergGenerator I R)) :=
  {w | IsHRelation (I := I) s w}

#audit_axioms GroupApproximation.K2Excision.hRelations

variable (I) in
/-- `St_I(R^{(h^t)})`, the Steinberg group of the `h^t`-homotope. -/
abbrev HSt (h : R) (t : ℕ) : Type _ :=
  PresentedGroup (hRelations (I := I) (h ^ t))

namespace HSt

/-- The generator `x_ij(a)` of `St_I(R^{(h^t)})`. -/
def x (h : R) (t : ℕ) (i j : I) (hij : i ≠ j) (a : R) : HSt I h t :=
  PresentedGroup.of ⟨i, j, hij, a⟩

#audit_axioms GroupApproximation.K2Excision.HSt.x

variable {h : R} {t : ℕ}

theorem x_mul (i j : I) (hij : i ≠ j) (a b : R) :
    x h t i j hij a * x h t i j hij b = x h t i j hij (a + b) := by
  apply eq_of_mul_inv_eq_one
  have hrel : FreeGroup.of (⟨i, j, hij, a⟩ : SteinbergGenerator I R) *
      FreeGroup.of (⟨i, j, hij, b⟩ : SteinbergGenerator I R) *
      (FreeGroup.of (⟨i, j, hij, a + b⟩ : SteinbergGenerator I R))⁻¹ ∈
        hRelations (I := I) (h ^ t) :=
    IsHRelation.add i j hij a b
  simpa only [x, PresentedGroup.of, map_mul, map_inv] using PresentedGroup.one_of_mem hrel

#audit_axioms GroupApproximation.K2Excision.HSt.x_mul

@[simp] theorem x_zero (i j : I) (hij : i ≠ j) : x h t i j hij (0 : R) = 1 := by
  have e := x_mul (h := h) (t := t) i j hij 0 0
  rw [zero_add] at e
  apply mul_left_cancel (a := x h t i j hij 0)
  simpa only [mul_one] using e

#audit_axioms GroupApproximation.K2Excision.HSt.x_zero

@[simp] theorem x_neg (i j : I) (hij : i ≠ j) (a : R) :
    x h t i j hij (-a) = (x h t i j hij a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [x_mul]
  simp

#audit_axioms GroupApproximation.K2Excision.HSt.x_neg

theorem x_commute_of_ne (i j k l : I) (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i)
    (a b : R) : Commute (x h t i j hij a) (x h t k l hkl b) := by
  rw [commute_iff_eq]
  apply commutatorElement_eq_one_iff_mul_comm.mp
  have hrel : ⁅FreeGroup.of (⟨i, j, hij, a⟩ : SteinbergGenerator I R),
      FreeGroup.of (⟨k, l, hkl, b⟩ : SteinbergGenerator I R)⁆ ∈ hRelations (I := I) (h ^ t) :=
    IsHRelation.commute i j k l hij hkl hjk hli a b
  simpa only [x, PresentedGroup.of, map_commutatorElement] using PresentedGroup.one_of_mem hrel

#audit_axioms GroupApproximation.K2Excision.HSt.x_commute_of_ne

/-- The adjacent-root relation of the homotope: `[x_ij(a), x_jk(b)] = x_ik(a h^t b)`. -/
theorem x_commutator (i j k : I) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    ⁅x h t i j hij a, x h t j k hjk b⁆ = x h t i k hik (a * h ^ t * b) := by
  apply eq_of_mul_inv_eq_one
  have hrel : ⁅FreeGroup.of (⟨i, j, hij, a⟩ : SteinbergGenerator I R),
      FreeGroup.of (⟨j, k, hjk, b⟩ : SteinbergGenerator I R)⁆ *
      (FreeGroup.of (⟨i, k, hik, a * h ^ t * b⟩ : SteinbergGenerator I R))⁻¹ ∈
        hRelations (I := I) (h ^ t) :=
    IsHRelation.adjacent i j k hij hjk hik a b
  simpa only [x, PresentedGroup.of, map_mul, map_inv, map_commutatorElement] using
    PresentedGroup.one_of_mem hrel

#audit_axioms GroupApproximation.K2Excision.HSt.x_commutator

/-- A homomorphism out of `St_I(R^{(h^t)})` from images of generators that satisfy the three
relation families. -/
def lift {G : Type*} [Group G] (f : (i j : I) → i ≠ j → R → G)
    (hadd : ∀ i j (hij : i ≠ j) a b, f i j hij a * f i j hij b = f i j hij (a + b))
    (hcomm : ∀ i j k l (hij : i ≠ j) (hkl : k ≠ l), j ≠ k → l ≠ i → ∀ a b,
      ⁅f i j hij a, f k l hkl b⁆ = 1)
    (hadj : ∀ i j k (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) a b,
      ⁅f i j hij a, f j k hjk b⁆ = f i k hik (a * h ^ t * b)) :
    HSt I h t →* G :=
  PresentedGroup.toGroup (f := fun g : SteinbergGenerator I R => f g.row g.column g.row_ne_column
    g.coefficient) (by
    intro w hw
    change IsHRelation (h ^ t) w at hw
    cases hw with
    | add i j hij a b =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      change f i j hij a * f i j hij b * (f i j hij (a + b))⁻¹ = 1
      rw [hadd, mul_inv_cancel]
    | commute i j k l hij hkl hjk hli a b =>
      simp only [map_commutatorElement, FreeGroup.lift_apply_of]
      change ⁅f i j hij a, f k l hkl b⁆ = 1
      exact hcomm i j k l hij hkl hjk hli a b
    | adjacent i j k hij hjk hik a b =>
      simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
      change ⁅f i j hij a, f j k hjk b⁆ * (f i k hik (a * h ^ t * b))⁻¹ = 1
      rw [hadj, mul_inv_cancel])

#audit_axioms GroupApproximation.K2Excision.HSt.lift

@[simp] theorem lift_x {G : Type*} [Group G] (f : (i j : I) → i ≠ j → R → G) (hadd hcomm hadj)
    (i j : I) (hij : i ≠ j) (a : R) :
    lift (h := h) (t := t) f hadd hcomm hadj (x h t i j hij a) = f i j hij a :=
  PresentedGroup.toGroup.of _

#audit_axioms GroupApproximation.K2Excision.HSt.lift_x

/-- Two homomorphisms out of `St_I(R^{(h^t)})` agreeing on generators are equal. -/
theorem hom_ext {G : Type*} [Group G] {φ ψ : HSt I h t →* G}
    (e : ∀ i j (hij : i ≠ j) a, φ (x h t i j hij a) = ψ (x h t i j hij a)) : φ = ψ :=
  PresentedGroup.ext fun g => e g.row g.column g.row_ne_column g.coefficient

#audit_axioms GroupApproximation.K2Excision.HSt.hom_ext

end HSt

open HSt

variable (h : R)

/-- **Structure maps** `St_I(R^{(h^m)}) → St_I(R^{(h^t)})`, `x_ij(a) ↦ x_ij(a h^k)`, for
`t + k = m`. -/
def div {t k m : ℕ} (e : t + k = m) : HSt I h m →* HSt I h t :=
  lift (fun i j hij a => HSt.x h t i j hij (a * h ^ k))
    (fun i j hij a b => by rw [x_mul, add_mul])
    (fun i j k' l hij hkl hjk hli a b => (x_commute_of_ne i j k' l hij hkl hjk hli _ _).commutator_eq)
    (fun i j k' hij hjk hik a b => by
      rw [x_commutator]
      congr 1
      rw [← e, pow_add]
      ring)

#audit_axioms GroupApproximation.K2Excision.div

@[simp] theorem div_x {t k m : ℕ} (e : t + k = m) (i j : I) (hij : i ≠ j) (a : R) :
    div h e (HSt.x h m i j hij a) = HSt.x h t i j hij (a * h ^ k) :=
  lift_x _ _ _ _ i j hij a

#audit_axioms GroupApproximation.K2Excision.div_x

/-- The structure maps are functorial. -/
theorem div_div {t k m k' n : ℕ} (e : t + k = m) (e' : m + k' = n) :
    (div (I := I) h e).comp (div h e') = div h (show t + (k + k') = n by omega) :=
  hom_ext fun i j hij a => by
    simp only [MonoidHom.comp_apply, div_x]
    congr 1
    rw [pow_add]
    ring

#audit_axioms GroupApproximation.K2Excision.div_div

theorem div_self (t : ℕ) : div (I := I) h (show t + 0 = t by omega) = MonoidHom.id _ :=
  hom_ext fun i j hij a => by simp

#audit_axioms GroupApproximation.K2Excision.div_self

/-- `St_I(R^{(h^t)}) → St_I(R)`, `x_ij(a) ↦ x_ij(h^t a)`. -/
def toSt (t : ℕ) : HSt I h t →* SteinbergGroup I R :=
  lift (fun i j hij a => SteinbergGroup.x i j hij (h ^ t * a))
    (fun i j hij a b => by rw [SteinbergGroup.x_mul, mul_add])
    (fun i j k l hij hkl hjk hli a b =>
      (SteinbergGroup.x_commute_of_ne i j k l hij hkl hjk hli _ _).commutator_eq)
    (fun i j k hij hjk hik a b => by
      rw [SteinbergGroup.x_commutator]
      congr 1
      ring)

#audit_axioms GroupApproximation.K2Excision.toSt

@[simp] theorem toSt_x (t : ℕ) (i j : I) (hij : i ≠ j) (a : R) :
    toSt h t (HSt.x h t i j hij a) = SteinbergGroup.x i j hij (h ^ t * a) :=
  lift_x _ _ _ _ i j hij a

#audit_axioms GroupApproximation.K2Excision.toSt_x

/-- `toSt` is compatible with the structure maps. -/
theorem toSt_div {t k m : ℕ} (e : t + k = m) :
    (toSt (I := I) h t).comp (div h e) = toSt h m := by
  subst e
  exact hom_ext fun i j hij a => by
    simp only [MonoidHom.comp_apply, div_x, toSt_x]
    congr 1
    rw [pow_add]
    ring

#audit_axioms GroupApproximation.K2Excision.toSt_div

/-- `St_I(R) → St_I(R^{(h^0)})`, `x_ij(a) ↦ x_ij(a)`. -/
def ofSt : SteinbergGroup I R →* HSt I h 0 :=
  PresentedGroup.toGroup (f := fun g : SteinbergGenerator I R =>
    HSt.x h 0 g.row g.column g.row_ne_column g.coefficient) (by
    intro w hw
    change SteinbergGroup.IsRelation w at hw
    cases hw with
    | add i j hij a b =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      change HSt.x h 0 i j hij a * HSt.x h 0 i j hij b * (HSt.x h 0 i j hij (a + b))⁻¹ = 1
      rw [x_mul, mul_inv_cancel]
    | commute i j k l hij hkl hjk hli a b =>
      simp only [map_commutatorElement, FreeGroup.lift_apply_of]
      change ⁅HSt.x h 0 i j hij a, HSt.x h 0 k l hkl b⁆ = 1
      exact (x_commute_of_ne i j k l hij hkl hjk hli _ _).commutator_eq
    | adjacent i j k hij hjk hik a b =>
      simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
      change ⁅HSt.x h 0 i j hij a, HSt.x h 0 j k hjk b⁆ * (HSt.x h 0 i k hik (a * b))⁻¹ = 1
      rw [x_commutator, pow_zero, mul_one, mul_inv_cancel])

#audit_axioms GroupApproximation.K2Excision.ofSt

@[simp] theorem ofSt_x (i j : I) (hij : i ≠ j) (a : R) :
    ofSt h (SteinbergGroup.x i j hij a) = HSt.x h 0 i j hij a :=
  PresentedGroup.toGroup.of _

#audit_axioms GroupApproximation.K2Excision.ofSt_x

theorem toSt_ofSt : (toSt (I := I) h 0).comp (ofSt h) = MonoidHom.id _ :=
  PresentedGroup.ext fun g => by
    change toSt h 0 (ofSt h (SteinbergGroup.x g.row g.column g.row_ne_column g.coefficient)) =
      SteinbergGroup.x g.row g.column g.row_ne_column g.coefficient
    rw [ofSt_x, toSt_x, pow_zero, one_mul]

#audit_axioms GroupApproximation.K2Excision.toSt_ofSt

theorem ofSt_toSt : (ofSt (I := I) h).comp (toSt h 0) = MonoidHom.id _ :=
  hom_ext fun i j hij a => by
    simp only [MonoidHom.comp_apply, toSt_x, pow_zero, one_mul, ofSt_x, MonoidHom.id_apply]

#audit_axioms GroupApproximation.K2Excision.ofSt_toSt

/-- **Functoriality in the ring**: `f : R → R'` induces `St_I(R^{(h^t)}) → St_I(R'^{(f(h)^t)})`. -/
def map {R' : Type*} [CommRing R'] (f : R →+* R') (t : ℕ) : HSt I h t →* HSt I (f h) t :=
  lift (fun i j hij a => HSt.x (f h) t i j hij (f a))
    (fun i j hij a b => by rw [x_mul, map_add])
    (fun i j k l hij hkl hjk hli a b => (x_commute_of_ne i j k l hij hkl hjk hli _ _).commutator_eq)
    (fun i j k hij hjk hik a b => by rw [x_commutator, map_mul, map_mul, map_pow])

#audit_axioms GroupApproximation.K2Excision.map

@[simp] theorem map_x {R' : Type*} [CommRing R'] (f : R →+* R') (t : ℕ) (i j : I) (hij : i ≠ j)
    (a : R) : map h f t (HSt.x h t i j hij a) = HSt.x (f h) t i j hij (f a) :=
  lift_x _ _ _ _ i j hij a

#audit_axioms GroupApproximation.K2Excision.map_x

/-- `map` commutes with the structure maps. -/
theorem map_div {R' : Type*} [CommRing R'] (f : R →+* R') {t k m : ℕ} (e : t + k = m) :
    (map (I := I) h f t).comp (div h e) = (div (f h) e).comp (map h f m) :=
  hom_ext fun i j hij a => by
    simp only [MonoidHom.comp_apply, div_x, map_x, map_mul, map_pow]

#audit_axioms GroupApproximation.K2Excision.map_div

end GroupApproximation.K2Excision
