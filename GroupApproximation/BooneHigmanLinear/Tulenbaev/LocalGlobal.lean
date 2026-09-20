import GroupApproximation.BooneHigmanLinear.Tulenbaev.Components
import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.LocFinitary
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.Tactic.LinearCombination
import GroupApproximation.Meta.AxiomGuard

/-!
# Tulenbaev's local–global principle for `St_N`, from the dilation principle (lane sk-k2-loc)

Source: M. S. Tulenbaev, *The Steinberg group of a polynomial ring*, Math. USSR Sb. 45 (1983)
139–154, §2 (read at source). Piece LG of `board/k2-poly.md`.

Tulenbaev's §2 has three layers.
1. Lemma 2.3 and Cor 2.4, the **dilation principle**. If `α ∈ St_r(A[X])` has `α(0) = 1` and
   `α ↦ 1` in `St_r(A_a[X])`, then `α(a^n X) = 1` for all large `n`. The proof needs van der
   Kallen's relative generators `X_{v,w}` (Tulenbaev §1, foundations F of `k2-poly`). It is
   **not** proved here; it is the hypothesis `StDilationStatementAt n₀`.
2. Lemma 2.5, **patching**. If `aA + bA = A` and `α ↦ 1` over both `A_a` and `A_b`, then
   `α = 1`. Proved here from (1) as `eq_one_of_coprime`. The argument is simpler than
   Tulenbaev's `β(X,Y,Z)`: take `β(X, Z) = α(X) α((1+Z)X)⁻¹` over the base `A[X]` and dilate it
   at `b`, and dilate `α` itself at `a`.
3. Thm 2.1, the **local–global principle**. The `c` with `α_c = 1` form an ideal
   (`goodIdeal`). If that ideal meets every maximal ideal's complement, it is `⊤`, so `α = 1`
   (`eq_one_of_away`, Zariski form).
   - The finite-stage principle at maximal ideals is proved as `stAtMaximalFiniteStage`,
     using Steinberg groups commuting with localization and polynomial localization.
   - `stLocalGlobal_of_dilation` gives Components' `StLocalGlobalStatementAt n₀`.

**LG-stable** (`diesAfterPadding_of_away`). If `u ∈ St_N(A[X])`, `u(0) = 1`, dies after padding
over some `A_s`, `s ∉ 𝔪`, for every maximal `𝔪`, then `u` dies after padding. The proof is
quasi-compactness plus (3).

Not here: the companion "image of `St_{r-1}`" form of Thm 2.1.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace Tulenbaev

noncomputable section

open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic Polynomial

/-! ### Generic facts about Steinberg groups -/

/-- The Steinberg group of a subsingleton ring is trivial. -/
theorem steinberg_eq_one_of_subsingleton {I R : Type*} [Fintype I] [DecidableEq I] [Ring R]
    [Subsingleton R] (g : SteinbergGroup I R) : g = 1 := by
  have h : MonoidHom.id (SteinbergGroup I R) = 1 := by
    refine PresentedGroup.ext ?_
    rintro ⟨i, j, hij, a⟩
    change x i j hij a = 1
    rw [Subsingleton.elim a 0, x_zero]
  exact DFunLike.congr_fun h g

#audit_axioms GroupApproximation.BooneHigmanLinear.Tulenbaev.steinberg_eq_one_of_subsingleton

/-- Coefficient maps commute with index maps. -/
theorem ringMap_indexMap_comm {I J R S : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] [Ring R] [Ring S] (f : R →+* S) (e : I ↪ J) (u : SteinbergGroup I R) :
    ringMap f (indexMap e u) = indexMap e (ringMap f u) := by
  have h : (ringMap (I := J) f).comp (indexMap (R := R) e) =
      (indexMap (R := S) e).comp (ringMap (I := I) f) := by
    refine PresentedGroup.ext ?_
    rintro ⟨i, j, hij, a⟩
    change ringMap f (indexMap e (x i j hij a)) = indexMap e (ringMap f (x i j hij a))
    rw [indexMap_x, ringMap_x, ringMap_x, indexMap_x]
  exact DFunLike.congr_fun h u

#audit_axioms GroupApproximation.BooneHigmanLinear.Tulenbaev.ringMap_indexMap_comm

/-- Padding in two steps is padding in one step. -/
theorem indexMap_castLEEmb_trans {R : Type*} [Ring R] {n m p : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ p)
    (u : SteinbergGroup (Fin n) R) :
    indexMap (Fin.castLEEmb h₂) (indexMap (Fin.castLEEmb h₁) u) =
      indexMap (Fin.castLEEmb (h₁.trans h₂)) u := by
  have he : (Fin.castLEEmb h₁).trans (Fin.castLEEmb h₂) = Fin.castLEEmb (h₁.trans h₂) :=
    Function.Embedding.ext fun _ => Fin.ext rfl
  rw [← he, indexMap_trans]
  rfl

#audit_axioms GroupApproximation.BooneHigmanLinear.Tulenbaev.indexMap_castLEEmb_trans

/-! ### The ring maps of the argument -/

/-- Coefficientwise localization `A[X] → A_a[X]`. -/
abbrev awayPoly {A : Type} [CommRing A] (a : A) : A[X] →+* (Localization.Away a)[X] :=
  Polynomial.mapRingHom (algebraMap A (Localization.Away a))

/-- The dilation `A[X] → A[X]`, `X ↦ c X`. -/
def dil {A : Type} [CommRing A] (c : A) : A[X] →+* A[X] :=
  Polynomial.eval₂RingHom Polynomial.C (Polynomial.C c * Polynomial.X)

@[simp] theorem dil_C {A : Type} [CommRing A] (c a : A) : dil c (Polynomial.C a) = Polynomial.C a := by
  simp [dil]

@[simp] theorem dil_X {A : Type} [CommRing A] (c : A) :
    dil c Polynomial.X = Polynomial.C c * Polynomial.X := by
  simp [dil]

theorem dil_comp {A : Type} [CommRing A] (c d : A) : (dil c).comp (dil d) = dil (c * d) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp
  · rw [RingHom.comp_apply, dil_X, map_mul, dil_C, dil_X, dil_X, Polynomial.C_mul]
    ring

/-- `A[X] → A[X][Z]`, `X ↦ (1 + Z) X`. -/
def shiftMul (A : Type) [CommRing A] : A[X] →+* (A[X])[X] :=
  Polynomial.eval₂RingHom ((Polynomial.C : A[X] →+* (A[X])[X]).comp Polynomial.C)
    ((1 + Polynomial.X) * Polynomial.C Polynomial.X)

@[simp] theorem shiftMul_C {A : Type} [CommRing A] (a : A) :
    shiftMul A (Polynomial.C a) = Polynomial.C (Polynomial.C a) := by
  simp [shiftMul]

@[simp] theorem shiftMul_X {A : Type} [CommRing A] :
    shiftMul A Polynomial.X = (1 + Polynomial.X) * Polynomial.C Polynomial.X := by
  simp [shiftMul]

/-! ### The dilation principle (Tulenbaev, Lemma 2.3 and Cor 2.4) -/

/-- **Dilation principle** (Tulenbaev, Cor 2.4), at ranks `N ≥ n₀`. If `α ∈ St_N(A[X])` has
`α(0) = 1` and becomes `1` in `St_N(A_a[X])`, then `α(a^n X) = 1` for all large `n`. Tulenbaev
proves it for `r ≥ 5` from van der Kallen's relative generators (his Lemma 2.3). -/
def StDilationStatementAt (n₀ : ℕ) : Prop :=
  ∀ (A : Type) [CommRing A] (N : ℕ), n₀ ≤ N → ∀ (a : A) (α : SteinbergGroup (Fin N) A[X]),
    ringMap (Polynomial.evalRingHom (0 : A)) α = 1 → ringMap (awayPoly a) α = 1 →
      ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → ringMap (dil (a ^ n)) α = 1

#audit_axioms GroupApproximation.BooneHigmanLinear.Tulenbaev.StDilationStatementAt

/-- **Finite-stage principle at maximal ideals** (Tulenbaev, Lemma 2.2, for `A_𝔪 = colim A_s`).
An element of `St_N(A[X])` that becomes `1` over `A_𝔪` becomes `1` over some `A_s`, `s ∉ 𝔪`. -/
def StAtMaximalFiniteStageStatement : Prop :=
  ∀ (A : Type) [CommRing A] (N : ℕ) (M : Ideal A) [M.IsMaximal] (α : SteinbergGroup (Fin N) A[X]),
    ringMap (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime M))) α = 1 →
      ∃ s ∉ M, ringMap (awayPoly s) α = 1

#audit_axioms GroupApproximation.BooneHigmanLinear.Tulenbaev.StAtMaximalFiniteStageStatement

attribute [local instance] Polynomial.algebra in
/-- An equality over `A_𝔪[X]` already holds after inverting one element outside `𝔪`.
This is the finite-stage principle, with no rank or domain hypothesis. -/
theorem stAtMaximalFiniteStage : StAtMaximalFiniteStageStatement := by
  intro A _ N M _ α hα
  have hL := Polynomial.isLocalization M.primeCompl (Localization.AtPrime M)
  have hα' : ringMap (algebraMap A[X] (Localization.AtPrime M)[X]) α = 1 := by
    simpa only [Polynomial.algebraMap_def] using hα
  obtain ⟨f, hf, hkill⟩ := K2Found.exists_mem_ringMap_eq_one _ (Fin N) hL hα'
  obtain ⟨s, hs, rfl⟩ := Submonoid.mem_map.mp hf
  refine ⟨s, hs, hkill _ (awayPoly s) ?_⟩
  simpa only [awayPoly, Polynomial.coe_mapRingHom, Polynomial.map_C] using
    (IsLocalization.Away.algebraMap_isUnit s).map Polynomial.C

#audit_closed_axioms GroupApproximation.BooneHigmanLinear.Tulenbaev.stAtMaximalFiniteStage

variable {n₀ : ℕ}

/-! ### Patching two localizations (Tulenbaev, Lemma 2.5) -/

/-- **Tulenbaev, Lemma 2.5**, from the dilation principle. If `a, b` are coprime,
`α ∈ St_N(A[X])` has `α(0) = 1`, and `α ↦ 1` over `A_a` and over `A_b`, then `α = 1`. -/
theorem eq_one_of_coprime (hD : StDilationStatementAt n₀) {A : Type} [CommRing A] {N : ℕ}
    (hN : n₀ ≤ N) {a b : A} (hab : IsCoprime a b) {α : SteinbergGroup (Fin N) A[X]}
    (h0 : ringMap (Polynomial.evalRingHom (0 : A)) α = 1)
    (ha : ringMap (awayPoly a) α = 1) (hb : ringMap (awayPoly b) α = 1) : α = 1 := by
  -- `β(X, Z) = α(X) α((1 + Z) X)⁻¹` over the base ring `A[X]`
  have hev_C : (Polynomial.evalRingHom (0 : A[X])).comp (Polynomial.C : A[X] →+* (A[X])[X]) =
      RingHom.id A[X] := by
    apply Polynomial.ringHom_ext <;> intros <;> simp
  have hev_φ : (Polynomial.evalRingHom (0 : A[X])).comp (shiftMul A) = RingHom.id A[X] := by
    apply Polynomial.ringHom_ext
    · intro c
      simp
    · simp
  have hβ0 : ringMap (Polynomial.evalRingHom (0 : A[X]))
      (ringMap (Polynomial.C : A[X] →+* (A[X])[X]) α * (ringMap (shiftMul A) α)⁻¹) = 1 := by
    rw [map_mul, map_inv, ringMap_ringMap, ringMap_ringMap, hev_C, hev_φ, ringMap_id,
      MonoidHom.id_apply, mul_inv_cancel]
  -- `β ↦ 1` over `A[X]_b`
  have hu : IsUnit ((((Polynomial.C : Localization.Away (Polynomial.C b : A[X]) →+* _).comp
      (algebraMap A[X] (Localization.Away (Polynomial.C b : A[X])))).comp
        (Polynomial.C : A →+* A[X])) b) :=
    (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (Polynomial.C b : A[X]))
      (Polynomial.C b : A[X])).map Polynomial.C
  have hcompC : (awayPoly (Polynomial.C b : A[X])).comp (Polynomial.C : A[X] →+* (A[X])[X]) =
      (Polynomial.eval₂RingHom (IsLocalization.Away.lift (S := Localization.Away b) b hu)
        (Polynomial.C (algebraMap A[X] (Localization.Away (Polynomial.C b : A[X])) Polynomial.X))).comp
        (awayPoly b) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [awayPoly]
    · simp [awayPoly]
  have hcompφ : (awayPoly (Polynomial.C b : A[X])).comp (shiftMul A) =
      (Polynomial.eval₂RingHom (IsLocalization.Away.lift (S := Localization.Away b) b hu)
        ((1 + Polynomial.X) *
          Polynomial.C (algebraMap A[X] (Localization.Away (Polynomial.C b : A[X])) Polynomial.X))).comp
        (awayPoly b) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [awayPoly]
    · simp [awayPoly]
  have hβb : ringMap (awayPoly (Polynomial.C b : A[X]))
      (ringMap (Polynomial.C : A[X] →+* (A[X])[X]) α * (ringMap (shiftMul A) α)⁻¹) = 1 := by
    rw [map_mul, map_inv, ringMap_ringMap, ringMap_ringMap, hcompC, hcompφ, ← ringMap_ringMap,
      ← ringMap_ringMap, hb, map_one, map_one, inv_one, one_mul]
  -- dilate `β` at `b` and `α` at `a`
  obtain ⟨n₁, hn₁⟩ := hD A[X] N hN (Polynomial.C b) _ hβ0 hβb
  obtain ⟨n₂, hn₂⟩ := hD A N hN a α h0 ha
  set n := max n₁ n₂ with hn
  obtain ⟨s, d, hsd⟩ := hab.pow (m := n) (n := n)
  have hβn := hn₁ n ((le_max_left n₁ n₂).trans_eq hn.symm)
  have hαn := hn₂ n ((le_max_right n₁ n₂).trans_eq hn.symm)
  -- evaluate `Z ↦ -d` (compositions associate to the left, as `ringMap_ringMap` produces them)
  have hεC : ((Polynomial.evalRingHom (Polynomial.C (-d) : A[X])).comp
      (dil ((Polynomial.C b : A[X]) ^ n))).comp (Polynomial.C : A[X] →+* (A[X])[X]) =
      RingHom.id A[X] := by
    apply Polynomial.ringHom_ext <;> intros <;> simp
  have hεφ : ((Polynomial.evalRingHom (Polynomial.C (-d) : A[X])).comp
      (dil ((Polynomial.C b : A[X]) ^ n))).comp (shiftMul A) = dil (s * a ^ n) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp
    · have h1 : (Polynomial.C (s * a ^ n) : A[X]) =
          1 + (Polynomial.C b : A[X]) ^ n * Polynomial.C (-d) := by
        rw [← map_pow, ← map_mul, ← map_one (Polynomial.C : A →+* A[X]), ← map_add]
        congr 1
        linear_combination hsd
      rw [RingHom.comp_apply, RingHom.comp_apply, shiftMul_X, dil_X, h1]
      simp
  have hkey := congrArg (ringMap (I := Fin N) (Polynomial.evalRingHom (Polynomial.C (-d) : A[X])))
    hβn
  rw [map_one, map_mul, map_inv, map_mul, map_inv, ringMap_ringMap, ringMap_ringMap,
    ringMap_ringMap, ringMap_ringMap, hεC, hεφ, ringMap_id, MonoidHom.id_apply,
    ← dil_comp, ← ringMap_ringMap, hαn, map_one, inv_one, mul_one] at hkey
  exact hkey

#audit_axioms GroupApproximation.BooneHigmanLinear.Tulenbaev.eq_one_of_coprime

/-! ### The ideal of good localizations (Tulenbaev, proof of Thm 2.1) -/

theorem away_zero_eq_one {A : Type} [CommRing A] {N : ℕ} (α : SteinbergGroup (Fin N) A[X]) :
    ringMap (awayPoly (0 : A)) α = 1 := by
  haveI : Subsingleton (Localization.Away (0 : A)) :=
    IsLocalization.subsingleton (M := Submonoid.powers (0 : A))
      (S := Localization.Away (0 : A)) (Submonoid.mem_powers 0)
  haveI : Subsingleton (Localization.Away (0 : A))[X] :=
    Polynomial.subsingleton_iff_subsingleton.mpr inferInstance
  exact steinberg_eq_one_of_subsingleton _

#audit_axioms GroupApproximation.BooneHigmanLinear.Tulenbaev.away_zero_eq_one

theorem away_mul_eq_one {A : Type} [CommRing A] {N : ℕ} {α : SteinbergGroup (Fin N) A[X]}
    {c : A} (hc : ringMap (awayPoly c) α = 1) (r : A) : ringMap (awayPoly (r * c)) α = 1 := by
  have hu : IsUnit (algebraMap A (Localization.Away (r * c)) c) :=
    isUnit_of_mul_isUnit_right (x := algebraMap A (Localization.Away (r * c)) r)
      (by rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit (r * c))
  have hcomp : awayPoly (r * c) =
      (Polynomial.mapRingHom (IsLocalization.Away.lift (S := Localization.Away c) c hu)).comp
        (awayPoly c) := by
    simp only [awayPoly, Polynomial.mapRingHom_comp, IsLocalization.Away.lift_comp]
  rw [hcomp, ← ringMap_ringMap, hc, map_one]

#audit_axioms GroupApproximation.BooneHigmanLinear.Tulenbaev.away_mul_eq_one

/-- Over `A' = A_c`, the images of `a ∈ A` with `α_a = 1` still have `α'_a = 1`. -/
theorem away_away_eq_one {A : Type} [CommRing A] {N : ℕ} {α : SteinbergGroup (Fin N) A[X]}
    (c a : A) (ha : ringMap (awayPoly a) α = 1) :
    ringMap (awayPoly (algebraMap A (Localization.Away c) a)) (ringMap (awayPoly c) α) = 1 := by
  have hu : IsUnit (((algebraMap (Localization.Away c)
      (Localization.Away (algebraMap A (Localization.Away c) a))).comp
        (algebraMap A (Localization.Away c))) a) :=
    IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away (algebraMap A (Localization.Away c) a))
      (algebraMap A (Localization.Away c) a)
  have hcomp : (awayPoly (algebraMap A (Localization.Away c) a)).comp (awayPoly c) =
      (Polynomial.mapRingHom (IsLocalization.Away.lift (S := Localization.Away a) a hu)).comp
        (awayPoly a) := by
    simp only [awayPoly, Polynomial.mapRingHom_comp, IsLocalization.Away.lift_comp]
  rw [ringMap_ringMap, hcomp, ← ringMap_ringMap, ha, map_one]

#audit_axioms GroupApproximation.BooneHigmanLinear.Tulenbaev.away_away_eq_one

theorem away_add_eq_one (hD : StDilationStatementAt n₀) {A : Type} [CommRing A] {N : ℕ}
    (hN : n₀ ≤ N) {α : SteinbergGroup (Fin N) A[X]}
    (h0 : ringMap (Polynomial.evalRingHom (0 : A)) α = 1) {a b : A}
    (ha : ringMap (awayPoly a) α = 1) (hb : ringMap (awayPoly b) α = 1) :
    ringMap (awayPoly (a + b)) α = 1 := by
  have hev : (Polynomial.evalRingHom (0 : Localization.Away (a + b))).comp (awayPoly (a + b)) =
      (algebraMap A (Localization.Away (a + b))).comp (Polynomial.evalRingHom 0) := by
    apply Polynomial.ringHom_ext <;> intros <;> simp [awayPoly]
  have h0' : ringMap (Polynomial.evalRingHom (0 : Localization.Away (a + b)))
      (ringMap (awayPoly (a + b)) α) = 1 := by
    rw [ringMap_ringMap, hev, ← ringMap_ringMap, h0, map_one]
  have hcop : IsCoprime (algebraMap A (Localization.Away (a + b)) a)
      (algebraMap A (Localization.Away (a + b)) b) := by
    obtain ⟨u, hu⟩ := (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (a + b))
      (a + b)).exists_left_inv
    exact ⟨u, u, by rw [← mul_add, ← map_add, hu]⟩
  exact eq_one_of_coprime hD hN hcop h0' (away_away_eq_one (a + b) a ha)
    (away_away_eq_one (a + b) b hb)

#audit_axioms GroupApproximation.BooneHigmanLinear.Tulenbaev.away_add_eq_one

/-- **The ideal of good localizations**: the `c ∈ A` with `α ↦ 1` in `St_N(A_c[X])`. -/
def goodIdeal (hD : StDilationStatementAt n₀) {A : Type} [CommRing A] {N : ℕ} (hN : n₀ ≤ N)
    (α : SteinbergGroup (Fin N) A[X]) (h0 : ringMap (Polynomial.evalRingHom (0 : A)) α = 1) :
    Ideal A where
  carrier := {c | ringMap (awayPoly c) α = 1}
  add_mem' := fun ha hb => away_add_eq_one hD hN h0 ha hb
  zero_mem' := away_zero_eq_one α
  smul_mem' := fun r {_} hc => away_mul_eq_one hc r

theorem mem_goodIdeal (hD : StDilationStatementAt n₀) {A : Type} [CommRing A] {N : ℕ}
    (hN : n₀ ≤ N) {α : SteinbergGroup (Fin N) A[X]}
    (h0 : ringMap (Polynomial.evalRingHom (0 : A)) α = 1) (c : A) :
    c ∈ goodIdeal hD hN α h0 ↔ ringMap (awayPoly c) α = 1 :=
  Iff.rfl

/-- `α ↦ 1` over `A_1 ≅ A` means `α = 1`. -/
theorem eq_one_of_away_one {A : Type} [CommRing A] {N : ℕ} {α : SteinbergGroup (Fin N) A[X]}
    (h1 : ringMap (awayPoly (1 : A)) α = 1) : α = 1 := by
  have hu : IsUnit ((RingHom.id A) 1) := isUnit_one
  have hcomp : (Polynomial.mapRingHom
      (IsLocalization.Away.lift (S := Localization.Away (1 : A)) (1 : A) hu)).comp
        (awayPoly (1 : A)) = RingHom.id A[X] := by
    simp only [awayPoly, Polynomial.mapRingHom_comp, IsLocalization.Away.lift_comp,
      Polynomial.mapRingHom_id]
  calc α = ringMap (RingHom.id A[X]) α := by rw [ringMap_id, MonoidHom.id_apply]
    _ = 1 := by rw [← hcomp, ← ringMap_ringMap, h1, map_one]

#audit_axioms GroupApproximation.BooneHigmanLinear.Tulenbaev.eq_one_of_away_one

theorem eq_one_of_one_mem_goodIdeal (hD : StDilationStatementAt n₀) {A : Type} [CommRing A]
    {N : ℕ} (hN : n₀ ≤ N) {α : SteinbergGroup (Fin N) A[X]}
    (h0 : ringMap (Polynomial.evalRingHom (0 : A)) α = 1) (h1 : (1 : A) ∈ goodIdeal hD hN α h0) :
    α = 1 :=
  eq_one_of_away_one h1

/-! ### The local–global principle (Tulenbaev, Thm 2.1) -/

/-- **Tulenbaev, Thm 2.1, Zariski form**, from the dilation principle. If `α(0) = 1` and, for
every maximal ideal `𝔪`, `α ↦ 1` over some `A_s`, `s ∉ 𝔪`, then `α = 1`. -/
theorem eq_one_of_away (hD : StDilationStatementAt n₀) {A : Type} [CommRing A] {N : ℕ}
    (hN : n₀ ≤ N) {α : SteinbergGroup (Fin N) A[X]}
    (h0 : ringMap (Polynomial.evalRingHom (0 : A)) α = 1)
    (hloc : ∀ M : Ideal A, M.IsMaximal → ∃ s ∉ M, ringMap (awayPoly s) α = 1) : α = 1 := by
  apply eq_one_of_one_mem_goodIdeal hD hN h0
  have htop : goodIdeal hD hN α h0 = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨s, hsM, hs⟩ := hloc M hM
    exact hsM (hle ((mem_goodIdeal hD hN h0 s).mpr hs))
  rw [htop]
  exact Submodule.mem_top

#audit_axioms GroupApproximation.BooneHigmanLinear.Tulenbaev.eq_one_of_away

/-- **Tulenbaev, Thm 2.1, kernel form**: `α(0) = 1` and `α_𝔪 = 1` for every maximal `𝔪` give
`α = 1`, from the dilation principle. The finite-stage principle is proved above. -/
theorem eq_one_of_atMaximal (hD : StDilationStatementAt n₀)
    {A : Type} [CommRing A] {N : ℕ} (hN : n₀ ≤ N)
    {α : SteinbergGroup (Fin N) A[X]} (h0 : ringMap (Polynomial.evalRingHom (0 : A)) α = 1)
    (hM : ∀ (M : Ideal A) [M.IsMaximal],
      ringMap (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime M))) α = 1) : α = 1 :=
  eq_one_of_away hD hN h0 fun M hM' => by
    haveI := hM'
    exact stAtMaximalFiniteStage A N M α (hM M)

#audit_axioms GroupApproximation.BooneHigmanLinear.Tulenbaev.eq_one_of_atMaximal

/-- **Components' `StLocalGlobalStatementAt n₀`** (constancy form) from dilation alone. -/
theorem stLocalGlobal_of_dilation (hD : StDilationStatementAt n₀) :
    StLocalGlobalStatementAt n₀ := by
  intro A _ N hN g hg
  have hevC : (Polynomial.evalRingHom (0 : A)).comp (Polynomial.C : A →+* A[X]) =
      RingHom.id A := RingHom.ext fun c => by simp
  have key : g * (ringMap (Polynomial.C : A →+* A[X])
      (ringMap (Polynomial.evalRingHom (0 : A)) g))⁻¹ = 1 := by
    apply eq_one_of_atMaximal hD hN
    · rw [map_mul, map_inv, ringMap_ringMap (Polynomial.evalRingHom (0 : A)) Polynomial.C, hevC,
        ringMap_id, MonoidHom.id_apply, mul_inv_cancel]
    · intro M _
      have hmapC : (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime M))).comp
          (Polynomial.C : A →+* A[X]) =
          (Polynomial.C : Localization.AtPrime M →+* _).comp
            (algebraMap A (Localization.AtPrime M)) :=
        RingHom.ext fun c => by simp
      rw [map_mul, map_inv, hg M,
        ringMap_ringMap (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime M)))
          (Polynomial.C : A →+* A[X]), hmapC, ← ringMap_ringMap, mul_inv_cancel]
  exact mul_inv_eq_one.mp key

#audit_axioms GroupApproximation.BooneHigmanLinear.Tulenbaev.stLocalGlobal_of_dilation

/-! ### LG-stable: dying after padding is local -/

/-- **LG-stable, Zariski form.** If `u ∈ St_N(A[X])` has `u(0) = 1` and, for every maximal `𝔪`,
dies after padding over some `A_s`, `s ∉ 𝔪`, then `u` dies after padding. -/
theorem diesAfterPadding_of_away (hD : StDilationStatementAt n₀) {A : Type} [CommRing A]
    {N : ℕ} (hN : n₀ ≤ N) {u : SteinbergGroup (Fin N) A[X]}
    (h0 : ringMap (Polynomial.evalRingHom (0 : A)) u = 1)
    (hloc : ∀ M : Ideal A, M.IsMaximal → ∃ s ∉ M, ∃ N' : ℕ, ∃ h : N ≤ N',
      ringMap (awayPoly s) (indexMap (Fin.castLEEmb h) u) = 1) :
    ∃ N' : ℕ, ∃ h : N ≤ N', indexMap (Fin.castLEEmb h) u = 1 := by
  classical
  let S : Set A := {s | ∃ N' : ℕ, ∃ h : N ≤ N',
    ringMap (awayPoly s) (indexMap (Fin.castLEEmb h) u) = 1}
  have hspan : Ideal.span S = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨s, hsM, hs⟩ := hloc M hM
    have hsS : s ∈ S := hs
    exact hsM (hle (Ideal.subset_span hsS))
  have h1 : (1 : A) ∈ Ideal.span S := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨T, hTS, hT⟩ := Submodule.mem_span_finite_of_mem_span h1
  have hS : ∀ t ∈ S, ∃ N' : ℕ, ∃ h : N ≤ N',
      ringMap (awayPoly t) (indexMap (Fin.castLEEmb h) u) = 1 := fun t ht => ht
  choose! NT hNT hNTu using hS
  set N' := max N (T.sup NT) with hN'
  have hNN' : N ≤ N' := le_max_left _ _
  have hTN' : ∀ t ∈ T, NT t ≤ N' := fun t ht => (Finset.le_sup ht).trans (le_max_right _ _)
  have h0' : ringMap (Polynomial.evalRingHom (0 : A)) (indexMap (Fin.castLEEmb hNN') u) = 1 := by
    rw [ringMap_indexMap_comm, h0, map_one]
  refine ⟨N', hNN', eq_one_of_one_mem_goodIdeal hD (hN.trans hNN') h0' ?_⟩
  have hsub : (T : Set A) ⊆ (goodIdeal hD (hN.trans hNN') _ h0' : Set A) := by
    intro t ht
    have htS : t ∈ S := hTS ht
    rw [SetLike.mem_coe, mem_goodIdeal]
    have hpad := indexMap_castLEEmb_trans (hNT t htS) (hTN' t ht) u
    rw [← hpad, ringMap_indexMap_comm, hNTu t htS, map_one]
  exact (Ideal.span_le.mpr hsub) hT

#audit_axioms GroupApproximation.BooneHigmanLinear.Tulenbaev.diesAfterPadding_of_away

/-- **LG-stable, maximal-ideal form**, from dilation alone. -/
theorem diesAfterPadding_of_atMaximal (hD : StDilationStatementAt n₀)
    {A : Type} [CommRing A] {N : ℕ} (hN : n₀ ≤ N)
    {u : SteinbergGroup (Fin N) A[X]} (h0 : ringMap (Polynomial.evalRingHom (0 : A)) u = 1)
    (hM : ∀ (M : Ideal A) [M.IsMaximal], ∃ N' : ℕ, ∃ h : N ≤ N',
      ringMap (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime M)))
        (indexMap (Fin.castLEEmb h) u) = 1) :
    ∃ N' : ℕ, ∃ h : N ≤ N', indexMap (Fin.castLEEmb h) u = 1 :=
  diesAfterPadding_of_away hD hN h0 fun M hM' => by
    haveI := hM'
    obtain ⟨N', h, hu⟩ := hM M
    obtain ⟨s, hsM, hs⟩ := stAtMaximalFiniteStage A N' M _ hu
    exact ⟨s, hsM, N', h, hs⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.Tulenbaev.diesAfterPadding_of_atMaximal

end

end Tulenbaev
end BooneHigmanLinear
end GroupApproximation
