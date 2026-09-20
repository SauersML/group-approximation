import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Commute
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination
import GroupApproximation.Meta.AxiomGuard

/-!
# The map `S_α(a, -)` of Lavrenov–Sinchuk §5.3, in the abstract (k2-poly H.L4)

A. Lavrenov, S. Sinchuk, *A Horrocks-type theorem for even orthogonal K₂*, Doc. Math. 25
(2020), arXiv:1909.02637, §5.3: Def 5.26, Lemma 5.27, Cor 5.29 and Lemma 5.30. Lane k2-hl4c.

This file is group theory only. The Steinberg inputs enter through the fields of `SData` and
`PData` and through explicit hypotheses, which `LSCore/SMap.lean` discharges in
`St_I(A[X, X⁻¹])`. For a root `α`:
* `D.y c = x_α(c X⁻¹)`, additive in `c` (`SData.y_add`);
* `D.sym u = {X, u}` for units `u`, multiplicative and central (`SData.sym_mul`,
  `SData.sym_central`);
* `P.P0 = P_α(0)` and `P.xn m = x_{-α}(m X)`, which normalizes `P_α(0)` for `m ∈ M` (L–S 5.9).
  The coset `P_α(m) = P_α(0) · x_{-α}(m X)` is `PData.InCoset`.

`sMapAt a m g` is L–S (5.11) on the coset `P_α(m)`:
`S_α(a, g) = x_α(aX⁻¹) · g · x_α(-(a/(1+am)) X⁻¹) · {X, 1+am}`, with
`a/(1+am) = a * Ring.inverse (1 + a * m)`. The map `S_α(a, -)` on `P_α(*)` is
`sMapAt a (p_α g) g`, with `p_α` the invariant of L–S 5.9.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace LSCore
namespace SMapCore

variable {G A : Type*} [Group G] [CommRing A]

theorem addFn_zero {f : A → G} (hf : ∀ b c : A, f (b + c) = f b * f c) : f 0 = 1 := by
  have h := hf 0 0
  rw [add_zero] at h
  calc f 0 = (f 0)⁻¹ * (f 0 * f 0) := by group
    _ = 1 := by rw [← h, inv_mul_cancel]

theorem addFn_neg {f : A → G} (hf : ∀ b c : A, f (b + c) = f b * f c) (c : A) :
    f (-c) = (f c)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← hf, neg_add_cancel, addFn_zero hf])

/-- `1 + a(m + m') = (1 + am)(1 + (a/(1+am)) m')`. -/
theorem one_add_split {a m : A} (m' : A) (hu : IsUnit (1 + a * m)) :
    1 + a * (m + m') = (1 + a * m) * (1 + a * Ring.inverse (1 + a * m) * m') := by
  have hi := Ring.mul_inverse_cancel _ hu
  linear_combination (-(a * m')) * hi

/-- `(a/(1+am)) / (1 + (a/(1+am)) m') = a / (1 + a(m + m'))`. -/
theorem inverse_split {a m : A} (m' : A) (hu : IsUnit (1 + a * m)) :
    a * Ring.inverse (1 + a * m) * Ring.inverse (1 + a * Ring.inverse (1 + a * m) * m') =
      a * Ring.inverse (1 + a * (m + m')) := by
  rw [one_add_split m' hu, Ring.mul_inverse_rev]
  ring

/-- The Steinberg data behind L–S Def 5.26, for one root `α`. -/
structure SData (G A : Type*) [Group G] [CommRing A] where
  /-- `y c = x_α(c X⁻¹)`. -/
  y : A → G
  y_add : ∀ b c : A, y (b + c) = y b * y c
  /-- `sym u = {X, u}`. -/
  sym : A → G
  sym_mul : ∀ u v : A, IsUnit u → IsUnit v → sym (u * v) = sym u * sym v
  sym_central : ∀ (u : A) (g : G), IsUnit u → Commute (sym u) g

namespace SData

variable (D : SData G A)

theorem y_neg (c : A) : D.y (-c) = (D.y c)⁻¹ :=
  addFn_neg D.y_add c

theorem sym_one : D.sym 1 = 1 := by
  have h := D.sym_mul 1 1 isUnit_one isUnit_one
  rw [mul_one] at h
  calc D.sym 1 = (D.sym 1)⁻¹ * (D.sym 1 * D.sym 1) := by group
    _ = 1 := by rw [← h, inv_mul_cancel]

/-- **L–S (5.11)**, Def 5.26, on the coset `P_α(m)`. -/
noncomputable def sMapAt (a m : A) (g : G) : G :=
  D.y a * g * D.y (-(a * Ring.inverse (1 + a * m))) * D.sym (1 + a * m)

/-- L–S after Def 5.26: on `P_α(0)` the map is conjugation by `x_α(aX⁻¹)`. -/
theorem sMapAt_zero (a : A) (g : G) : D.sMapAt a 0 g = D.y a * g * (D.y a)⁻¹ := by
  unfold sMapAt
  rw [mul_zero, add_zero, Ring.inverse_one, mul_one, D.sym_one, mul_one, D.y_neg]

#audit_axioms GroupApproximation.BooneHigmanLinear.LSCore.SMapCore.SData.sMapAt_zero

/-- A factor from `P_α(0)` on the left comes out conjugated by `x_α(aX⁻¹)`. -/
theorem sMapAt_mul_left (a m : A) (g₀ g : G) :
    D.sMapAt a m (g₀ * g) = D.y a * g₀ * (D.y a)⁻¹ * D.sMapAt a m g := by
  unfold sMapAt
  group

/-- **L–S Lemma 5.27**: `S_α(a, g₁ g₂) = S_α(a, g₁) · S_α(a/(1+am), g₂)` for `g₁ ∈ P_α(m)` and
`g₂ ∈ P_α(m')`. -/
theorem sMapAt_mul (a m m' : A) (g₁ g₂ : G) (hu : IsUnit (1 + a * m))
    (hw : IsUnit (1 + a * (m + m'))) :
    D.sMapAt a (m + m') (g₁ * g₂) =
      D.sMapAt a m g₁ * D.sMapAt (a * Ring.inverse (1 + a * m)) m' g₂ := by
  have hsplit := one_add_split m' hu
  have hv : IsUnit (1 + a * Ring.inverse (1 + a * m) * m') := by
    rw [hsplit] at hw
    exact isUnit_of_mul_isUnit_right hw
  unfold sMapAt
  rw [← inverse_split m' hu, hsplit, D.sym_mul _ _ hu hv]
  set a' := a * Ring.inverse (1 + a * m)
  set Z := D.y (-(a' * Ring.inverse (1 + a' * m')))
  have hYY : D.y (-a') * D.y a' = 1 := by rw [← D.y_add, neg_add_cancel, addFn_zero D.y_add]
  have hc := (D.sym_central (1 + a * m) (D.y a' * g₂ * Z) hu).eq
  calc D.y a * (g₁ * g₂) * Z * (D.sym (1 + a * m) * D.sym (1 + a' * m'))
      = D.y a * g₁ * (D.y (-a') * D.y a') * g₂ * Z * D.sym (1 + a * m) *
          D.sym (1 + a' * m') := by
        rw [hYY]; group
    _ = D.y a * g₁ * D.y (-a') * (D.y a' * g₂ * Z * D.sym (1 + a * m)) *
          D.sym (1 + a' * m') := by
        group
    _ = D.y a * g₁ * D.y (-a') * D.sym (1 + a * m) *
          (D.y a' * g₂ * Z * D.sym (1 + a' * m')) := by
        rw [← hc]; group

#audit_axioms GroupApproximation.BooneHigmanLinear.LSCore.SMapCore.SData.sMapAt_mul

end SData

/-- The coset data of L–S 5.9 for one root `α`: `P0 = P_α(0)` and `xn m = x_{-α}(m X)`. -/
structure PData (G A : Type*) [Group G] [CommRing A] (M : Ideal A) where
  P0 : Subgroup G
  /-- `xn m = x_{-α}(m X)`. -/
  xn : A → G
  xn_add : ∀ b c : A, xn (b + c) = xn b * xn c
  xn_normal : ∀ m ∈ M, ∀ g ∈ P0, xn m * g * (xn m)⁻¹ ∈ P0

namespace PData

variable {M : Ideal A} (P : PData G A M)

/-- `g ∈ P_α(m) = P_α(0) · x_{-α}(m X)`. -/
def InCoset (m : A) (g : G) : Prop :=
  ∃ g₀ ∈ P.P0, g = g₀ * P.xn m

/-- `g₀ · x_{-α}(mX) · s ∈ P_α(m)` for `g₀, s ∈ P_α(0)`, since `x_{-α}(mX)` normalizes `P_α(0)`. -/
theorem inCoset_mul_right {m : A} (hm : m ∈ M) {g₀ s : G} (hg₀ : g₀ ∈ P.P0) (hs : s ∈ P.P0) :
    P.InCoset m (g₀ * P.xn m * s) := by
  refine ⟨g₀ * (P.xn m * s * (P.xn m)⁻¹), P.P0.mul_mem hg₀ (P.xn_normal m hm s hs), ?_⟩
  group

end PData

variable (D : SData G A)

/-- **L–S Cor 5.29**, abstract: for `g ∈ P_α(m)`, `S_α(a, g) · h_α(1+am)⁻¹ ∈ P_α(m/(1+am))`.
`hconj` is L–S Lemma 5.24. `h528` is L–S Lemma 5.28, with `s = ⟨a, m⟩_α ∈ P_α(0)` (L–S 5.11)
and `hh = h_α(1+am)`. -/
theorem sMapAt_inCoset {M : Ideal A} (P : PData G A M) (a m : A) (hm : m ∈ M)
    (hconj : ∀ g₀ ∈ P.P0, D.y a * g₀ * (D.y a)⁻¹ ∈ P.P0)
    (hh s : G) (hs : s ∈ P.P0)
    (h528 : D.sMapAt a m (P.xn m) = P.xn (m * Ring.inverse (1 + a * m)) * s * hh)
    {g : G} (hg : P.InCoset m g) :
    P.InCoset (m * Ring.inverse (1 + a * m)) (D.sMapAt a m g * hh⁻¹) := by
  obtain ⟨g₀, hg₀, rfl⟩ := hg
  have hc : m * Ring.inverse (1 + a * m) ∈ M := by
    rw [mul_comm m]
    exact M.mul_mem_left _ hm
  have key := P.inCoset_mul_right hc (hconj g₀ hg₀) hs
  have e : D.sMapAt a m (g₀ * P.xn m) * hh⁻¹ =
      D.y a * g₀ * (D.y a)⁻¹ * P.xn (m * Ring.inverse (1 + a * m)) * s := by
    rw [D.sMapAt_mul_left, h528]
    group
  rw [e]
  exact key

#audit_axioms GroupApproximation.BooneHigmanLinear.LSCore.SMapCore.sMapAt_inCoset

/-- **L–S Lemma 5.30**, abstract. Take `g = g₀ · x_{-α}(mX) · x_{-β}(m'X)` with
`g₀ ∈ K(α, β)` (L–S Prop 5.17), `z t = x_{α-β}(t)` and `e = N_{α,-β}`. Then
`S_α(a, g) · h_α(1+am)⁻¹ · x_{α-β}(-e a m') ∈ P_β(m'/(1+am))`.
The hypotheses are:
* `hK`: L–S Cor 5.23;
* `hR2`: (R2), `x_{-β}(tX)^{x_α(cX⁻¹)} = x_{-β}(tX) · x_{α-β}(e c t)`;
* `h528`: L–S Lemma 5.28, with `s = ⟨a, m⟩_α`;
* `hxa`, `hs`: `x_{-α}(M X)` and `⟨a, m⟩_α` lie in `P_β(0)` (L–S 5.8, 5.11);
* `hhb`, `hhz`: (2.10) for `hh = h_α(1+am)` against `x_{-β}` and `x_{α-β}`. -/
theorem sMapAt_pair_inCoset {M : Ideal A} (Pα Pβ : PData G A M) (K : Subgroup G)
    (z : A → G) (hz : ∀ b c : A, z (b + c) = z b * z c) (e a m m' : A)
    (hu : IsUnit (1 + a * m))
    (hK : ∀ g₀ ∈ K, D.y a * g₀ * (D.y a)⁻¹ ∈ Pβ.P0)
    (hR2 : ∀ c t : A, D.y c * Pβ.xn t * (D.y c)⁻¹ = Pβ.xn t * z (e * c * t))
    (hh s : G) (hs : s ∈ Pβ.P0)
    (hxa : Pα.xn (m * Ring.inverse (1 + a * m)) ∈ Pβ.P0)
    (h528 : D.sMapAt a m (Pα.xn m) = Pα.xn (m * Ring.inverse (1 + a * m)) * s * hh)
    (hhb : hh * Pβ.xn m' = Pβ.xn (m' * Ring.inverse (1 + a * m)) * hh)
    (hhz : ∀ t : A, hh * z t = z ((1 + a * m) * t) * hh)
    {g₀ : G} (hg₀ : g₀ ∈ K) :
    Pβ.InCoset (m' * Ring.inverse (1 + a * m))
      (D.sMapAt a m (g₀ * Pα.xn m * Pβ.xn m') * hh⁻¹ * z (-(e * a * m'))) := by
  have hw : IsUnit (1 + a * (m + 0)) := by rwa [add_zero]
  have hsplit : D.sMapAt a m (Pα.xn m * Pβ.xn m') =
      D.sMapAt a m (Pα.xn m) * D.sMapAt (a * Ring.inverse (1 + a * m)) 0 (Pβ.xn m') := by
    have h := D.sMapAt_mul a m 0 (Pα.xn m) (Pβ.xn m') hu hw
    rwa [add_zero] at h
  have hzz : z ((1 + a * m) * (e * (a * Ring.inverse (1 + a * m)) * m')) *
      z (-(e * a * m')) = 1 := by
    have hi := Ring.mul_inverse_cancel _ hu
    have h0 : (1 + a * m) * (e * (a * Ring.inverse (1 + a * m)) * m') + -(e * a * m') = 0 := by
      linear_combination (e * a * m') * hi
    rw [← hz, h0, addFn_zero hz]
  refine ⟨D.y a * g₀ * (D.y a)⁻¹ * Pα.xn (m * Ring.inverse (1 + a * m)) * s,
    Pβ.P0.mul_mem (Pβ.P0.mul_mem (hK g₀ hg₀) hxa) hs, ?_⟩
  rw [mul_assoc g₀, D.sMapAt_mul_left, hsplit, h528, D.sMapAt_zero, hR2]
  calc _ = D.y a * g₀ * (D.y a)⁻¹ * Pα.xn (m * Ring.inverse (1 + a * m)) * s *
          (hh * Pβ.xn m') * z (e * (a * Ring.inverse (1 + a * m)) * m') * hh⁻¹ *
          z (-(e * a * m')) := by
        group
    _ = D.y a * g₀ * (D.y a)⁻¹ * Pα.xn (m * Ring.inverse (1 + a * m)) * s *
          Pβ.xn (m' * Ring.inverse (1 + a * m)) *
          (hh * z (e * (a * Ring.inverse (1 + a * m)) * m')) * hh⁻¹ * z (-(e * a * m')) := by
        rw [hhb]; group
    _ = D.y a * g₀ * (D.y a)⁻¹ * Pα.xn (m * Ring.inverse (1 + a * m)) * s *
          Pβ.xn (m' * Ring.inverse (1 + a * m)) *
          (z ((1 + a * m) * (e * (a * Ring.inverse (1 + a * m)) * m')) *
            z (-(e * a * m'))) := by
        rw [hhz]; group
    _ = _ := by rw [hzz, mul_one]

#audit_axioms GroupApproximation.BooneHigmanLinear.LSCore.SMapCore.sMapAt_pair_inCoset

end SMapCore
end LSCore
end BooneHigmanLinear
end GroupApproximation
