import GroupApproximation.CharClass.OddPRedPow
import GroupApproximation.CharClass.OddPWDiagonalRing
import GroupApproximation.CharClass.ChernTotalRingOf
import GroupApproximation.CharClass.CohomologyKunnethTorusOf
import GroupApproximation.CharClass.KroneckerSphere
import Mathlib.Algebra.Field.ZMod
import GroupApproximation.Meta.AxiomGuard

/-!
# The `T²` corner of the Cartan formula at an odd prime

For degree-one classes `x, y` the D-form Cartan formula at the index `2(p − 1)` reads, in the total ring,

    [D_{2(p−1)}(x ⌣ y)] = Σ_{a + b = 2(p−1), a ≤ p, b ≤ p} κ(a, b) · [D_a x] · [D_b y],

with `κ(a, b) = (−1)^{p(p−1)/2} · c̄_{a,b} · (−1)^{b(p − a)}` and `c̄_{a,b} = wdPhi p a b 1 1`.  Only
`a ∈ {p − 2, p − 1, p}` occur, in degrees `(2, 0)`, `(1, 1)` and `(0, 2)`.  When `x` and `y` are pulled back
from circles, every class of degree two on a circle is zero, so only `a = p − 1` survives.  Its coefficient
is `(−1)^{(p−1)/2}` (`kappa_main`):

    [D_{2(p−1)}(x ⌣ y)] = (−1)^{(p−1)/2} · [D_{p−1} x] · [D_{p−1} y].

On the torus `S¹ × S¹`, with `P⁰ = c · id` in degree one, the top class `t_S ⌣ t_Y ≠ 0` therefore carries
the degree-two constant `(−1)^{(p−1)/2} c²`.  This constant is unique and a unit whenever `c` is one.  With
lane `lx-toppower`'s `c = ((p − 1)/2)!` it is the `P⁰` constant in degree two.

## The two inputs, as named propositions

* `CornerCartan p hp` — the formula above for two degree-one classes of any space.  It is the instance
  `q = q' = 1`, `i = 2(p − 1)` of lane `lx-cartan-b`'s `totalOf_oddDClass_cup` (`CharClass/OddPCompare.lean`),
  and `kappa p a b` is `cartanCoeffP p 1 1 a b` by definition, so the discharge is
  `fun X x y => totalOf_oddDClass_cup p hp X 1 1 (2 * (p - 1)) (idx_two_le p) x y`.
* `DegOneConst p hp c` — `[D_{p−1} t] = c · t` for every degree-one class of every space.  Lane
  `lx-toppower` discharges it with `c = ((p − 1)/2)!` (`TopPow.oddDClass_deg_one`).

## Main declarations

* `oddDClass_pull_circle_eq_zero` — `[D_a]` vanishes in degree `≥ 2` on a class pulled back from `S¹`.
* `kappa_main` — `κ(p − 1, p − 1) = (−1)^{p/2}`.
* `corner_pull_circle` — the corner formula for classes pulled back from circles.
* `cup_torus_ne_zero`, `torus_corner`, `torus_const_unique`, `isUnit_torus_const` — the constant of
  `[D_{2(p−1)}]` on the top class of `S¹ × S¹`: its value `(−1)^{p/2} c²`, uniqueness, and the unit property.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass
namespace OddPCartanTorus

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-! ## 1. Indices, degrees, and the total ring -/

theorem one_le : 1 ≤ p := (Fact.out : p.Prime).one_lt.le

/-- `P⁰` in degree one sits at index `p − 1`. -/
theorem idx_one_le : p - 1 ≤ p * 1 := by omega

theorem deg_one : p * 1 - (p - 1) = 1 := by
  have := one_le p
  omega

/-- `P⁰` in degree two sits at index `2(p − 1)`. -/
theorem idx_two_le : 2 * (p - 1) ≤ p * (1 + 1) := by omega

/-- A degree cast does not change a class in the total ring. -/
theorem totalOf_cohCast {X : TopCat.{0}} {m m' : ℕ} (e : m = m') (a : Hmod (ZMod p) X m) :
    TotalHOf.of (ZMod p) X m' (cohCast e a) = TotalHOf.of (ZMod p) X m a := by
  subst e
  rfl

/-- The inclusion of a degree into the total ring is linear. -/
theorem totalOf_smul {X : TopCat.{0}} {n : ℕ} (s : ZMod p) (a : TotalPieceOf (ZMod p) X n) :
    TotalHOf.of (ZMod p) X n (s • a) = s • TotalHOf.of (ZMod p) X n a :=
  map_smul (DirectSum.lof (ZMod p) ℕ (fun n : ℕ => TotalPieceOf (ZMod p) X n) n) s a

/-! ## 2. The Cartan coefficient and the two inputs -/

/-- **The Cartan coefficient `κ(a, b)` for two degree-one classes**: the riffle Koszul sign
`(−1)^{1·1·p(p−1)/2}`, the reduced coefficient `c̄_{a,b} = wdPhi p a b 1 1`, and the sign `(−1)^{b(p − a)}`.
By definition this is lane `lx-cartan-b`'s `cartanCoeffP p 1 1 a b`. -/
def kappa (a b : ℕ) : ZMod p :=
  (-1 : ZMod p) ^ (1 * 1 * (p * (p - 1) / 2)) * wdPhi p a b (1 : ZMod p) 1
    * (-1 : ZMod p) ^ (b * (p * 1 - a))

/-- **The D-form Cartan formula for two degree-one classes, at the index `2(p − 1)`**, in the total ring.

This is the instance `q = q' = 1`, `i = 2(p − 1)` of `totalOf_oddDClass_cup` (lane `lx-cartan-b`,
`CharClass/OddPCompare.lean`: the comparison of the equivariant diagonals `AW^{⊗p} ∘ Φ` and
`riffle ∘ (Φ ⊗ Φ) ∘ ψ_W`, read on classes), which discharges it verbatim.  It is named here so that the
corner computation stays below that file. -/
def CornerCartan (hp : Odd p) : Prop :=
  ∀ (X : TopCat.{0}) (x y : Hmod (ZMod p) X 1),
    TotalHOf.of (ZMod p) X (p * (1 + 1) - 2 * (p - 1))
        (oddDClass p hp (1 + 1) (2 * (p - 1)) (idx_two_le p) (cup x y))
      = ∑ ab ∈ Finset.antidiagonal (2 * (p - 1)),
          if h : ab.1 ≤ p * 1 ∧ ab.2 ≤ p * 1 then
            kappa p ab.1 ab.2 •
              (TotalHOf.of (ZMod p) X (p * 1 - ab.1) (oddDClass p hp 1 ab.1 h.1 x)
                * TotalHOf.of (ZMod p) X (p * 1 - ab.2) (oddDClass p hp 1 ab.2 h.2 y))
          else 0

/-- **`P⁰` in degree one is multiplication by `c`**: `[D_{p−1} t] = c · t` for every degree-one class of
every space.  Lane `lx-toppower` discharges it with `c = ((p − 1)/2)!` (`TopPow.oddDClass_deg_one`). -/
def DegOneConst (hp : Odd p) (c : ZMod p) : Prop :=
  ∀ (X : TopCat.{0}) (t : Hmod (ZMod p) X 1),
    oddDClass p hp 1 (p - 1) (idx_one_le p) t = cohCast (deg_one p).symm (c • t)

/-! ## 3. Vanishing by degree on circles -/

/-- **On a class pulled back from the circle, `[D_a]` vanishes in degree at least two**: it is the
pullback of a class of `H^{≥2}(S¹; F_p) = 0`. -/
theorem oddDClass_pull_circle_eq_zero (hp : Odd p) {X : TopCat.{0}} (f : X ⟶ TopCat.of (Sphere 1))
    (σ : Hmod (ZMod p) (TopCat.of (Sphere 1)) 1) {a : ℕ} (ha : a ≤ p * 1) (h2 : 2 ≤ p * 1 - a) :
    oddDClass p hp 1 a ha (pull f 1 σ) = 0 := by
  rw [← oddDClass_natural p hp f 1 a ha σ,
    sphere_coh_eq_zero_of_neOf (ZMod p) 1 (p * 1 - a) (by omega) (by omega)
      (oddDClass p hp 1 a ha σ),
    pull_zero]

/-! ## 4. The main coefficient -/

/-- **`κ(p − 1, p − 1) = (−1)^{(p−1)/2}`**: the reduced coefficient is `1` because `p − 1` is even, the
sign `(−1)^{(p−1)·1}` is `1`, and the riffle sign is `(−1)^{p · (p−1)/2} = (−1)^{(p−1)/2}`. -/
theorem kappa_main (hp : Odd p) : kappa p (p - 1) (p - 1) = (-1) ^ (p / 2) := by
  obtain ⟨k, hk⟩ := hp
  have e1 : Even (p - 1) := ⟨k, by omega⟩
  have hodd : Odd p := ⟨k, hk⟩
  have e3 : 1 * 1 * (p * (p - 1) / 2) = p * k := by
    rw [Nat.mul_one, Nat.one_mul, show p - 1 = 2 * k by omega, Nat.mul_left_comm,
      Nat.mul_div_cancel_left _ two_pos]
  have e4 : p / 2 = k := by omega
  unfold kappa
  rw [e3, wdPhi_one_one_even p e1, deg_one p, Nat.mul_one, e1.neg_one_pow, mul_one, mul_one,
    pow_mul, hodd.neg_one_pow, e4]

/-! ## 5. The corner formula -/

/-- **The corner formula for classes pulled back from circles.**
`[D_{2(p−1)}(x ⌣ y)] = (−1)^{(p−1)/2} · [D_{p−1} x] · [D_{p−1} y]` in the total ring when `x = f^* σ` and
`y = g^* τ` for maps `f, g` to `S¹`.  The terms `a = p − 2` and `a = p` carry a factor of degree two pulled
back from a circle, and vanish. -/
theorem corner_pull_circle (hp : Odd p) (hC : CornerCartan p hp) {X : TopCat.{0}}
    (f g : X ⟶ TopCat.of (Sphere 1)) (σ τ : Hmod (ZMod p) (TopCat.of (Sphere 1)) 1) :
    TotalHOf.of (ZMod p) X (p * (1 + 1) - 2 * (p - 1))
        (oddDClass p hp (1 + 1) (2 * (p - 1)) (idx_two_le p) (cup (pull f 1 σ) (pull g 1 τ)))
      = (-1 : ZMod p) ^ (p / 2) •
          (TotalHOf.of (ZMod p) X (p * 1 - (p - 1))
              (oddDClass p hp 1 (p - 1) (idx_one_le p) (pull f 1 σ))
            * TotalHOf.of (ZMod p) X (p * 1 - (p - 1))
              (oddDClass p hp 1 (p - 1) (idx_one_le p) (pull g 1 τ))) := by
  rw [hC X, Finset.sum_eq_single_of_mem ((p - 1, p - 1) : ℕ × ℕ)
    (Finset.mem_antidiagonal.mpr (show p - 1 + (p - 1) = 2 * (p - 1) by omega))]
  · have h : p - 1 ≤ p * 1 ∧ p - 1 ≤ p * 1 := by omega
    simp only [dif_pos h, kappa_main p hp]
  · rintro ⟨a, b⟩ hab hne
    rw [Finset.mem_antidiagonal] at hab
    have hab' : a + b = 2 * (p - 1) := hab
    by_cases h : a ≤ p * 1 ∧ b ≤ p * 1
    · simp only [dif_pos h]
      rcases Nat.lt_or_ge a (p - 1) with hlt | hge
      · rw [oddDClass_pull_circle_eq_zero p hp f σ h.1 (by omega), map_zero, zero_mul, smul_zero]
      · have ha : a ≠ p - 1 := fun ha =>
          hne (by rw [ha, show b = p - 1 by omega])
        rw [oddDClass_pull_circle_eq_zero p hp g τ h.2 (by omega), map_zero, mul_zero, smul_zero]
    · simp only [dif_neg h]

/-! ## 6. The torus -/

/-- The degree-one class of the second circle factor of `S¹ × S¹`. -/
def torusS : Hmod (ZMod p) (TopCat.of (Sphere 1 × Sphere 1)) 1 :=
  pull (knPrS (Sphere 1) 1) 1 (sphereTopClassOf (ZMod p) 1 le_rfl)

/-- The degree-one class of the first circle factor of `S¹ × S¹`. -/
def torusY : Hmod (ZMod p) (TopCat.of (Sphere 1 × Sphere 1)) 1 :=
  pull (knPrY (Sphere 1) 1) 1 (sphereTopClassOf (ZMod p) 1 le_rfl)

/-- **The top class of the torus is nonzero**: Künneth injectivity for one sphere factor. -/
theorem cup_torus_ne_zero : cup (torusS p) (torusY p) ≠ 0 := by
  intro h
  exact sphereTopClassOf_ne_zero (ZMod p) 1 le_rfl
    (KnHemi.kunnethSecondInjective_of_ne_zeroOf (ZMod p) (Sphere 1) 1 le_rfl _
      (sphereTopClassOf_ne_zero (ZMod p) 1 le_rfl) 1 _ h)

/-- **The corner on the torus**: `[D_{2(p−1)}(t_S ⌣ t_Y)] = (−1)^{(p−1)/2} c² · t_S ⌣ t_Y` in the total
ring when `P⁰ = c · id` in degree one. -/
theorem torus_corner (hp : Odd p) (hC : CornerCartan p hp) {c : ZMod p} (hc : DegOneConst p hp c) :
    TotalHOf.of (ZMod p) (TopCat.of (Sphere 1 × Sphere 1)) (p * (1 + 1) - 2 * (p - 1))
        (oddDClass p hp (1 + 1) (2 * (p - 1)) (idx_two_le p) (cup (torusS p) (torusY p)))
      = ((-1 : ZMod p) ^ (p / 2) * c ^ 2) •
          TotalHOf.of (ZMod p) (TopCat.of (Sphere 1 × Sphere 1)) (1 + 1)
            (cup (torusS p) (torusY p)) := by
  unfold torusS torusY
  rw [corner_pull_circle p hp hC, hc, hc, totalOf_cohCast, totalOf_cohCast, ← TotalHOf.of_mul,
    cup_smul_left, cup_smul_right, smul_smul, totalOf_smul, smul_smul, sq]

/-- **The constant is unique**: the top class of the torus is nonzero, so a scalar `μ` with
`[D_{2(p−1)}(t_S ⌣ t_Y)] = μ · t_S ⌣ t_Y` equals `(−1)^{(p−1)/2} c²`. -/
theorem torus_const_unique (hp : Odd p) (hC : CornerCartan p hp) {c : ZMod p}
    (hc : DegOneConst p hp c) {μ : ZMod p}
    (hμ : TotalHOf.of (ZMod p) (TopCat.of (Sphere 1 × Sphere 1)) (p * (1 + 1) - 2 * (p - 1))
        (oddDClass p hp (1 + 1) (2 * (p - 1)) (idx_two_le p) (cup (torusS p) (torusY p)))
      = μ • TotalHOf.of (ZMod p) (TopCat.of (Sphere 1 × Sphere 1)) (1 + 1)
          (cup (torusS p) (torusY p))) :
    μ = (-1) ^ (p / 2) * c ^ 2 := by
  have hv : TotalHOf.of (ZMod p) (TopCat.of (Sphere 1 × Sphere 1)) (1 + 1)
      (cup (torusS p) (torusY p)) ≠ 0 := fun h0 =>
    cup_torus_ne_zero p ((TotalHOf.of_eq_zero_iff _ _ _ _).mp h0)
  have h := hμ.symm.trans (torus_corner p hp hC hc)
  by_contra hne
  have hsub : (μ - (-1) ^ (p / 2) * c ^ 2) •
      TotalHOf.of (ZMod p) (TopCat.of (Sphere 1 × Sphere 1)) (1 + 1)
        (cup (torusS p) (torusY p)) = 0 := by
    rw [sub_smul, h, sub_self]
  apply hv
  have h2 := congrArg (fun w => (μ - (-1) ^ (p / 2) * c ^ 2)⁻¹ • w) hsub
  simp only [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul, smul_zero] at h2
  exact h2

/-- **The degree-two constant is a unit** when the degree-one constant is. -/
theorem isUnit_torus_const {c : ZMod p} (hc : IsUnit c) :
    IsUnit ((-1 : ZMod p) ^ (p / 2) * c ^ 2) :=
  (isUnit_neg_one.pow _).mul (hc.pow 2)

end

end OddPCartanTorus
end GroupApproximation.CharClass

open GroupApproximation.CharClass

#audit_axioms OddPCartanTorus.totalOf_smul
#audit_axioms OddPCartanTorus.oddDClass_pull_circle_eq_zero
#audit_axioms OddPCartanTorus.kappa_main
#audit_axioms OddPCartanTorus.corner_pull_circle
#audit_axioms OddPCartanTorus.cup_torus_ne_zero
#audit_axioms OddPCartanTorus.torus_corner
#audit_axioms OddPCartanTorus.torus_const_unique
#audit_axioms OddPCartanTorus.isUnit_torus_const
