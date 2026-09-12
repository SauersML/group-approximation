import GroupApproximation.CharClass.LIXStepDGenReal
import GroupApproximation.CharClass.KroneckerSphere
import GroupApproximation.CharClass.CohomologyKunnethInjectiveOf

/-!
# The bundle-independent inputs of Step D mod `p` at the real mapping torus

Lane `lix-evenside-n` of the STW Problem LIX strengthening programme
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`, §1.4–1.5; lead's ruling of 2026-09-11 assigning the
torus fields of `Gen.RealTorusModP` to this lane).

`CharClass/LIXStepDGenReal.lean` takes the torus data of Step D mod `p` as the structure
`Gen.RealTorusModP`.  This file discharges the fields that are not about the reduced powers,
and the characteristic instance the even side consumes:

* **`circle_two`**, `H²(S¹; K) = 0`, from `lix-cupone`'s `sphere_coh_eq_zero_of_neOf`
  (`CharClass/KroneckerSphere.lean`), at the circle `Sphere 1`;
* **`z_inj`**, Künneth uniqueness for `z = t x` in the ring `TotalHOf K Y`, from the degreewise
  statement (`Gen.z_inj_of_degreewise`).  This is the coefficient-generic form of
  `Gen.tx_inj_of_degreewise` (`CharClass/LIXStepDGenParity.lean`): the ring equation splits
  into one equation per degree, and peeling the two generators one at a time reads, in degree
  `1 + ((2n+1) + c)`, exactly the degreewise hypothesis at `c`.  The degreewise statement on the
  Künneth model `(Y × S^{2n+1}) × S¹` is `lix-coeff`'s, over `kunneth_decomposition_uniqueOf`;
* **`ExpChar (Gen.evenPart (ZMod p) Y) p`** for a prime `p` and a nonempty `Y`
  (`Gen.expChar_evenPart`): the natural numbers act on `H⁰` through `ZMod p`, and the unit class
  of a nonempty space does not vanish because it pulls back to the unit class of a point
  (`KnHemi.one_ne_zero_unitOf`).

What remains of `Gen.RealTorusModP` after this file is the reduced powers (`lix-steenrod`).

## Main results

* `Gen.componentOf_map`, `Gen.componentOf_of_mul` — components of pullbacks and of products with
  a homogeneous class, over `K`.
* `Gen.z_inj_of_degreewise` — the field `z_inj`.
* `Gen.circle_two_sphereOf` — the field `circle_two` at `S₁ = Sphere 1`.
* `Gen.one_ne_zero_of_nonempty`, `Gen.charP_evenPart`, `Gen.expChar_evenPart` — the instance.
-/

set_option autoImplicit false

noncomputable section

namespace GroupApproximation
namespace CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace Gen

/-! ## 1. Components over `K` -/

section Components

variable (K : Type) [CommRing K]

/-- **The component of a pullback is the pullback of the component.** -/
theorem componentOf_map {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (u : TotalHOf K Y) :
    TotalHOf.component K X n (TotalHOf.map K f u) = pull f n (TotalHOf.component K Y n u) := by
  induction u using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, pull_zero]
  | of j c =>
    show TotalHOf.component K X n (TotalHOf.map K f (TotalHOf.of K Y j c))
      = pull f n (TotalHOf.component K Y n (TotalHOf.of K Y j c))
    rw [TotalHOf.map_of]
    rcases eq_or_ne j n with rfl | hjn
    · rw [TotalHOf.component_of, TotalHOf.component_of]
    · rw [TotalHOf.component_of_ne K X hjn.symm, TotalHOf.component_of_ne K Y hjn.symm,
        pull_zero]
  | add u₁ u₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂, pull_add]

/-- **The component of `of i w * z` at `i + m` is `w ⌣ (component m z)`.** -/
theorem componentOf_of_mul {X : TopCat.{0}} (i m : ℕ) (w : TotalPieceOf K X i)
    (z : TotalHOf K X) :
    TotalHOf.component K X (i + m) (TotalHOf.of K X i w * z)
      = cup w (TotalHOf.component K X m z) := by
  induction z using DirectSum.induction_on with
  | zero => rw [mul_zero, map_zero, map_zero, cup_zero]
  | of j c =>
    show TotalHOf.component K X (i + m) (TotalHOf.of K X i w * TotalHOf.of K X j c)
      = cup w (TotalHOf.component K X m (TotalHOf.of K X j c))
    rw [← TotalHOf.of_mul]
    rcases eq_or_ne j m with rfl | hjm
    · rw [TotalHOf.component_of, TotalHOf.component_of]
    · rw [TotalHOf.component_of_ne K X (show i + m ≠ i + j by omega),
        TotalHOf.component_of_ne K X hjm.symm, cup_zero]
  | add z₁ z₂ h₁ h₂ => rw [mul_add, map_add, map_add, h₁, h₂, cup_add_right]

end Components

/-! ## 2. The field `z_inj`, from the degreewise statement -/

/-- **Künneth uniqueness for `z = t x` in the ring, from the degreewise statement.**  The field
`z_inj` of `Gen.RealTorusModP`.  The degreewise hypothesis is read in degree `1 + ((2n+1) + c)`,
peeling `t` and then `x`, which keeps every degree cast-free. -/
theorem z_inj_of_degreewise (K : Type) [CommRing K] {N Y S₁ Sodd : TopCat.{0}} (n : ℕ)
    (pY : N ⟶ Y) (q₁ : N ⟶ S₁) (qodd : N ⟶ Sodd)
    (σ₁ : TotalPieceOf K S₁ 1) (σodd : TotalPieceOf K Sodd (2 * n + 1))
    (h : ∀ (c : ℕ) (α : TotalPieceOf K Y (1 + ((2 * n + 1) + c))) (β : TotalPieceOf K Y c),
      pull pY (1 + ((2 * n + 1) + c)) α
          + cup (pull q₁ 1 σ₁) (cup (pull qodd (2 * n + 1) σodd) (pull pY c β)) = 0 →
        β = 0) :
    ∀ u v : TotalHOf K Y,
      TotalHOf.map K pY u + zClass K q₁ qodd σ₁ σodd * TotalHOf.map K pY v = 0 → v = 0 := by
  intro u v huv
  rw [zClass, mul_assoc, tClassOf, xClassOf, TotalHOf.map_of, TotalHOf.map_of] at huv
  refine DirectSum.ext fun c => ?_
  show TotalHOf.component K Y c v = TotalHOf.component K Y c 0
  rw [map_zero]
  refine h c (TotalHOf.component K Y (1 + ((2 * n + 1) + c)) u) (TotalHOf.component K Y c v) ?_
  have hc := congrArg (TotalHOf.component K N (1 + ((2 * n + 1) + c))) huv
  rw [map_add, map_zero, componentOf_map, componentOf_of_mul, componentOf_of_mul,
    componentOf_map] at hc
  exact hc

/-! ## 3. The field `circle_two` -/

/-- **`H²(S¹; K) = 0`**, the field `circle_two` of `Gen.RealTorusModP` at `S₁ = Sphere 1`. -/
theorem circle_two_sphereOf (K : Type) [Field K] :
    ∀ a : TotalPieceOf K (TopCat.of (Sphere 1)) (1 + 1), a = 0 :=
  fun a => sphere_coh_eq_zero_of_neOf K 1 (1 + 1) (by omega) (by omega) a

/-! ## 4. The characteristic of the even part over `ZMod p` -/

/-- **The unit class of a nonempty space does not vanish**, over a field: it pulls back to the
unit class of a point. -/
theorem one_ne_zero_of_nonempty (K : Type) [Field K] (X : TopCat.{0}) [Nonempty X] :
    (one X : Hmod K X 0) ≠ 0 := by
  intro h
  obtain ⟨x⟩ := ‹Nonempty X›
  have h1 := pull_one (K := K) (TopCat.ofHom (ContinuousMap.const Unit x) : TopCat.of Unit ⟶ X)
  rw [h, pull_zero] at h1
  exact KnHemi.one_ne_zero_unitOf K h1.symm

/-- **The even part of `H^*(Y; F_p)` has characteristic `p`**, for a nonempty `Y`. -/
theorem charP_evenPart (p : ℕ) [Fact p.Prime] (Y : TopCat.{0}) [Nonempty Y] :
    CharP (evenPart (ZMod p) Y) p where
  cast_eq_zero_iff x := by
    rw [← ZMod.natCast_eq_zero_iff x p, Subtype.ext_iff]
    show TotalHOf.of (ZMod p) Y 0 ((x : ZMod p) • (one Y : Hmod (ZMod p) Y 0)) = 0
      ↔ (x : ZMod p) = 0
    rw [TotalHOf.of_eq_zero_iff]
    constructor
    · intro hx
      exact (eq_zero_or_eq_zero_of_smul_eq_zero hx).resolve_right
        (one_ne_zero_of_nonempty (ZMod p) Y)
    · intro hx
      rw [hx, zero_smul]

/-- **The instance the even side consumes**: `ExpChar (Gen.evenPart (ZMod p) Y) p`. -/
theorem expChar_evenPart (p : ℕ) [hp : Fact p.Prime] (Y : TopCat.{0}) [Nonempty Y] :
    ExpChar (evenPart (ZMod p) Y) p :=
  haveI := charP_evenPart p Y
  ExpChar.prime hp.out

end Gen

#audit_axioms Gen.componentOf_map
#audit_axioms Gen.componentOf_of_mul
#audit_axioms Gen.z_inj_of_degreewise
#audit_axioms Gen.circle_two_sphereOf
#audit_axioms Gen.one_ne_zero_of_nonempty
#audit_axioms Gen.charP_evenPart
#audit_axioms Gen.expChar_evenPart

end CharClass
end GroupApproximation

end
