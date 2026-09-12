import GroupApproximation.CharClass.OddPTotalInterface
import GroupApproximation.CharClass.LIXStepDGenRealTorusModel
import GroupApproximation.CharClass.CohomologyKunnethDecompOf
import GroupApproximation.Meta.AxiomGuard

/-!
# The product of the two sphere factors of the mapping torus, and the class `z`

Lane `lx-torusP` of the LIX strongest swarm (`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`, §1.4–1.5).

The torus data `Gen.RealTorusModP` (`CharClass/LIXStepDGenReal.lean`) needs three statements about
the mapping torus `N` itself, besides the reduced powers.  This file proves the geometric inputs for
every space `N` with an isomorphism `e : N ≅ (Y × S^{2n+1}) × S¹` onto `lix-coeff`'s Künneth model
`KnTwo.torusBaseOf Y n`, with the projections `e ≫ KnTwo.prYOf`, `e ≫ KnTwo.prS1Of`,
`e ≫ KnTwo.prSoddOf` and any nonzero sphere classes:

* the cohomology of `S^{2n+1} × S¹` vanishes outside the degrees `0, 1, 2n + 1, 2n + 2`
  (`Gen.sphereProd_coh_eq_zero_of_ne`, from the Künneth decomposition with one sphere factor);
* `z = t x` is pulled back from `S^{2n+1} × S¹` as the homogeneous class `Gen.zSphereProd`
  (`Gen.zClass_comp_sphereProd`), so the positive reduced powers kill it
  (`Gen.P_z_of_sphereFactor`);
* **Künneth uniqueness for `z`** moves across `e` (`Gen.z_inj_ofIso`).

The total power of `z` and the torus data themselves are in `CharClass/LIXStepDGenTorusPPtot.lean`.
Nothing here depends on `Y`, so every stage of the tower is covered, stage `0` included.

## Main results

* `Gen.prSphOf`, `Gen.zSphereProd`.
* `Gen.sphereProd_coh_eq_zero_of_ne`, `Gen.sphereProd_coh_eq_zero`.
* `Gen.zClass_comp_sphereProd`, `Gen.P_z_of_sphereFactor`.
* `Gen.totalHOf_map_comp_apply`, `Gen.totalHOf_map_id_apply`.
* `Gen.z_inj_ofIso`.
-/

set_option autoImplicit false

noncomputable section

namespace GroupApproximation
namespace CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace Gen

/-! ## 1. The product of the two sphere factors -/

/-- The projection of the model `(Y × S^{2n+1}) × S¹` onto `S^{2n+1} × S¹`. -/
def prSphOf (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    TopCat.of (KnTwo.torusBaseOf Y n) ⟶ TopCat.of (Sphere (2 * n + 1) × Sphere 1) :=
  cmap (ContinuousMap.prodMk
    ((ContinuousMap.snd : C(Y × Sphere (2 * n + 1), Sphere (2 * n + 1))).comp
      (ContinuousMap.fst : C(KnTwo.torusBaseOf Y n, Y × Sphere (2 * n + 1))))
    (ContinuousMap.snd : C(KnTwo.torusBaseOf Y n, Sphere 1)))

/-- The class `z = t x` on `S^{2n+1} × S¹`, in degree `2n + 2`. -/
def zSphereProd (K : Type) [CommRing K] (n : ℕ) (σ₁ : TotalPieceOf K (TopCat.of (Sphere 1)) 1)
    (σodd : TotalPieceOf K (TopCat.of (Sphere (2 * n + 1))) (2 * n + 1)) :
    TotalPieceOf K (TopCat.of (Sphere (2 * n + 1) × Sphere 1)) (1 + (2 * n + 1)) :=
  cup (pull (knPrS (Sphere (2 * n + 1)) 1) 1 σ₁) (pull (knPrY (Sphere (2 * n + 1)) 1) (2 * n + 1) σodd)

/-- The degree of `z` is even. -/
theorem even_zDeg (n : ℕ) : Even (1 + (2 * n + 1)) := ⟨n + 1, by omega⟩

/-- **The cohomology of `S^{2n+1} × S¹` vanishes outside the degrees `0, 1, 2n + 1, 2n + 2`**, over
a field: in the Künneth decomposition with the circle factor both coefficients live on `S^{2n+1}`,
in degrees `m` and `m − 1`, and neither is `0` or `2n + 1`. -/
theorem sphereProd_coh_eq_zero_of_ne (K : Type) [Field K] (n m : ℕ) (hm0 : m ≠ 0) (hm1 : m ≠ 1)
    (hmo : m ≠ 2 * n + 1) (hmd : m ≠ 2 * n + 2)
    (c : TotalPieceOf K (TopCat.of (Sphere (2 * n + 1) × Sphere 1)) m) : c = 0 := by
  obtain ⟨a, b, hab⟩ :=
    KnHemi.kunneth_decompositionOf K (Sphere (2 * n + 1)) 1 le_rfl m (m - 1) (by omega) c
  rw [hab, sphere_coh_eq_zero_of_neOf K (2 * n + 1) m hm0 hmo a,
    sphere_coh_eq_zero_of_neOf K (2 * n + 1) (m - 1) (by omega) (by omega) b,
    pull_zero, pull_zero, cup_zero, CharClass.cohCast_zero, add_zero]

/-- **The cohomology of `S^{2n+1} × S¹` vanishes above degree `2n + 2`**, over a field. -/
theorem sphereProd_coh_eq_zero (K : Type) [Field K] (n m : ℕ) (hm : 2 * n + 2 < m)
    (c : TotalPieceOf K (TopCat.of (Sphere (2 * n + 1) × Sphere 1)) m) : c = 0 :=
  sphereProd_coh_eq_zero_of_ne K n m (by omega) (by omega) (by omega) (by omega) c

/-- **`z = t x` is pulled back from `S^{2n+1} × S¹`**, as the homogeneous class `zSphereProd`. -/
theorem zClass_comp_sphereProd (K : Type) [CommRing K] (n : ℕ) {N : TopCat.{0}}
    (g : N ⟶ TopCat.of (Sphere (2 * n + 1) × Sphere 1))
    (σ₁ : TotalPieceOf K (TopCat.of (Sphere 1)) 1)
    (σodd : TotalPieceOf K (TopCat.of (Sphere (2 * n + 1))) (2 * n + 1)) :
    zClass K (g ≫ knPrS (Sphere (2 * n + 1)) 1) (g ≫ knPrY (Sphere (2 * n + 1)) 1) σ₁ σodd
      = TotalHOf.map K g (TotalHOf.of K _ (1 + (2 * n + 1)) (zSphereProd K n σ₁ σodd)) := by
  rw [zSphereProd, zClass, tClassOf, xClassOf, TotalHOf.map_of, TotalHOf.map_of, TotalHOf.map_of,
    pull_cup, pull_comp, pull_comp, TotalHOf.of_mul]

/-- **`P^{>0} z = 0`**, whenever the circle and odd-sphere projections factor through a map to
`S^{2n+1} × S¹`: naturality moves `P^i` to `S^{2n+1} × S¹`, where it lands in degree
`2n + 2 + 2i(p − 1) > 2n + 2`. -/
theorem P_z_of_sphereFactor {p : ℕ} [Fact p.Prime] (ops : OddPTotal.EvenReducedPowers p) (n : ℕ)
    {N : TopCat.{0}} (q₁ : N ⟶ TopCat.of (Sphere 1))
    (qodd : N ⟶ TopCat.of (Sphere (2 * n + 1)))
    (g : N ⟶ TopCat.of (Sphere (2 * n + 1) × Sphere 1))
    (hq₁ : q₁ = g ≫ knPrS (Sphere (2 * n + 1)) 1) (hqodd : qodd = g ≫ knPrY (Sphere (2 * n + 1)) 1)
    (σ₁ : TotalPieceOf (ZMod p) (TopCat.of (Sphere 1)) 1)
    (σodd : TotalPieceOf (ZMod p) (TopCat.of (Sphere (2 * n + 1))) (2 * n + 1)) :
    ∀ i : ℕ, 0 < i → ops.P N i (evenZClass (ZMod p) q₁ qodd σ₁ σodd) = 0 := by
  intro i hi
  subst hq₁ hqodd
  have hz : evenZClass (ZMod p) (g ≫ knPrS (Sphere (2 * n + 1)) 1)
      (g ≫ knPrY (Sphere (2 * n + 1)) 1) σ₁ σodd
      = evenMap (ZMod p) g (OddPTotal.evenOf (ZMod p) _ (even_zDeg n)
          (zSphereProd (ZMod p) n σ₁ σodd)) :=
    Subtype.ext (zClass_comp_sphereProd (ZMod p) n g σ₁ σodd)
  obtain ⟨c', hc'⟩ := ops.shift _ i (even_zDeg n) (zSphereProd (ZMod p) n σ₁ σodd)
  have h1 : 0 < 2 * i * (p - 1) :=
    Nat.mul_pos (Nat.mul_pos (by norm_num) hi) (by have := (Fact.out : p.Prime).two_le; omega)
  have hc0 : c' = 0 := sphereProd_coh_eq_zero (ZMod p) n _ (by omega) c'
  have hP0 : ops.P _ i (OddPTotal.evenOf (ZMod p) _ (even_zDeg n)
      (zSphereProd (ZMod p) n σ₁ σodd)) = 0 :=
    Subtype.ext (hc'.trans ((congrArg (TotalHOf.of (ZMod p) _ _) hc0).trans (map_zero _)))
  rw [hz, ops.natural, hP0, map_zero]

/-! ## 2. Functoriality of the ring pullback -/

/-- The ring pullback along a composite is the composite of the pullbacks. -/
theorem totalHOf_map_comp_apply (K : Type) [CommRing K] {X Y Z : TopCat.{0}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (u : TotalHOf K Z) :
    TotalHOf.map K (f ≫ g) u = TotalHOf.map K f (TotalHOf.map K g u) := by
  induction u using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | of j c =>
    show TotalHOf.map K (f ≫ g) (TotalHOf.of K Z j c)
      = TotalHOf.map K f (TotalHOf.map K g (TotalHOf.of K Z j c))
    rw [TotalHOf.map_of, TotalHOf.map_of, TotalHOf.map_of, pull_comp]
  | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]

/-- The ring pullback along the identity is the identity. -/
theorem totalHOf_map_id_apply (K : Type) [CommRing K] {X : TopCat.{0}} (u : TotalHOf K X) :
    TotalHOf.map K (𝟙 X) u = u := by
  induction u using DirectSum.induction_on with
  | zero => rw [map_zero]
  | of j c =>
    show TotalHOf.map K (𝟙 X) (TotalHOf.of K X j c) = TotalHOf.of K X j c
    rw [TotalHOf.map_of, pull_id]
  | add u v hu hv => rw [map_add, hu, hv]

/-! ## 3. Künneth uniqueness at a space isomorphic to the model -/

/-- **Künneth uniqueness for `z = t x` at a space isomorphic to the model**, over a field, for any
nonzero sphere classes.  The equation on `N` is the pullback along `e` of the equation on the
model, and pullback along an isomorphism is injective. -/
theorem z_inj_ofIso (K : Type) [Field K] (Y : Type) [TopologicalSpace Y] (n : ℕ) {N : TopCat.{0}}
    (e : N ≅ TopCat.of (KnTwo.torusBaseOf Y n))
    (σ₁ : TotalPieceOf K (TopCat.of (Sphere 1)) 1) (hσ₁ : σ₁ ≠ 0)
    (σodd : TotalPieceOf K (TopCat.of (Sphere (2 * n + 1))) (2 * n + 1)) (hσodd : σodd ≠ 0) :
    ∀ u v : TotalHOf K (TopCat.of Y),
      TotalHOf.map K (e.hom ≫ KnTwo.prYOf Y n) u
          + zClass K (e.hom ≫ KnTwo.prS1Of Y n) (e.hom ≫ KnTwo.prSoddOf Y n) σ₁ σodd
            * TotalHOf.map K (e.hom ≫ KnTwo.prYOf Y n) v = 0 → v = 0 := by
  intro u v h
  refine z_inj_torusOf K Y n σ₁ hσ₁ σodd hσodd u v ?_
  have hz : zClass K (e.hom ≫ KnTwo.prS1Of Y n) (e.hom ≫ KnTwo.prSoddOf Y n) σ₁ σodd
      = TotalHOf.map K e.hom (zClass K (KnTwo.prS1Of Y n) (KnTwo.prSoddOf Y n) σ₁ σodd) := by
    rw [zClass, zClass, tClassOf, tClassOf, xClassOf, xClassOf, map_mul,
      totalHOf_map_comp_apply, totalHOf_map_comp_apply]
  have h' : TotalHOf.map K e.hom (TotalHOf.map K (KnTwo.prYOf Y n) u
      + zClass K (KnTwo.prS1Of Y n) (KnTwo.prSoddOf Y n) σ₁ σodd
        * TotalHOf.map K (KnTwo.prYOf Y n) v) = 0 := by
    rw [map_add, map_mul, ← hz, ← totalHOf_map_comp_apply, ← totalHOf_map_comp_apply]
    exact h
  have h2 := congrArg (TotalHOf.map K e.inv) h'
  rwa [← totalHOf_map_comp_apply, e.inv_hom_id, totalHOf_map_id_apply, map_zero] at h2

end Gen

#audit_axioms Gen.prSphOf
#audit_axioms Gen.zSphereProd
#audit_axioms Gen.even_zDeg
#audit_axioms Gen.sphereProd_coh_eq_zero_of_ne
#audit_axioms Gen.sphereProd_coh_eq_zero
#audit_axioms Gen.zClass_comp_sphereProd
#audit_axioms Gen.P_z_of_sphereFactor
#audit_axioms Gen.totalHOf_map_comp_apply
#audit_axioms Gen.totalHOf_map_id_apply
#audit_axioms Gen.z_inj_ofIso

end CharClass
end GroupApproximation

end
