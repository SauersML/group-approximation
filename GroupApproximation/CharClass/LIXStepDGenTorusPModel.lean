import GroupApproximation.CharClass.OddPTotalInterface
import GroupApproximation.CharClass.LIXStepDGenRealTorusModel
import GroupApproximation.CharClass.CohomologyKunnethDecompOf
import GroupApproximation.Meta.AxiomGuard

/-!
# The torus data of Step D mod `p` at any space isomorphic to the Künneth model

Lane `lx-torusP` of the LIX strongest swarm (`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`, §1.4–1.5).

`Gen.RealTorusModP` (`CharClass/LIXStepDGenReal.lean`) asks for the reduced powers on the even
parts of `H^*(N; F_p)` and `H^*(Y; F_p)` and for three statements about the torus.  The reduced
powers are `lx-pzero`'s named input `OddPTotal.EvenReducedPowers p`
(`CharClass/OddPTotalInterface.lean`), and `Gen.RealTorusModP.ofEven` reads the operation fields off
it.  This file proves the three torus statements for every space `N` with an isomorphism
`e : N ≅ (Y × S^{2n+1}) × S¹` onto `lix-coeff`'s Künneth model `KnTwo.torusBaseOf Y n`, with the
projections `e ≫ KnTwo.prYOf`, `e ≫ KnTwo.prS1Of`, `e ≫ KnTwo.prSoddOf` and any nonzero sphere
classes:

* `H²(S¹; K) = 0` is `Gen.circle_two_sphereOf`;
* **Künneth uniqueness for `z = t x`** moves across `e` (`Gen.z_inj_ofIso`): pullback along an
  isomorphism is injective, and `z` on `N` is the pullback of `z` on the model;
* **`P^{>0} z = 0` is a naturality statement.**  `z = t x` is pulled back along the projection
  `N → S^{2n+1} × S¹`, and the cohomology of `S^{2n+1} × S¹` vanishes above degree `2n + 2`
  (`Gen.sphereProd_coh_eq_zero`, from the Künneth decomposition with one sphere factor), so
  `P^i z` lands in a zero group for `i > 0`.  No Cartan formula on odd classes is used.

Nothing here depends on `Y`, so every stage of the tower is covered, stage `0` included (where `Y`
is a point).

## Main results

* `Gen.prSphOf` — the projection of the model onto the two sphere factors.
* `Gen.sphereProd_coh_eq_zero` — `H^m(S^{2n+1} × S¹; K) = 0` for `m > 2n + 2`.
* `Gen.zClass_comp_sphereProd` — `z` is pulled back from `S^{2n+1} × S¹`.
* `Gen.P_z_of_sphereFactor` — `P^{>0} z = 0`.
* `Gen.totalHOf_map_comp_apply`, `Gen.totalHOf_map_id_apply` — functoriality of the ring
  pullback.
* `Gen.z_inj_ofIso` — Künneth uniqueness on `N`.
* `Gen.RealTorusModP.ofEven` — the torus data from the reduced powers and the three statements.
* `Gen.realTorusModP_ofIso` — **the torus data at `N`**.
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

/-- **The cohomology of `S^{2n+1} × S¹` vanishes above degree `2n + 2`**, over a field: in the
Künneth decomposition with the circle factor both coefficients live on `S^{2n+1}` in degrees
`m` and `m − 1`, which are neither `0` nor `2n + 1`. -/
theorem sphereProd_coh_eq_zero (K : Type) [Field K] (n m : ℕ) (hm : 2 * n + 2 < m)
    (c : TotalPieceOf K (TopCat.of (Sphere (2 * n + 1) × Sphere 1)) m) : c = 0 := by
  obtain ⟨a, b, hab⟩ :=
    KnHemi.kunneth_decompositionOf K (Sphere (2 * n + 1)) 1 le_rfl m (m - 1) (by omega) c
  rw [hab, sphere_coh_eq_zero_of_neOf K (2 * n + 1) m (by omega) (by omega) a,
    sphere_coh_eq_zero_of_neOf K (2 * n + 1) (m - 1) (by omega) (by omega) b,
    pull_zero, pull_zero, cup_zero, CharClass.cohCast_zero, add_zero]

/-- **`z = t x` is pulled back from `S^{2n+1} × S¹`**, as the homogeneous class
`pr_{S¹}^* σ₁ ⌣ pr_{S^{2n+1}}^* σodd` of degree `2n + 2`. -/
theorem zClass_comp_sphereProd (K : Type) [CommRing K] (n : ℕ) {N : TopCat.{0}}
    (g : N ⟶ TopCat.of (Sphere (2 * n + 1) × Sphere 1))
    (σ₁ : TotalPieceOf K (TopCat.of (Sphere 1)) 1)
    (σodd : TotalPieceOf K (TopCat.of (Sphere (2 * n + 1))) (2 * n + 1)) :
    zClass K (g ≫ knPrS (Sphere (2 * n + 1)) 1) (g ≫ knPrY (Sphere (2 * n + 1)) 1) σ₁ σodd
      = TotalHOf.map K g (TotalHOf.of K _ (1 + (2 * n + 1))
          (cup (pull (knPrS (Sphere (2 * n + 1)) 1) 1 σ₁)
            (pull (knPrY (Sphere (2 * n + 1)) 1) (2 * n + 1) σodd))) := by
  rw [zClass, tClassOf, xClassOf, TotalHOf.map_of, TotalHOf.map_of, TotalHOf.map_of, pull_cup,
    pull_comp, pull_comp, TotalHOf.of_mul]

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
  have hd : Even (1 + (2 * n + 1)) := ⟨n + 1, by omega⟩
  have hz : evenZClass (ZMod p) (g ≫ knPrS (Sphere (2 * n + 1)) 1)
      (g ≫ knPrY (Sphere (2 * n + 1)) 1) σ₁ σodd
      = evenMap (ZMod p) g (OddPTotal.evenOf (ZMod p) _ hd
          (cup (pull (knPrS (Sphere (2 * n + 1)) 1) 1 σ₁)
            (pull (knPrY (Sphere (2 * n + 1)) 1) (2 * n + 1) σodd))) :=
    Subtype.ext (zClass_comp_sphereProd (ZMod p) n g σ₁ σodd)
  obtain ⟨c', hc'⟩ := ops.shift _ i hd
    (cup (pull (knPrS (Sphere (2 * n + 1)) 1) 1 σ₁)
      (pull (knPrY (Sphere (2 * n + 1)) 1) (2 * n + 1) σodd))
  have h1 : 0 < 2 * i * (p - 1) :=
    Nat.mul_pos (Nat.mul_pos (by norm_num) hi) (by have := (Fact.out : p.Prime).two_le; omega)
  have hc0 : c' = 0 := sphereProd_coh_eq_zero (ZMod p) n _ (by omega) c'
  have hP0 : ops.P _ i (OddPTotal.evenOf (ZMod p) _ hd
      (cup (pull (knPrS (Sphere (2 * n + 1)) 1) 1 σ₁)
        (pull (knPrY (Sphere (2 * n + 1)) 1) (2 * n + 1) σodd))) = 0 :=
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

/-! ## 3. The torus data at a space isomorphic to the model -/

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

/-- **The torus data from the reduced powers.**  `P⁰ = id`, Cartan, naturality and instability
come from `ops`; `H²(S¹) = 0`, Künneth uniqueness for `z` and `P^{>0} z = 0` are the three
statements about the torus itself. -/
def RealTorusModP.ofEven {p n : ℕ} (ops : OddPTotal.EvenReducedPowers p)
    {N Y S₁ Sodd : TopCat.{0}} (pY : N ⟶ Y) (q₁ : N ⟶ S₁) (qodd : N ⟶ Sodd)
    (σ₁ : TotalPieceOf (ZMod p) S₁ 1) (σodd : TotalPieceOf (ZMod p) Sodd (2 * n + 1))
    (circle_two : ∀ a : TotalPieceOf (ZMod p) S₁ (1 + 1), a = 0)
    (z_inj : ∀ u v : TotalHOf (ZMod p) Y,
      TotalHOf.map (ZMod p) pY u + zClass (ZMod p) q₁ qodd σ₁ σodd * TotalHOf.map (ZMod p) pY v
        = 0 → v = 0)
    (P_z : ∀ i : ℕ, 0 < i → ops.P N i (evenZClass (ZMod p) q₁ qodd σ₁ σodd) = 0) :
    RealTorusModP n (ZMod p) pY q₁ qodd σ₁ σodd where
  circle_two := circle_two
  z_inj := z_inj
  PN := ops.P N
  PY := ops.P Y
  PN_zero := ops.zero N
  cartan := ops.cartan N
  natural := ops.natural pY
  P_z := P_z
  PY_unstable i _ hd c h := ops.unstable Y i hd c h

/-- **The torus data of Step D mod `p` at a space isomorphic to the model**, from the reduced
powers and any nonzero sphere classes.  This is `Gen.RealTorusModP` at the projections
`e ≫ KnTwo.prYOf Y n`, `e ≫ KnTwo.prS1Of Y n`, `e ≫ KnTwo.prSoddOf Y n`, which is how `lx-kunneth`
spells the projections of the real mapping torus (`KnLix.prY n dd := (KnLix.lixIso n dd).hom ≫
KnTwo.prYOf (baseY dd) n`, and likewise for the two sphere factors). -/
def realTorusModP_ofIso {p : ℕ} [Fact p.Prime] (ops : OddPTotal.EvenReducedPowers p)
    (Y : Type) [TopologicalSpace Y] (n : ℕ) {N : TopCat.{0}}
    (e : N ≅ TopCat.of (KnTwo.torusBaseOf Y n))
    (σ₁ : TotalPieceOf (ZMod p) (TopCat.of (Sphere 1)) 1) (hσ₁ : σ₁ ≠ 0)
    (σodd : TotalPieceOf (ZMod p) (TopCat.of (Sphere (2 * n + 1))) (2 * n + 1))
    (hσodd : σodd ≠ 0) :
    RealTorusModP n (ZMod p) (e.hom ≫ KnTwo.prYOf Y n) (e.hom ≫ KnTwo.prS1Of Y n)
      (e.hom ≫ KnTwo.prSoddOf Y n) σ₁ σodd :=
  RealTorusModP.ofEven ops _ _ _ σ₁ σodd (circle_two_sphereOf (ZMod p))
    (z_inj_ofIso (ZMod p) Y n e σ₁ hσ₁ σodd hσodd)
    (P_z_of_sphereFactor ops n _ _ (e.hom ≫ prSphOf Y n)
      (by rw [Category.assoc]; exact rfl) (by rw [Category.assoc]; exact rfl) σ₁ σodd)

end Gen

#audit_axioms Gen.prSphOf
#audit_axioms Gen.sphereProd_coh_eq_zero
#audit_axioms Gen.zClass_comp_sphereProd
#audit_axioms Gen.P_z_of_sphereFactor
#audit_axioms Gen.totalHOf_map_comp_apply
#audit_axioms Gen.totalHOf_map_id_apply
#audit_axioms Gen.z_inj_ofIso
#audit_axioms Gen.RealTorusModP.ofEven
#audit_axioms Gen.realTorusModP_ofIso

end CharClass
end GroupApproximation

end
