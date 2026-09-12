import GroupApproximation.CharClass.LIXStepDGenTorusPModel
import GroupApproximation.CharClass.CohomologySphere
import GroupApproximation.Meta.AxiomGuard

/-!
# The total power of `z = t x`, and the torus data of Step D mod `p`

Lane `lx-torusP` of the LIX strongest swarm (`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`, §1.4–1.5).

`Gen.RealTorusModP` asks for the one product fact the even side uses about `z`:
`P^i r = 0 → P^i (z · pY^* r) = 0`.  `lx-pzero`'s `OddPTotal.EvenReducedPowers.mul_single` gives it
as soon as the total power of `z` is a multiple of `z`.  This file proves that at every space
isomorphic to the Künneth model, and assembles the torus data.

**The total power of `z` is a multiple of `z`** (`Gen.ptot_sphereProd`).  On `S^{2n+1} × S¹` the
even cohomology lives in degrees `0` and `2n + 2` only (`Gen.sphereProd_coh_eq_zero_of_ne`):

* the degree-`0` component of `Ptot z₀` vanishes: restricted to a point `z₀` is `0` (it contains a
  circle class), so by naturality the restriction of the component is `0`, and restriction to a
  point is injective on `H⁰`, which is the line spanned by the unit class;
* the degree-`(2n+2)` component lies on the line spanned by `z₀` (`Gen.sphereProd_top_eq_smul`).

Naturality along the projection `N → S^{2n+1} × S¹` carries this to `N`.

## Main results

* `Gen.totalHOf_of_smul`.
* `Gen.sphereProd_top_eq_smul` — `H^{2n+2}(S^{2n+1} × S¹; K)` is spanned by `z₀`.
* `Gen.ptot_sphereProd_component_zero`, `Gen.ptot_sphereProd` — `Ptot z₀ = ν • z₀`.
* `Gen.z_mul_zero_of_sphereFactor` — `P^i r = 0 → P^i (z · pY^* r) = 0`.
* `Gen.RealTorusModP.ofEven` — the torus data from the reduced powers.
* `Gen.realTorusModP_ofIso` — **the torus data at a space isomorphic to the model**.
-/

set_option autoImplicit false

noncomputable section

namespace GroupApproximation
namespace CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace Gen

/-- `TotalHOf.of` is `K`-linear. -/
theorem totalHOf_of_smul (K : Type) [CommRing K] (X : TopCat.{0}) (d : ℕ) (s : K)
    (c : TotalPieceOf K X d) : TotalHOf.of K X d (s • c) = s • TotalHOf.of K X d c :=
  DirectSum.of_smul d s c

/-! ## 1. The top degree of `S^{2n+1} × S¹` -/

/-- **`H^{2n+2}(S^{2n+1} × S¹; K)` is spanned by `z₀ = t x`**, for nonzero sphere classes.  In the
Künneth decomposition the coefficient on `S^{2n+1}` in degree `2n + 2` vanishes and the other is a
multiple of the fundamental class, as are `σ₁` and `σodd`, with nonzero coefficients. -/
theorem sphereProd_top_eq_smul (K : Type) [Field K] (n : ℕ)
    (σ₁ : TotalPieceOf K (TopCat.of (Sphere 1)) 1) (hσ₁ : σ₁ ≠ 0)
    (σodd : TotalPieceOf K (TopCat.of (Sphere (2 * n + 1))) (2 * n + 1)) (hσodd : σodd ≠ 0)
    (y : TotalPieceOf K (TopCat.of (Sphere (2 * n + 1) × Sphere 1)) (1 + (2 * n + 1))) :
    ∃ ν : K, y = ν • zSphereProd K n σ₁ σodd := by
  obtain ⟨a, b, hab⟩ := KnHemi.kunneth_decompositionOf K (Sphere (2 * n + 1)) 1 le_rfl
    (1 + (2 * n + 1)) (2 * n + 1) rfl y
  have ha : a = 0 := sphere_coh_eq_zero_of_neOf K (2 * n + 1) _ (by omega) (by omega) a
  obtain ⟨s, hb⟩ : ∃ s : K, b = s • sphereTopClassOf K (2 * n + 1) (by omega) :=
    ⟨_, sphere_coh_top_eq_smulOf K (2 * n + 1) (by omega) b⟩
  obtain ⟨s₁, h1⟩ : ∃ s : K, σ₁ = s • sphereTopClassOf K 1 le_rfl :=
    ⟨_, sphere_coh_top_eq_smulOf K 1 le_rfl σ₁⟩
  obtain ⟨s₂, h2⟩ : ∃ s : K, σodd = s • sphereTopClassOf K (2 * n + 1) (by omega) :=
    ⟨_, sphere_coh_top_eq_smulOf K (2 * n + 1) (by omega) σodd⟩
  have hs₁ : s₁ ≠ 0 := fun h => hσ₁ (by rw [h1, h, zero_smul])
  have hs₂ : s₂ ≠ 0 := fun h => hσodd (by rw [h2, h, zero_smul])
  refine ⟨s * (s₁ * s₂)⁻¹, ?_⟩
  rw [hab, ha, pull_zero, zero_add, cohCast_rfl, hb, knSigmaOf, zSphereProd, h1, h2, pull_smul,
    pull_smul, pull_smul, cup_smul_right, cup_smul_left, cup_smul_right, smul_smul, smul_smul]
  congr 1
  field_simp

/-! ## 2. The total power of `z₀` -/

/-- **The degree-`0` component of the total power of `z₀` vanishes.**  At a point `z₀` restricts to
`0`, since it contains a circle class; so does its total power, by naturality; and restriction to a
point is injective on `H⁰(S^{2n+1} × S¹)`, a line spanned by the unit class. -/
theorem ptot_sphereProd_component_zero {p : ℕ} [Fact p.Prime] (ops : OddPTotal.EvenReducedPowers p)
    (n : ℕ) (σ₁ : TotalPieceOf (ZMod p) (TopCat.of (Sphere 1)) 1)
    (σodd : TotalPieceOf (ZMod p) (TopCat.of (Sphere (2 * n + 1))) (2 * n + 1)) :
    (ops.Ptot _ (OddPTotal.evenOf (ZMod p) (TopCat.of (Sphere (2 * n + 1) × Sphere 1)) (even_zDeg n)
        (zSphereProd (ZMod p) n σ₁ σodd)) : TotalHOf (ZMod p) _) 0 = 0 := by
  obtain ⟨po⟩ := sphere_nonempty (2 * n + 1) (by omega)
  obtain ⟨p1⟩ := sphere_nonempty 1 le_rfl
  let f : TopCat.of Unit ⟶ TopCat.of (Sphere (2 * n + 1) × Sphere 1) :=
    cmap (ContinuousMap.const Unit (po, p1))
  have hzf : evenMap (ZMod p) f (OddPTotal.evenOf (ZMod p) _ (even_zDeg n)
      (zSphereProd (ZMod p) n σ₁ σodd)) = 0 := by
    apply Subtype.ext
    show TotalHOf.map (ZMod p) f
      (TotalHOf.of (ZMod p) _ (1 + (2 * n + 1)) (zSphereProd (ZMod p) n σ₁ σodd)) = 0
    rw [TotalHOf.map_of, zSphereProd, pull_cup, ← pull_comp f (knPrS (Sphere (2 * n + 1)) 1) 1 σ₁,
      show f ≫ knPrS (Sphere (2 * n + 1)) 1 = cmap (ContinuousMap.const Unit p1) from rfl,
      pull_const_eq_zeroOf (ZMod p) Unit p1 1 le_rfl σ₁, zero_cup, map_zero]
  have hnat := ops.ptot_natural f (OddPTotal.evenOf (ZMod p) _ (even_zDeg n)
    (zSphereProd (ZMod p) n σ₁ σodd))
  rw [hzf, map_zero] at hnat
  have hc : TotalHOf.component (ZMod p) (TopCat.of Unit) 0 0
      = TotalHOf.component (ZMod p) (TopCat.of Unit) 0 (TotalHOf.map (ZMod p) f
          (ops.Ptot _ (OddPTotal.evenOf (ZMod p) _ (even_zDeg n)
            (zSphereProd (ZMod p) n σ₁ σodd)) : TotalHOf (ZMod p) _)) :=
    congrArg (fun w : evenPart (ZMod p) (TopCat.of Unit) =>
      TotalHOf.component (ZMod p) (TopCat.of Unit) 0 (w : TotalHOf (ZMod p) (TopCat.of Unit))) hnat
  rw [map_zero, componentOf_map] at hc
  change 0 = pull f 0 ((ops.Ptot _ (OddPTotal.evenOf (ZMod p) _ (even_zDeg n)
      (zSphereProd (ZMod p) n σ₁ σodd)) : TotalHOf (ZMod p) _) 0) at hc
  obtain ⟨a, ha⟩ := KnHemi.kunneth_lowOf (ZMod p) (Sphere (2 * n + 1)) 1 0 (by omega)
    ((ops.Ptot _ (OddPTotal.evenOf (ZMod p) _ (even_zDeg n)
      (zSphereProd (ZMod p) n σ₁ σodd)) : TotalHOf (ZMod p) _) 0)
  haveI : Nonempty (TopCat.of (Sphere (2 * n + 1))) := sphere_nonempty (2 * n + 1) (by omega)
  haveI : PathConnectedSpace (TopCat.of (Sphere (2 * n + 1))) :=
    sphere_pathConnectedSpace (2 * n + 1) (by omega)
  haveI : Nonempty (TopCat.of Unit) := ⟨()⟩
  obtain ⟨s, hs⟩ := (finrank_eq_one_iff_of_nonzero' _
    (one_ne_zero_of_nonempty (ZMod p) (TopCat.of (Sphere (2 * n + 1))))).mp
      (cohZero_finrankOf (ZMod p) (TopCat.of (Sphere (2 * n + 1)))) a
  rw [ha, ← hs, ← pull_comp, pull_smul, pull_one] at hc
  have hs0 : s = 0 := by
    rcases smul_eq_zero.mp hc.symm with h | h
    · exact h
    · exact absurd h (one_ne_zero_of_nonempty (ZMod p) (TopCat.of Unit))
  rw [ha, ← hs, hs0, zero_smul, pull_zero]

/-- **The total power of `z₀` is a multiple of `z₀`**, for nonzero sphere classes.  Its odd
components vanish because it is even; its components in even degrees other than `0` and `2n + 2`
vanish because the cohomology does; the degree-`0` component vanishes by
`ptot_sphereProd_component_zero`; and the degree-`(2n+2)` component is a multiple of `z₀`. -/
theorem ptot_sphereProd {p : ℕ} [Fact p.Prime] (ops : OddPTotal.EvenReducedPowers p) (n : ℕ)
    (σ₁ : TotalPieceOf (ZMod p) (TopCat.of (Sphere 1)) 1) (hσ₁ : σ₁ ≠ 0)
    (σodd : TotalPieceOf (ZMod p) (TopCat.of (Sphere (2 * n + 1))) (2 * n + 1)) (hσodd : σodd ≠ 0) :
    ∃ ν : ZMod p,
      (ops.Ptot _ (OddPTotal.evenOf (ZMod p) (TopCat.of (Sphere (2 * n + 1) × Sphere 1))
          (even_zDeg n) (zSphereProd (ZMod p) n σ₁ σodd)) : TotalHOf (ZMod p) _)
        = ν • TotalHOf.of (ZMod p) _ (1 + (2 * n + 1)) (zSphereProd (ZMod p) n σ₁ σodd) := by
  obtain ⟨ν, hν⟩ := sphereProd_top_eq_smul (ZMod p) n σ₁ hσ₁ σodd hσodd
    ((ops.Ptot _ (OddPTotal.evenOf (ZMod p) _ (even_zDeg n)
      (zSphereProd (ZMod p) n σ₁ σodd)) : TotalHOf (ZMod p) _) (1 + (2 * n + 1)))
  refine ⟨ν, DFinsupp.ext fun e => ?_⟩
  rw [DirectSum.smul_apply]
  rcases eq_or_ne e (1 + (2 * n + 1)) with rfl | hed
  · rw [hν]
    exact congrArg (ν • ·) (TotalHOf.component_of (ZMod p) _ _ _).symm
  · rw [show (TotalHOf.of (ZMod p) (TopCat.of (Sphere (2 * n + 1) × Sphere 1)) (1 + (2 * n + 1))
        (zSphereProd (ZMod p) n σ₁ σodd) : TotalHOf (ZMod p) _) e = 0 from
        TotalHOf.component_of_ne (ZMod p) _ hed _, smul_zero]
    rcases Nat.even_or_odd e with he | he
    · rcases eq_or_ne e 0 with rfl | he0
      · exact ptot_sphereProd_component_zero ops n σ₁ σodd
      · exact sphereProd_coh_eq_zero_of_ne (ZMod p) n e he0
          (by rintro rfl; exact Nat.not_even_one he)
          (by rintro rfl; exact Nat.not_even_iff_odd.mpr ⟨n, rfl⟩ he)
          (by omega) _
    · exact mem_evenPart.mp (ops.Ptot _ (OddPTotal.evenOf (ZMod p) _ (even_zDeg n)
        (zSphereProd (ZMod p) n σ₁ σodd))).2 e he

/-! ## 3. The product field at `N` -/

/-- **`P^i r = 0 → P^i (z · pY^* r) = 0`**, whenever the circle and odd-sphere projections factor
through a map to `S^{2n+1} × S¹`: the total power of `z` is a multiple of `z` by naturality and
`ptot_sphereProd`, so `mul_single` moves `P^i` past `z`, and naturality along `pY` finishes. -/
theorem z_mul_zero_of_sphereFactor {p : ℕ} [Fact p.Prime] (ops : OddPTotal.EvenReducedPowers p)
    (n : ℕ) {N Y : TopCat.{0}} (pY : N ⟶ Y) (q₁ : N ⟶ TopCat.of (Sphere 1))
    (qodd : N ⟶ TopCat.of (Sphere (2 * n + 1)))
    (g : N ⟶ TopCat.of (Sphere (2 * n + 1) × Sphere 1))
    (hq₁ : q₁ = g ≫ knPrS (Sphere (2 * n + 1)) 1) (hqodd : qodd = g ≫ knPrY (Sphere (2 * n + 1)) 1)
    (σ₁ : TotalPieceOf (ZMod p) (TopCat.of (Sphere 1)) 1) (hσ₁ : σ₁ ≠ 0)
    (σodd : TotalPieceOf (ZMod p) (TopCat.of (Sphere (2 * n + 1))) (2 * n + 1)) (hσodd : σodd ≠ 0) :
    ∀ (i : ℕ) (r : evenPart (ZMod p) Y), ops.P Y i r = 0 →
      ops.P N i (evenZClass (ZMod p) q₁ qodd σ₁ σodd * evenMap (ZMod p) pY r) = 0 := by
  subst hq₁ hqodd
  obtain ⟨ν, hν⟩ := ptot_sphereProd ops n σ₁ hσ₁ σodd hσodd
  have hz : evenZClass (ZMod p) (g ≫ knPrS (Sphere (2 * n + 1)) 1)
      (g ≫ knPrY (Sphere (2 * n + 1)) 1) σ₁ σodd
      = OddPTotal.evenOf (ZMod p) N (even_zDeg n)
          (pull g (1 + (2 * n + 1)) (zSphereProd (ZMod p) n σ₁ σodd)) :=
    Subtype.ext ((zClass_comp_sphereProd (ZMod p) n g σ₁ σodd).trans
      (TotalHOf.map_of (ZMod p) g (1 + (2 * n + 1)) (zSphereProd (ZMod p) n σ₁ σodd)))
  have hzM : OddPTotal.evenOf (ZMod p) N (even_zDeg n)
        (pull g (1 + (2 * n + 1)) (zSphereProd (ZMod p) n σ₁ σodd))
      = evenMap (ZMod p) g (OddPTotal.evenOf (ZMod p) _ (even_zDeg n)
          (zSphereProd (ZMod p) n σ₁ σodd)) :=
    Subtype.ext (TotalHOf.map_of (ZMod p) g (1 + (2 * n + 1)) (zSphereProd (ZMod p) n σ₁ σodd)).symm
  have hptot : (ops.Ptot N (OddPTotal.evenOf (ZMod p) N (even_zDeg n)
        (pull g (1 + (2 * n + 1)) (zSphereProd (ZMod p) n σ₁ σodd))) : TotalHOf (ZMod p) N)
      = ν • TotalHOf.of (ZMod p) N (1 + (2 * n + 1))
          (pull g (1 + (2 * n + 1)) (zSphereProd (ZMod p) n σ₁ σodd)) := by
    rw [hzM, ops.ptot_natural, coe_evenMap, hν,
      ← totalHOf_of_smul (ZMod p) _ (1 + (2 * n + 1)) ν (zSphereProd (ZMod p) n σ₁ σodd),
      TotalHOf.map_of, pull_smul, totalHOf_of_smul]
  obtain ⟨c, hc⟩ := ops.mul_single N (even_zDeg n)
    (pull g (1 + (2 * n + 1)) (zSphereProd (ZMod p) n σ₁ σodd)) ν hptot
  intro i r hr
  apply Subtype.ext
  rw [hz, hc i (evenMap (ZMod p) pY r), ops.natural, hr, map_zero]
  show c • (TotalHOf.of (ZMod p) N (1 + (2 * n + 1))
    (pull g (1 + (2 * n + 1)) (zSphereProd (ZMod p) n σ₁ σodd)) * 0) = 0
  rw [mul_zero, smul_zero]

/-! ## 4. The torus data -/

/-- **The torus data from the reduced powers.**  The operations, naturality and instability come
from `ops`; `H²(S¹) = 0`, Künneth uniqueness for `z` and the product field are the three statements
about the torus itself. -/
def RealTorusModP.ofEven {p n : ℕ} (ops : OddPTotal.EvenReducedPowers p)
    {N Y S₁ Sodd : TopCat.{0}} (pY : N ⟶ Y) (q₁ : N ⟶ S₁) (qodd : N ⟶ Sodd)
    (σ₁ : TotalPieceOf (ZMod p) S₁ 1) (σodd : TotalPieceOf (ZMod p) Sodd (2 * n + 1))
    (circle_two : ∀ a : TotalPieceOf (ZMod p) S₁ (1 + 1), a = 0)
    (z_inj : ∀ u v : TotalHOf (ZMod p) Y,
      TotalHOf.map (ZMod p) pY u + zClass (ZMod p) q₁ qodd σ₁ σodd * TotalHOf.map (ZMod p) pY v
        = 0 → v = 0)
    (z_mul_zero : ∀ (i : ℕ) (r : evenPart (ZMod p) Y), ops.P Y i r = 0 →
      ops.P N i (evenZClass (ZMod p) q₁ qodd σ₁ σodd * evenMap (ZMod p) pY r) = 0) :
    RealTorusModP n (ZMod p) pY q₁ qodd σ₁ σodd where
  circle_two := circle_two
  z_inj := z_inj
  PN := ops.P N
  PY := ops.P Y
  natural := ops.natural pY
  z_mul_zero := z_mul_zero
  PY_unstable i _ hd c h := ops.unstable Y i hd c h

/-- **The torus data of Step D mod `p` at a space isomorphic to the model**, from the reduced
powers and any nonzero sphere classes, at the projections `e ≫ KnTwo.prYOf Y n`,
`e ≫ KnTwo.prS1Of Y n`, `e ≫ KnTwo.prSoddOf Y n` (how `lx-kunneth` spells the projections of the
real mapping torus). -/
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
    (z_mul_zero_of_sphereFactor ops n _ _ _ (e.hom ≫ prSphOf Y n)
      (by rw [Category.assoc]; exact rfl) (by rw [Category.assoc]; exact rfl)
      σ₁ hσ₁ σodd hσodd)

end Gen

#audit_axioms Gen.totalHOf_of_smul
#audit_axioms Gen.sphereProd_top_eq_smul
#audit_axioms Gen.ptot_sphereProd_component_zero
#audit_axioms Gen.ptot_sphereProd
#audit_axioms Gen.z_mul_zero_of_sphereFactor
#audit_axioms Gen.RealTorusModP.ofEven
#audit_axioms Gen.realTorusModP_ofIso

end CharClass
end GroupApproximation

end
