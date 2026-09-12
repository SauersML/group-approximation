import GroupApproximation.CharClass.CohomologyKunnethTorusN
import GroupApproximation.CharClass.LIXKGenChern
import GroupApproximation.CharClass.LIXKGenSphere
import GroupApproximation.CharClass.LerayHirschBundle
import GroupApproximation.CharClass.ParityEvenTransport
import GroupApproximation.Meta.AxiomGuard

/-!
# The Künneth objects of the rank-`n` LIX base, mod 2

Lane `lx-kunneth` of the STW Problem LIX strengthening (`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`
§1.4).  Residual (b) of `Gen.lemmaTwoFor_powers_two_lixChernOf` (`CharClass/LIXLemmaTwoGenTwo.lean`)
is its binder `data`, a mod-2 `Gen.WuStepDData n dd pY q₁ qodd σ₁ σodd γ` over the geometric base
`KGen.lixN n dd = S¹ × S^{2n+1} × ∏ⱼ ℂP^{dⱼ}`.  This file supplies the Künneth side of that
record: the three projections, the sphere classes, and the fields `tx_inj` and `gamma_eq` together
with the instability input of `sq_b`.

It is `CharClass/ParityEvenTransport.lean` at rank `n`.  The Künneth work lives on the left-nested
model `KnTwo.torusBaseOf Y n = (Y × S^{2n+1}) × S¹` (`CharClass/CohomologyKunnethTorusN.lean`), and
one homeomorphism carries it to the geometric base.  The circle needs no bridge, `↥sphereOne` and
the vendored `Sphere 1` being the same subtype; the odd sphere is carried by
`KGen.unitVectorsHomeo n`.  Each statement crosses by applying `TotalH.map` along the isomorphism and
cancelling (`Wu.totalH_map_injective_of_iso`), so nothing is re-proved.

**The slice stays definitional.**  For a slice `y ↦ (p₁, (q, y))` of `KGen.lixN n dd`, composing
with `KnLix.prY n dd` is the identity and composing with `KnLix.prS1 n dd` is the constant map at
`p₁`, both by `rfl`: the homeomorphism is built from `Homeomorph.refl` on the circle and on `Y`
and two `prodComm`s, and neither moves `y` or `p₁`.

## Main declarations

* `KnLix.torusHomeo`, `KnLix.lixIso` — the model homeomorphism and its `TopCat` isomorphism.
* `KnLix.prY`, `KnLix.prS1`, `KnLix.prSodd` — the three projections at the geometric base.
* `KnLix.tx_inj` — the field `tx_inj`, at `σ₁ = sphereTopClass 1 _`, `σodd = sphereTopClass (2n+1) _`.
* `KnLix.chern_split` — every even class of the base splits in the ring.
* `KnLix.gamma_split_of_graded`, `KnLix.gamma_split_mappingTorus` — **the fields `gamma_eq` and
  `sq_b`**, for any degreewise family and for the Chern classes of a mapping torus.
-/

open CategoryTheory Limits TopologicalSpace
open scoped Matrix
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace KnLix

variable {ℓ : ℕ}

/-! ## 1. The model homeomorphism and the projections -/

/-- **The model homeomorphism at rank `n`.**  `S¹ × (S^{2n+1} × Y)` with the circle outermost is
`(Y × S^{2n+1}) × S¹` left-nested. -/
def torusHomeo (n : ℕ) (dd : Fin ℓ → ℕ) :
    (↥sphereOne × Gen.baseM n dd) ≃ₜ KnTwo.torusBaseOf (baseY dd) n :=
  (((Homeomorph.refl ↥sphereOne).prodCongr
        ((KGen.unitVectorsHomeo n).prodCongr (Homeomorph.refl (baseY dd)))).trans
      (Homeomorph.prodComm _ _)).trans
    ((Homeomorph.prodComm _ _).prodCongr (Homeomorph.refl (Sphere 1)))

/-- The model homeomorphism as an isomorphism of `TopCat` objects. -/
def lixIso (n : ℕ) (dd : Fin ℓ → ℕ) :
    KGen.lixN n dd ≅ TopCat.of (KnTwo.torusBaseOf (baseY dd) n) :=
  TopCat.isoOfHomeo (torusHomeo n dd)

/-- The projection to `Y`, at the geometric base. -/
def prY (n : ℕ) (dd : Fin ℓ → ℕ) : KGen.lixN n dd ⟶ TopCat.of (baseY dd) :=
  (lixIso n dd).hom ≫ KnTwo.prYOf (baseY dd) n

/-- The projection to the circle factor, at the geometric base. -/
def prS1 (n : ℕ) (dd : Fin ℓ → ℕ) : KGen.lixN n dd ⟶ TopCat.of (Sphere 1) :=
  (lixIso n dd).hom ≫ KnTwo.prS1Of (baseY dd) n

/-- The projection to the odd sphere factor, at the geometric base. -/
def prSodd (n : ℕ) (dd : Fin ℓ → ℕ) : KGen.lixN n dd ⟶ TopCat.of (Sphere (2 * n + 1)) :=
  (lixIso n dd).hom ≫ KnTwo.prSoddOf (baseY dd) n

/-! ## 2. Carrying the classes across -/

theorem map_hom_prY (n : ℕ) (dd : Fin ℓ → ℕ) (w : TotalH (TopCat.of (baseY dd))) :
    TotalH.map (lixIso n dd).hom (TotalH.map (KnTwo.prYOf (baseY dd) n) w)
      = TotalH.map (prY n dd) w := by
  rw [← Wu.totalH_map_comp]
  rfl

theorem map_hom_tClass (n : ℕ) (dd : Fin ℓ → ℕ) (σ : Hmod2 (TopCat.of (Sphere 1)) 1) :
    TotalH.map (lixIso n dd).hom (Wu.tClass (KnTwo.prS1Of (baseY dd) n) σ)
      = Wu.tClass (prS1 n dd) σ := by
  show TotalH.map (lixIso n dd).hom
      (TotalH.map (KnTwo.prS1Of (baseY dd) n) (TotalH.of (TopCat.of (Sphere 1)) 1 σ))
    = TotalH.map (prS1 n dd) (TotalH.of (TopCat.of (Sphere 1)) 1 σ)
  rw [← Wu.totalH_map_comp]
  rfl

theorem map_hom_sphereClass (n : ℕ) (dd : Fin ℓ → ℕ) {c : ℕ}
    (σ : Hmod2 (TopCat.of (Sphere (2 * n + 1))) c) :
    TotalH.map (lixIso n dd).hom (Gen.sphereClass (KnTwo.prSoddOf (baseY dd) n) σ)
      = Gen.sphereClass (prSodd n dd) σ := by
  show TotalH.map (lixIso n dd).hom
      (TotalH.map (KnTwo.prSoddOf (baseY dd) n) (TotalH.of (TopCat.of (Sphere (2 * n + 1))) c σ))
    = TotalH.map (prSodd n dd) (TotalH.of (TopCat.of (Sphere (2 * n + 1))) c σ)
  rw [← Wu.totalH_map_comp]
  rfl

/-! ## 3. The fields -/

/-- **The field `tx_inj` of `Gen.WuStepDData` at the geometric base.** -/
theorem tx_inj (n : ℕ) (dd : Fin ℓ → ℕ) :
    ∀ u v : TotalH (TopCat.of (baseY dd)),
      TotalH.map (prY n dd) u
          + Wu.tClass (prS1 n dd) (sphereTopClass 1 (by omega))
            * Gen.sphereClass (prSodd n dd) (sphereTopClass (2 * n + 1) (by omega))
            * TotalH.map (prY n dd) v = 0 → v = 0 := by
  intro u v h
  refine KnTwo.tx_injN (baseY dd) n u v ?_
  refine Wu.totalH_map_injective_of_iso (lixIso n dd) ?_
  rw [map_zero, map_add, map_mul, map_mul, map_hom_prY, map_hom_prY, map_hom_tClass,
    map_hom_sphereClass]
  exact h

set_option maxHeartbeats 1000000 in
/-- **Every even class of the rank-`n` base splits in the ring**, mod 2: `x = pr_Y^* α +
t x pr_Y^* β` with `β` of degree `d − (2n + 2)`, and `β = 0` below `2n + 2`. -/
theorem chern_split (n : ℕ) (dd : Fin ℓ → ℕ) (d : ℕ) (hd : Even d)
    (x : Hmod2 (KGen.lixN n dd) d) :
    ∃ (α : Hmod2 (TopCat.of (baseY dd)) d) (β : Hmod2 (TopCat.of (baseY dd)) (d - (2 * n + 2))),
      (d < 2 * n + 2 → β = 0) ∧
      TotalH.of (KGen.lixN n dd) d x
        = TotalH.map (prY n dd) (TotalH.of (TopCat.of (baseY dd)) d α)
          + Wu.tClass (prS1 n dd) (sphereTopClass 1 (by omega))
            * Gen.sphereClass (prSodd n dd) (sphereTopClass (2 * n + 1) (by omega))
            * TotalH.map (prY n dd) (TotalH.of (TopCat.of (baseY dd)) (d - (2 * n + 2)) β) := by
  obtain ⟨α, β, hβ, hsplit⟩ := KnTwo.totalSplitN (baseY dd) n (noOddCohomology_baseY dd) d hd
    (pull (lixIso n dd).inv d x)
  refine ⟨α, β, hβ, ?_⟩
  have hk := congrArg (TotalH.map (lixIso n dd).hom) hsplit
  rw [← TotalH.map_of, ← Wu.totalH_map_comp, (lixIso n dd).hom_inv_id, Wu.totalH_map_id,
    map_add, map_mul, map_mul, map_hom_prY, map_hom_prY, map_hom_tClass,
    map_hom_sphereClass] at hk
  exact hk

/-- **The fields `gamma_eq` and `sq_b` of `Gen.WuStepDData`, for a degreewise family.**  If each
`γ k` is concentrated in degree `2k`, then `γ k = pr_Y^* a_k + t x pr_Y^* b_k` with `b_k` of degree
`2k − (2n + 2)`, and `b_k` is killed by `Sq^j` whenever `2k < j + (2n + 2)`. -/
theorem gamma_split_of_graded (n : ℕ) (dd : Fin ℓ → ℕ) (γ : ℕ → TotalH (KGen.lixN n dd))
    (g : ∀ k : ℕ, Hmod2 (KGen.lixN n dd) (2 * k))
    (hg : ∀ k : ℕ, γ k = TotalH.of (KGen.lixN n dd) (2 * k) (g k)) :
    ∃ a b : ℕ → TotalH (TopCat.of (baseY dd)),
      (∀ k : ℕ, γ k = TotalH.map (prY n dd) (a k)
          + Wu.tClass (prS1 n dd) (sphereTopClass 1 (by omega))
            * Gen.sphereClass (prSodd n dd) (sphereTopClass (2 * n + 1) (by omega))
            * TotalH.map (prY n dd) (b k)) ∧
      (∀ k j : ℕ, 2 * k < j + (2 * n + 2) → Steenrod.SqH (TopCat.of (baseY dd)) j (b k) = 0) := by
  choose α β hβ hsplit using fun k => chern_split n dd (2 * k) ⟨k, by omega⟩ (g k)
  refine ⟨fun k => TotalH.of (TopCat.of (baseY dd)) (2 * k) (α k),
    fun k => TotalH.of (TopCat.of (baseY dd)) (2 * k - (2 * n + 2)) (β k), fun k => ?_, ?_⟩
  · rw [hg k]
    exact hsplit k
  · refine Gen.sq_b_of_grading n _ (fun k hk => ?_) (fun k c hc => ?_)
    · show TotalH.of (TopCat.of (baseY dd)) (2 * k - (2 * n + 2)) (β k) = 0
      rw [hβ k (by omega), map_zero]
    · exact ⟨cohCast (show 2 * k - (2 * n + 2) = c by omega) (β k),
        (KnTwo.totalH_of_cohCast _ _).symm⟩

/-- **The fields `gamma_eq` and `sq_b` at the Chern classes of a mapping torus**, at the `γfun`
spelling of `CharClass/LIXLemmaTwoGenTwo.lean`. -/
theorem gamma_split_mappingTorus (n : ℕ) (dd : Fin ℓ → ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    ∃ a b : ℕ → TotalH (TopCat.of (baseY dd)),
      (∀ k : ℕ, KGen.lixChernOf n (KGen.lixChern n dd)
            (mappingTorus (Gen.Vmat n) G circHoriz circHeight) k
          = TotalH.map (prY n dd) (a k)
            + Wu.tClass (prS1 n dd) (sphereTopClass 1 (by omega))
              * Gen.sphereClass (prSodd n dd) (sphereTopClass (2 * n + 1) (by omega))
              * TotalH.map (prY n dd) (b k)) ∧
      (∀ k j : ℕ, 2 * k < j + (2 * n + 2) → Steenrod.SqH (TopCat.of (baseY dd)) j (b k) = 0) :=
  gamma_split_of_graded n dd _ _
    (fun k => KGen.lixChernOf_mappingTorus n (KGen.lixChern n dd) hGc hGu k)

end KnLix

end

/-! Audited on every build. -/

#audit_axioms KnLix.tx_inj
#audit_axioms KnLix.chern_split
#audit_axioms KnLix.gamma_split_of_graded
#audit_axioms KnLix.gamma_split_mappingTorus

end GroupApproximation.CharClass
