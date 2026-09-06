import GroupApproximation.CharClass.SqDataInstance
import GroupApproximation.CharClass.CohomologyParityKunneth
import GroupApproximation.CharClass.LemmaTwoTopClass
import GroupApproximation.CharClass.LemmaTwoStepCAbsEquiv

/-!
# The even side at the geometric model of the mapping-torus base

The even and odd sides of Lemma 2 were each proved over a **different** model of
the base `N`.

* `cc-cohom-api`'s Künneth work lives at `KnTwo.NTop Y = (Y × Sphere 5) × Sphere 1`,
  left-nested, with the vendored sphere models.
* `cc-thom` and `cc-lix-odd` work at `lixN dd = ↥sphereOne × baseM dd`, that is
  `S¹ × (S⁵ × Y)`, with the circle outermost, `S⁵` the Hermitian unit sphere of
  `ℂ³` and the circle the unit sphere of the Euclidean plane.

Both are correct; they are correct about different spaces, and the contradiction
needs both about the same class on the same space.  By the lead's ruling the
geometric model wins — the mapping torus, the section, its zero, the rank
identity and the nonvanishing all live there — and this file carries the even
side across.

## What is here

* `totalH_map_comp`, `totalH_map_id` — functoriality of `TotalH.map`, which did
  not exist and which every transport below rests on.
* `lixTorusHomeo`, `lixIso` — the one model homeomorphism, from `prodComm` and
  `prodCongr` together with `cc-lix-odd`'s `unitVectorsThreeHomeoSphere` (namespace `CharClass`, not a lane
  sub-namespace).  The
  circle needs no bridge: `↥sphereOne` and the vendored `Sphere 1` are the same
  subtype of `EuclideanSpace ℝ (Fin 2)`.
* `lixPrY`, `lixPrS1`, `lixPrS5` — the three projections of the Künneth model,
  pulled back to `lixN`, so that `ι`, `t` and `x` become classes on `lixN`.
* `lix_htx_inj`, `lix_gamma_eq` — the two statements that mention `N`, carried
  across.  `hsq_b` needs no transport at all: it is a statement about `H^*(Y)`
  and the Steenrod squares there, and `N` does not occur in it.
* `lix_gamma_top_eq_zero` — the even side of Lemma 2 at `lixN`.

## Why the transport is one homeomorphism and not four

Pullback along an isomorphism is injective on `TotalH` (`totalH_map_injective_of_iso`,
from functoriality alone), so each statement crosses by applying `TotalH.map` to
it and cancelling.  Nothing is re-proved.
-/

set_option autoImplicit false

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59

namespace GroupApproximation
namespace CharClass
namespace Wu

noncomputable section

/-! ## 1. Functoriality of `TotalH.map` -/

theorem totalH_map_id (X : TopCat.{0}) (c : TotalH X) : TotalH.map (𝟙 X) c = c := by
  induction c using DirectSum.induction_on with
  | zero => rw [map_zero]
  | of n a =>
    show TotalH.map (𝟙 X) (TotalH.of X n a) = TotalH.of X n a
    rw [TotalH.map_of, pull_id]
  | add c₁ c₂ h₁ h₂ => rw [map_add, h₁, h₂]

theorem totalH_map_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (c : TotalH Z) :
    TotalH.map (f ≫ g) c = TotalH.map f (TotalH.map g c) := by
  induction c using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | of n a =>
    show TotalH.map (f ≫ g) (TotalH.of Z n a)
      = TotalH.map f (TotalH.map g (TotalH.of Z n a))
    rw [TotalH.map_of, TotalH.map_of, TotalH.map_of, pull_comp]
  | add c₁ c₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add]

/-- Pullback along an isomorphism is injective on the whole ring. -/
theorem totalH_map_injective_of_iso {X Y : TopCat.{0}} (e : X ≅ Y) :
    Function.Injective (TotalH.map e.hom) := by
  have hinv : ∀ z : TotalH Y, TotalH.map e.inv (TotalH.map e.hom z) = z := by
    intro z
    rw [← totalH_map_comp, e.inv_hom_id, totalH_map_id]
  intro c c' hcc
  rw [← hinv c, ← hinv c', hcc]

/-! ## 2. The one model homeomorphism -/

variable {ℓ : ℕ}

/-- The circle of the geometric model **is** the vendored `S¹`: both are the unit
sphere of `EuclideanSpace ℝ (Fin 2)`, and `Fin (1 + 1)` reduces to `Fin 2` at the
index without unfolding anything. -/
def circHomeo : ↥sphereOne ≃ₜ Sphere 1 := Homeomorph.refl _

/-- **The model homeomorphism.**  `S¹ × (S⁵ × Y)` with the circle outermost is
`(Y × S⁵) × S¹` left-nested. -/
def lixTorusHomeo (dd : Fin ℓ → ℕ) :
    (↥sphereOne × baseM dd) ≃ₜ KnTwo.torusBase (baseY dd) :=
  ((circHomeo.prodCongr
        (unitVectorsThreeHomeoSphere.prodCongr
          (Homeomorph.refl (baseY dd)))).trans
      (Homeomorph.prodComm _ _)).trans
    ((Homeomorph.prodComm _ _).prodCongr (Homeomorph.refl (Sphere 1)))

/-- The model homeomorphism as an isomorphism of `TopCat` objects. -/
def lixIso (dd : Fin ℓ → ℕ) : lixN dd ≅ KnTwo.NTop (baseY dd) :=
  TopCat.isoOfHomeo (lixTorusHomeo dd)

/-! ## 3. The three projections, carried to `lixN` -/

/-- The projection to `Y`, at the geometric model. -/
def lixPrY (dd : Fin ℓ → ℕ) : lixN dd ⟶ KnTwo.YTop (baseY dd) :=
  (lixIso dd).hom ≫ KnTwo.prY (baseY dd)

/-- The projection to the circle factor, at the geometric model. -/
def lixPrS1 (dd : Fin ℓ → ℕ) : lixN dd ⟶ TopCat.of (Sphere 1) :=
  (lixIso dd).hom ≫ KnTwo.prS1 (baseY dd)

/-- The projection to the `S⁵` factor, at the geometric model. -/
def lixPrS5 (dd : Fin ℓ → ℕ) : lixN dd ⟶ TopCat.of (Sphere 5) :=
  (lixIso dd).hom ≫ KnTwo.prS5 (baseY dd)

theorem map_hom_tClass (dd : Fin ℓ → ℕ) (σ : Hmod2 (TopCat.of (Sphere 1)) 1) :
    TotalH.map (lixIso dd).hom (tClass (KnTwo.prS1 (baseY dd)) σ)
      = tClass (lixPrS1 dd) σ := by
  show TotalH.map (lixIso dd).hom
      (TotalH.map (KnTwo.prS1 (baseY dd)) (TotalH.of (TopCat.of (Sphere 1)) 1 σ))
    = TotalH.map (lixPrS1 dd) (TotalH.of (TopCat.of (Sphere 1)) 1 σ)
  rw [← totalH_map_comp]
  rfl

theorem map_hom_xClass (dd : Fin ℓ → ℕ) (σ : Hmod2 (TopCat.of (Sphere 5)) 5) :
    TotalH.map (lixIso dd).hom (xClass (KnTwo.prS5 (baseY dd)) σ)
      = xClass (lixPrS5 dd) σ := by
  show TotalH.map (lixIso dd).hom
      (TotalH.map (KnTwo.prS5 (baseY dd)) (TotalH.of (TopCat.of (Sphere 5)) 5 σ))
    = TotalH.map (lixPrS5 dd) (TotalH.of (TopCat.of (Sphere 5)) 5 σ)
  rw [← totalH_map_comp]
  rfl

theorem map_hom_prY (dd : Fin ℓ → ℕ) (w : TotalH (KnTwo.YTop (baseY dd))) :
    TotalH.map (lixIso dd).hom (TotalH.map (KnTwo.prY (baseY dd)) w)
      = TotalH.map (lixPrY dd) w := by
  rw [← totalH_map_comp]
  rfl

/-! ## 4. The two statements that mention `N`, carried across -/

/-- **`tx_inj` at the geometric model.** -/
theorem lix_htx_inj (dd : Fin ℓ → ℕ) (u v : TotalH (KnTwo.YTop (baseY dd)))
    (h : TotalH.map (lixPrY dd) u
        + tClass (lixPrS1 dd) (sphereTopClass 1 (by omega))
          * xClass (lixPrS5 dd) (sphereTopClass 5 (by omega))
          * TotalH.map (lixPrY dd) v = 0) : v = 0 := by
  refine KnTwo.htx_inj (baseY dd) u v ?_
  refine totalH_map_injective_of_iso (lixIso dd) ?_
  rw [map_zero, map_add, map_mul, map_mul, map_hom_prY, map_hom_prY,
    map_hom_tClass, map_hom_xClass]
  exact h

/-- **The Künneth decomposition at the geometric model.** -/
theorem lix_gamma_eq (dd : Fin ℓ → ℕ) (γ : ℕ → TotalH (lixN dd))
    (a b : ℕ → TotalH (KnTwo.YTop (baseY dd)))
    (h : ∀ k : ℕ, TotalH.map (lixIso dd).inv (γ k)
        = TotalH.map (KnTwo.prY (baseY dd)) (a k)
          + tClass (KnTwo.prS1 (baseY dd)) (sphereTopClass 1 (by omega))
            * xClass (KnTwo.prS5 (baseY dd)) (sphereTopClass 5 (by omega))
            * TotalH.map (KnTwo.prY (baseY dd)) (b k)) :
    ∀ k : ℕ, γ k = TotalH.map (lixPrY dd) (a k)
      + tClass (lixPrS1 dd) (sphereTopClass 1 (by omega))
        * xClass (lixPrS5 dd) (sphereTopClass 5 (by omega))
        * TotalH.map (lixPrY dd) (b k) := by
  intro k
  have hk := congrArg (TotalH.map (lixIso dd).hom) (h k)
  rw [← totalH_map_comp, (lixIso dd).hom_inv_id, totalH_map_id, map_add, map_mul,
    map_mul, map_hom_prY, map_hom_prY, map_hom_tClass, map_hom_xClass] at hk
  exact hk

/-! ## 5. The `a` and `b` of a `ChernSplit`, and its instability -/

/-- The `H^*(Y)`-coordinate of a `ChernSplit`, in the ring. -/
def splitA (dd : Fin ℓ → ℕ) {γN : ℕ → TotalH (KnTwo.NTop (baseY dd))}
    (S : KnTwo.ChernSplit (baseY dd) γN) (k : ℕ) : TotalH (KnTwo.YTop (baseY dd)) :=
  TotalH.of (KnTwo.YTop (baseY dd)) (2 * k) (S.alpha k)

/-- The `t x`-coordinate of a `ChernSplit`, in the ring. -/
def splitB (dd : Fin ℓ → ℕ) {γN : ℕ → TotalH (KnTwo.NTop (baseY dd))}
    (S : KnTwo.ChernSplit (baseY dd) γN) (k : ℕ) : TotalH (KnTwo.YTop (baseY dd)) :=
  TotalH.of (KnTwo.YTop (baseY dd)) (2 * k - 6) (S.beta k)

/-- **`hsq_b` needs no transport**: neither `N` nor the model occurs in it. -/
theorem splitB_sq (dd : Fin ℓ → ℕ) {γN : ℕ → TotalH (KnTwo.NTop (baseY dd))}
    (S : KnTwo.ChernSplit (baseY dd) γN) :
    ∀ k j : ℕ, 2 * k < j + 6 →
      Steenrod.SqH (KnTwo.YTop (baseY dd)) j (splitB dd S k) = 0 := by
  refine sq_b_of_grading (splitB dd S) ?_ ?_
  · intro k hk
    show TotalH.of (KnTwo.YTop (baseY dd)) (2 * k - 6) (S.beta k) = 0
    rw [S.beta_low k (by omega), map_zero]
  · intro k c hkc
    have hc : c = 2 * k - 6 := by omega
    subst hc
    exact ⟨S.beta k, rfl⟩

/-! ## 6. The even side of Lemma 2, at the geometric model -/

/-- **Lemma 2, the even half, at `lixN`.**  Every class here is a class on the
space `cc-thom` and `cc-lix-odd` work over, so this is the statement the
contradiction can use against their nonvanishing. -/
theorem lix_gamma_top_eq_zero (dd : Fin ℓ → ℕ) (hC : CartanTotal)
    (γ : ℕ → TotalH (lixN dd))
    (S : KnTwo.ChernSplit (baseY dd) (fun k => TotalH.map (lixIso dd).inv (γ k)))
    (hsplit : HasSplitting (lixN dd) γ)
    (gen : Fin ℓ → TotalH (KnTwo.YTop (baseY dd)))
    (hd : ∀ j, Even (dd j))
    (hslice : ∀ q : ℕ,
      splitA dd S q = (sliceClass (Finset.univ : Finset (Fin ℓ)) gen dd).coeff q) :
    γ ((∑ j, dd j) + 3) = 0 := by
  refine gamma_top_eq_zero_of_hasSplitting (lixPrY dd) (lixPrS1 dd) (lixPrS5 dd)
    (hasSphereCohomology_sphere 1 (by omega)) (hasSphereCohomology_sphere 5 (by omega))
    (sphereTopClass 1 (by omega)) (sphereTopClass 5 (by omega))
    γ (splitA dd S) (splitB dd S) hC
    (lix_htx_inj dd)
    (lix_gamma_eq dd γ (splitA dd S) (splitB dd S) S.split)
    (splitB_sq dd S) hsplit Finset.univ gen dd (fun j _ => hd j) hslice

end

end Wu
end CharClass
end GroupApproximation
