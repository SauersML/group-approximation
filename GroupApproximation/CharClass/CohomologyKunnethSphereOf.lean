import GroupApproximation.CharClass.CohomologyKunnethSphere
import GroupApproximation.CharClass.KroneckerContractible
import GroupApproximation.Meta.AxiomGuard

/-!
# Covers of a product and Künneth vanishing with a sphere factor, over any field

Lane `lix-coeff` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.5).

Additive twin of `CohomologyProductCover` and `CohomologyKunnethSphere` with the coefficients a
field `K`.  Every step of the `F₂` files is coefficient-free except its inputs, which exist over
`K`:

* Mayer–Vietoris in vanishing form, from `CohomologyMayerVietoris`' generic `mvCoSCOf K`,
  `mvExactOf_ambient`, `isZero_mvCoX2Of`, `mvInterIsoOf`, `mvAmbientIsoOf`;
* homotopy invariance over any ring, `KroneckerContractible.pullEquivOfHomotopyEquivOf`;
* contractible spaces have no positive cohomology, `cohomology_isZero_of_contractibleOf`.

The opens `prodOpen`, the homeomorphism `prodSubtypeHomeo`, the hemispherical cover and the band
equivalence carry no coefficients and are the `F₂` files' own.

## Main declarations

* `isZero_mvAmbientOf` — Mayer–Vietoris, vanishing form, over `K`.
* `isZero_prodOpen_of_contractibleOf`, `isZero_cohomology_of_isEmptyOf`.
* `isZero_prod_sphere_succOf` — the Künneth vanishing step over `K`.
* `sphereCohSuspensionOf` — `H^j(S^n; K) ≅ H^{j+1}(S^{n+1}; K)` for `j ≥ 1`.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-! ## 1. Transport of vanishing -/

/-- Vanishing transports along a linear equivalence, over any ring. -/
theorem isZero_of_linearEquivOf {K : Type} [CommRing K] {M N : ModuleCat.{0} K}
    (e : M ≃ₗ[K] N) (h : IsZero M) : IsZero N := by
  rw [ModuleCat.isZero_iff_subsingleton] at h ⊢
  haveI := h
  exact e.toEquiv.symm.subsingleton

/-! ## 2. Mayer–Vietoris in vanishing form -/

/-- **Mayer–Vietoris, vanishing form, over a field.**  If `H^m(U ∩ V; K) = 0` and both
`H^{m+1}(U; K)` and `H^{m+1}(V; K)` vanish, then `H^{m+1}(Z; K) = 0`. -/
theorem isZero_mvAmbientOf (K : Type) [Field K] {Z : TopCat.{0}} (U V : Opens Z)
    (hUV : U ⊔ V = ⊤) (m : ℕ)
    (hI : IsZero (Hmod K (TopCat.of ↥((U : Set Z) ∩ (V : Set Z))) m))
    (hU : IsZero (Hmod K (TopCat.of (U : Set Z)) (m + 1)))
    (hV : IsZero (Hmod K (TopCat.of (V : Set Z)) (m + 1))) :
    IsZero (Hmod K Z (m + 1)) := by
  have h1 : IsZero ((mvCoSCOf K U V hUV).X₃.homology m) :=
    IsZero.of_iso hI (mvInterIsoOf K U V hUV m)
  have h2 : IsZero ((mvCoSCOf K U V hUV).X₂.homology (m + 1)) :=
    isZero_mvCoX2Of K U V hUV (m + 1) hU hV
  have hz : IsZero ((mvCoSCOf K U V hUV).X₁.homology (m + 1)) :=
    (mvExactOf_ambient K U V hUV m).isZero_X₂ (h1.eq_of_src _ _) (h2.eq_of_tgt _ _)
  exact IsZero.of_iso hz (mvAmbientIsoOf K U V hUV (m + 1)).symm

/-! ## 3. Opens of a product -/

/-- The cohomology of the open `A × U` is that of `A × ↥U`, over any ring. -/
def prodOpenCohEquivOf (K : Type) [CommRing K] (A : Type) [TopologicalSpace A] {Y : Type}
    [TopologicalSpace Y] (U : Opens Y) (k : ℕ) :
    Hmod K (TopCat.of (A × ↥(U : Set Y))) k
      ≃ₗ[K] Hmod K (TopCat.of ↥((prodOpen A U : Opens (A × Y)) : Set (A × Y))) k :=
  pullEquivOfHomotopyEquivOf K (prodSubtypeHomeo A (U : Set Y)).toHomotopyEquiv k

/-- `H^n(X × C; K) ≅ H^n(X; K)` for contractible `C`, realized by the first projection. -/
def cohProdContractibleOf (K : Type) [CommRing K] (X C : Type) [TopologicalSpace X]
    [TopologicalSpace C] [ContractibleSpace C] (n : ℕ) :
    Hmod K (TopCat.of X) n ≃ₗ[K] Hmod K (TopCat.of (X × C)) n :=
  pullEquivOfHomotopyEquivOf K (prodContractibleEquiv X C) n

/-- **`A × U` inherits the vanishing of `A` when `U` is contractible**, over any ring. -/
theorem isZero_prodOpen_of_contractibleOf (K : Type) [CommRing K] (A : Type) [TopologicalSpace A]
    {Y : Type} [TopologicalSpace Y] (U : Opens Y) [ContractibleSpace ↥(U : Set Y)] (k : ℕ)
    (h : IsZero (Hmod K (TopCat.of A) k)) :
    IsZero (Hmod K (TopCat.of ↥((prodOpen A U : Opens (A × Y)) : Set (A × Y))) k) :=
  isZero_of_linearEquivOf (prodOpenCohEquivOf K A U k)
    (isZero_of_linearEquivOf (cohProdContractibleOf K A ↥(U : Set Y) k) h)

/-! ## 4. The empty space -/

/-- All cochains on a space with no points agree, over any ring. -/
theorem subsingleton_cochainGroup_of_isEmptyOf (K : Type) [CommRing K] (Y : TopCat.{0})
    [IsEmpty Y] (n : ℕ) : Subsingleton (singularCochainGroup K Y n) := by
  haveI := isEmpty_singularSimplices Y n
  exact ⟨fun _ _ => cochain_ext (fun τ => (IsEmpty.false τ).elim)⟩

/-- **`H^k(∅; K) = 0` in every degree.** -/
theorem isZero_cohomology_of_isEmptyOf (K : Type) [CommRing K] (Y : Type) [TopologicalSpace Y]
    [IsEmpty Y] (k : ℕ) : IsZero (Hmod K (TopCat.of Y) k) := by
  haveI : IsEmpty (TopCat.of Y) := inferInstanceAs (IsEmpty Y)
  haveI := subsingleton_cochainGroup_of_isEmptyOf K (TopCat.of Y) k
  rw [ModuleCat.isZero_iff_subsingleton]
  constructor
  intro a b
  obtain ⟨φ, hφ, rfl⟩ := exists_cocycleOf a
  obtain ⟨ψ, hψ, rfl⟩ := exists_cocycleOf b
  exact cocycleClassK_congr K (TopCat.of Y) k (Subsingleton.elim φ ψ) hφ hψ

/-! ## 5. Künneth vanishing with a sphere factor -/

/-- `H^m(A × band; K) = 0` as soon as `H^m(A × S^n; K) = 0`. -/
theorem isZero_prod_bandOf (K : Type) [CommRing K] (A : Type) [TopologicalSpace A] (n m : ℕ)
    (hband : IsZero (Hmod K (TopCat.of (A × Sphere n)) m)) :
    IsZero (Hmod K (TopCat.of ↥(Prod.snd ⁻¹' (sphereBand n) : Set (A × Sphere (n + 1)))) m) :=
  isZero_of_linearEquivOf
    (pullEquivOfHomotopyEquivOf K (prodSubtypeHomeo A (sphereBand n)).toHomotopyEquiv m)
    (isZero_of_linearEquivOf
      (pullEquivOfHomotopyEquivOf K
        ((ContinuousMap.HomotopyEquiv.refl A).prodCongr (sphereBandHomotopyEquiv n)) m)
      hband)

set_option maxHeartbeats 1000000 in
/-- **The Künneth vanishing step over a field.**  If the cohomology of `A × S^n` vanishes in
degree `m` and that of `A` in degree `m+1`, then the cohomology of `A × S^{n+1}` vanishes in
degree `m+1`. -/
theorem isZero_prod_sphere_succOf (K : Type) [Field K] (A : Type) [TopologicalSpace A] (n m : ℕ)
    (hband : IsZero (Hmod K (TopCat.of (A × Sphere n)) m))
    (hA : IsZero (Hmod K (TopCat.of A) (m + 1))) :
    IsZero (Hmod K (TopCat.of (A × Sphere (n + 1))) (m + 1)) := by
  refine isZero_mvAmbientOf K (prodOpen A (upperOpens n)) (prodOpen A (lowerOpens n))
    (prodOpen_sup A (upperOpens_sup_lowerOpens n)) m ?_
    (isZero_prodOpen_of_contractibleOf K A (upperOpens n) (m + 1) hA)
    (isZero_prodOpen_of_contractibleOf K A (lowerOpens n) (m + 1) hA)
  rw [prodOpen_coe_inter, upperOpens_inter_lowerOpens]
  exact isZero_prod_bandOf K A n m hband

/-- **`H^j(S^n; K) ≅ H^{j+1}(S^{n+1}; K)` for `j ≥ 1`.**  The two hemispheres are contractible,
so the Mayer–Vietoris connecting map from the band is an isomorphism; the band is homotopy
equivalent to `S^n`. -/
def sphereCohSuspensionOf (K : Type) [Field K] (n j : ℕ) (hj : 1 ≤ j) :
    Hmod K (TopCat.of (Sphere n)) j ≃ₗ[K] Hmod K (TopCat.of (Sphere (n + 1))) (j + 1) :=
  (pullEquivOfHomotopyEquivOf K (sphereBandHomotopyEquiv n) j).trans
    (mvConnectingIsoOf K (upperOpens n) (lowerOpens n) (upperOpens_sup_lowerOpens n) j
      (cohomology_isZero_of_contractibleOf K _ j hj)
      (cohomology_isZero_of_contractibleOf K _ j hj)
      (cohomology_isZero_of_contractibleOf K _ (j + 1) (by omega))
      (cohomology_isZero_of_contractibleOf K _ (j + 1) (by omega))).toLinearEquiv

end

/-! Audited on every build. -/

#audit_axioms isZero_mvAmbientOf
#audit_axioms isZero_cohomology_of_isEmptyOf
#audit_axioms isZero_prod_sphere_succOf

end GroupApproximation.CharClass
