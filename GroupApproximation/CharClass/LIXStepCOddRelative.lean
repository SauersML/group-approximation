import GroupApproximation.CharClass.LIXBundlePair
import GroupApproximation.CharClass.RelativeSubspaceIso
import GroupApproximation.CharClass.RelativeRangeKer
import GroupApproximation.CharClass.RelativeProdContractible

/-!
# The relative-cohomology inputs of Step C's odd side

The eight binders of `cc-lix-odd`'s `lix_topClass_ne_zero_of_local`
(`CharClass/LIXStepCOddLocal.lean`) that belong to the relative-cohomology layer,
supplied here as terms at exactly those objects.  Nothing here is new
mathematics: each is an instantiation of a general statement of this lane at
`cc-lix-odd`'s spaces, maps and degree.  They are collected in one module so that
the consuming theorem's argument list can be filled from a single import.

Three concern the base pair `(lixN dd, {lixZero dd}ᶜ)`:

* `lixJ` is `relToAbs`, `lixI` is `absToSub`, and `lixHexact` is
  `relLES_range_eq_ker` — the long exact sequence of the pair, at these objects.

Five concern the bundle pair `(lixTotalPair, lixPuncturedInTotal)` and the
section:

* `lixHE` is the absolute cohomology of the total space and `lixJE` its
  relative-to-absolute map;
* `lixSAbs` and `lixPiStar` are the absolute pullbacks along `cc-lix-odd`'s
  section and along the bundle projection.  The section is *their* term,
  `lixSectionTotal`, not a new spelling: `lixSRel` is by definition `relPullback`
  along it, which is what makes `lixHnat` an instance of `relToAbs_naturality`
  rather than a computation;
* `lixHnat` is that naturality square, and `lixHsection` is functoriality of the
  absolute pullback applied to `s ≫ π = 𝟙`, which holds on the nose because the
  projection of the section at `x` is `x` definitionally.

## Main definitions

* `lixJ`, `lixI`, `lixJE`, `lixSAbs`, `lixPiStar`, and the spaces' maps `lixS`, `lixPi`.

## Main results

* `lixHexact`, `lixHnat`, `lixHsection` — the three properties the consumer takes.
-/

open scoped Matrix
open CategoryTheory Limits AlgebraicTopology
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

namespace RelativeSupport

noncomputable section

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ} {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}

/-! ## 1. The base pair -/

/-- `j`: the relative-to-absolute map of the pair `(lixN dd, {lixZero dd}ᶜ)`. -/
def lixJ (dd : Fin ℓ → ℕ) (n : ℕ) :
    relCohomology (ZMod 2) (lixN dd)
        ({lixZero dd}ᶜ : Set (↥sphereOne × baseM dd)) n ⟶
      cohomologyZMod2 (lixN dd) n :=
  relToAbs (ZMod 2) (lixN dd) ({lixZero dd}ᶜ : Set (↥sphereOne × baseM dd)) n

/-- `i`: restriction to the complement of the zero. -/
def lixI (dd : Fin ℓ → ℕ) (n : ℕ) :
    cohomologyZMod2 (lixN dd) n ⟶
      cohomologyZMod2 (TopCat.of ↥({lixZero dd}ᶜ : Set (↥sphereOne × baseM dd))) n :=
  absToSub (X := lixN dd) (ZMod 2) ({lixZero dd}ᶜ) n

/-- `hexact`: exactness of the pair sequence at the absolute group. -/
theorem lixHexact (dd : Fin ℓ → ℕ) (n : ℕ) :
    LinearMap.range (lixJ dd n).hom = LinearMap.ker (lixI dd n).hom :=
  relLES_range_eq_ker (lixN dd) ({lixZero dd}ᶜ : Set (↥sphereOne × baseM dd)) n

/-! ## 2. The section and the projection, as maps of spaces -/

/-- The section of `cc-lix-odd`, as a morphism of spaces.  Their `lixSectionTotal`. -/
def lixS (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) :
    lixN dd ⟶ lixTotalPair hGc hGu :=
  cmap (lixSectionTotal hGc hGu hGe)

/-- The bundle projection, as a morphism of spaces. -/
def lixPi (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    lixTotalPair hGc hGu ⟶ lixN dd :=
  cmap (Bundle.totalPi (lixBundle G hGc hGu))

/-- The projection of the section at `x` is `x`, on the nose. -/
theorem lixS_comp_lixPi (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) :
    lixS hGc hGu hGe ≫ lixPi hGc hGu = 𝟙 (lixN dd) := rfl

/-! ## 3. The bundle pair -/

/-- `HE`: the absolute cohomology of the total space. -/
abbrev lixHE (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) (n : ℕ) :
    ModuleCat.{0} (ZMod 2) :=
  cohomologyZMod2 (lixTotalPair hGc hGu) n

/-- `jE`: the relative-to-absolute map of the bundle pair. -/
def lixJE (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) (n : ℕ) :
    relCohomology (ZMod 2) (lixTotalPair hGc hGu) (lixPuncturedInTotal hGc hGu) n ⟶
      lixHE hGc hGu n :=
  relToAbs (ZMod 2) (lixTotalPair hGc hGu) (lixPuncturedInTotal hGc hGu) n

/-- `sAbs`: the absolute pullback along the section. -/
def lixSAbs (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) (n : ℕ) :
    lixHE hGc hGu n ⟶ cohomologyZMod2 (lixN dd) n :=
  absPull (lixS hGc hGu hGe) n

/-- `piStar`: the absolute pullback along the bundle projection. -/
def lixPiStar (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) (n : ℕ) :
    cohomologyZMod2 (lixN dd) n ⟶ lixHE hGc hGu n :=
  absPull (lixPi hGc hGu) n

/-- `hnat`: naturality of the relative-to-absolute map along the section, which is a
map of pairs by `cc-lix-odd`'s `lixSectionTotal_mapsTo`. -/
theorem lixHnat (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) (n : ℕ) :
    lixSRel hGc hGu hGe n ≫ lixJ dd n = lixJE hGc hGu n ≫ lixSAbs hGc hGu hGe n :=
  (relToAbs_naturality (ZMod 2) (lixS hGc hGu hGe)
    (lixSectionTotal_mapsTo hGc hGu hGe) n).symm

/-- `hsection`: functoriality of the absolute pullback applied to `s ≫ π = 𝟙`. -/
theorem lixHsection (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) (n : ℕ) :
    lixPiStar hGc hGu n ≫ lixSAbs hGc hGu hGe n
      = 𝟙 (cohomologyZMod2 (lixN dd) n) := by
  rw [lixPiStar, lixSAbs, ← absPull_comp, lixS_comp_lixPi, absPull_id_eq]

end

end RelativeSupport

end GroupApproximation.CharClass
