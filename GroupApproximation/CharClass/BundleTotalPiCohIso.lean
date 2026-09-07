import GroupApproximation.CharClass.BundleHomotopy
import GroupApproximation.CharClass.CohomologyBridge

/-!
# The bundle projection is an isomorphism on cohomology

A tool for `lix-hclass`, built generically at `Bundle X ι` rather than at any
LIX-specific object, per the standing rule that a hypothesis or a helper is
stated about the property it needs and not about the structure that happens to
supply it.

## What this is

`RelativeSupport.lixPiStar` (`LIXStepCOddRelative.lean`) is already known to be
a **split mono**: `RelativeSupport.lixHsection` proves `piStar ≫ sAbs = 𝟙`, so
`piStar` is injective with an explicit left inverse.  What was still open is
**surjectivity** — upgrading that split mono to an isomorphism.

That upgrade is exactly where the zero-section deformation retraction earns its
keep, and it is already landed and generic: `Bundle.totalHomotopyEquivBase`
(`BundleHomotopy.lean:66`) is the homotopy equivalence `Total p ≃ₕ X` given by
scaling every fibre to the origin, `(x, v) ↦ (x, t·v)` — elementary in this
repo's model, since the fibre is the fixed-point set of a linear map and the
scaling stays inside it for every `t`.  Composed with `pullEquivOfHomotopyEquiv`
(`CohomologyBridge.lean:102`, homotopy invariance of `H^*`), the pullback along
the bundle projection `π = Bundle.totalPi p` is a full linear **isomorphism**
on `H^n`, not merely an injection.

`Bundle.notZeroHomotopyEquivProj` (`BundleZeroSection.lean:499`) is a different
homotopy equivalence — the *punctured* total space onto the projectivisation —
and is not a substitute for this one; the retraction here uses the ordinary
(non-projective) total space and its zero section directly.

## What this is not

**This does not close `hclass`.**  It gives `jE.hom u` a unique `π*`-preimage,
nothing more.  *Which* class that preimage is — that it is the top Chern class
`lixChern (LIX.lixDD j) (mappingTorus ...) ... (lixRank ...)`, rather than some
other element of `H^n(N; F₂)` — is the entire remaining content of `hclass`,
and identifying it is `lix-hclass`'s work, not this file's.

## Main declarations

* `totalPiCohIso` — **`π*` is a linear isomorphism on `H^n`, generically.**
* `bijective_totalPiPull` — the same fact as plain bijectivity, the form most
  consumers actually need.
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace Bundle

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

/-- **The bundle projection is a linear isomorphism on `H^n`.**  `π* = pullMap
(totalPi p) n`, via the zero-section deformation retraction
(`totalHomotopyEquivBase`) and homotopy invariance of cohomology. -/
def totalPiCohIso (p : Bundle X ι) (n : ℕ) :
    Hmod2 (TopCat.of X) n ≃ₗ[ZMod 2] Hmod2 (TopCat.of (Total p)) n :=
  pullEquivOfHomotopyEquiv (totalHomotopyEquivBase p) n

@[simp] theorem totalPiCohIso_apply (p : Bundle X ι) (n : ℕ) (a : Hmod2 (TopCat.of X) n) :
    totalPiCohIso p n a = pullMap (totalPi p) n a :=
  pullEquivOfHomotopyEquiv_apply (totalHomotopyEquivBase p) n a

/-- **`π*` is bijective.**  The form most consumers need: `piStar` (however it
is packaged — `absPull`, `pullMap`, or a bare `ModuleCat` morphism — is this
same function once unfolded to the bundle projection, so bijectivity transports
along whichever spelling a consumer already has. -/
theorem bijective_totalPiPull (p : Bundle X ι) (n : ℕ) :
    Function.Bijective (pullMap (totalPi p) n) := by
  have heq : pullMap (totalPi p) n = ⇑(totalPiCohIso p n) := by
    funext a
    exact (totalPiCohIso_apply p n a).symm
  rw [heq]
  exact (totalPiCohIso p n).bijective

end Bundle

end GroupApproximation.CharClass
