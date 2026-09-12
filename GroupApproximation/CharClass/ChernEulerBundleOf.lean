import GroupApproximation.CharClass.ChernEulerBundle
import GroupApproximation.CharClass.KroneckerSphere

/-!
# The Euler class of a line bundle with coefficients in `K`

The coefficient-generic form of `ChernEuler` and `ChernEulerBundle`.  A line bundle on `X`, in
the projection model, is a rank-one projection-valued map, and `Bundle.classifyOne` reads it as a
continuous map `X → ℂP^d`, so the Euler class is a pullback,

```text
e_K(L) := f_L^* h  ∈  H^2(X; K).
```

**The generator is data.**  Over `F₂` an `F₂`-line has exactly one nonzero element, so
`ChernEulerBundle.cpGen` is canonical.  Over a field `K` a line has `|K| − 1` nonzero elements,
and the computation `H^*(ℂP^d; K)` is not in the tree yet, so `eulerOfBundleOf K hgen` takes the
class `hgen ∈ H^2(ℂP^d; K)` as an argument.  Nothing below depends on which class it is:
naturality, the normalisation `e_K(taut) = hgen`, homotopy invariance, and the vanishing for a
classifying map that factors through a space without `H²` hold for every `hgen`.  At `F₂` with
`hgen = cpGen d hd` this is `eulerOfBundle` on the nose (`eulerOfBundle_eq_eulerOfBundleOf`).

## Main declarations

* `eulerClassOf`, `eulerClassOf_comp`.
* `eulerOfBundleOf`, `eulerOfBundle_comapOf`, `eulerOfBundle_cpTautOf`,
  `eulerOfBundle_eq_of_homotopicOf`, `eulerOfBundle_eq_zero_of_factorsOf`.
* `hasPointCohomology_of_contractibleOf` — a contractible space has the cohomology of a point,
  over any field.
* `eulerOfBundle_eq_eulerOfBundleOf` — the `F₂` bridge.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory
open GroupApproximation.STW59

noncomputable section

/-! ## 1. The Euler class of a classifying map -/

/-- **The Euler class over `K`** of the line bundle classified by `f`, relative to a chosen
degree-2 class `hgen` on the target projective space. -/
def eulerClassOf (K : Type) [CommRing K] {X : TopCat.{0}} {d : ℕ} (hgen : Hmod K (CPtop d) 2)
    (f : X ⟶ CPtop d) : Hmod K X 2 :=
  pull f 2 hgen

/-- **Naturality.** -/
theorem eulerClassOf_comp (K : Type) [CommRing K] {X Y : TopCat.{0}} {d : ℕ}
    (hgen : Hmod K (CPtop d) 2) (g : X ⟶ Y) (f : Y ⟶ CPtop d) :
    eulerClassOf K hgen (g ≫ f) = pull g 2 (eulerClassOf K hgen f) :=
  pull_comp g f 2 hgen

/-! ## 2. The Euler class of a line bundle -/

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- **The Euler class over `K`** of a line bundle, presented as a rank-one projection-valued
map, relative to a chosen class `hgen ∈ H^2(ℂP^d; K)`. -/
def eulerOfBundleOf (K : Type) [CommRing K] {d : ℕ} (hgen : Hmod K (CPtop d) 2)
    (p : Bundle X (Fin (d + 1))) (hp : ∀ x, (p x).trace = 1) : Hmod K (TopCat.of X) 2 :=
  eulerClassOf K hgen (cmap (Bundle.classifyOne p hp))

/-- **Naturality.**  Pulling the bundle back along `f` pulls its Euler class back along `f`. -/
theorem eulerOfBundle_comapOf (K : Type) [CommRing K] {d : ℕ} (hgen : Hmod K (CPtop d) 2)
    (p : Bundle X (Fin (d + 1))) (hp : ∀ x, (p x).trace = 1) (f : C(Y, X)) :
    eulerOfBundleOf K hgen (Bundle.comap f p) (fun y => hp (f y))
      = pull (cmap f) 2 (eulerOfBundleOf K hgen p hp) := by
  show eulerClassOf K hgen (cmap (Bundle.classifyOne (Bundle.comap f p) _))
    = pull (cmap f) 2 (eulerClassOf K hgen (cmap (Bundle.classifyOne p hp)))
  rw [Bundle.classifyOne_comap]
  exact eulerClassOf_comp K hgen (cmap f) (cmap (Bundle.classifyOne p hp))

/-- **Normalisation.**  The Euler class of the tautological line of `ℂP^d` is the chosen
class. -/
theorem eulerOfBundle_cpTautOf (K : Type) [CommRing K] (d : ℕ) (hgen : Hmod K (CPtop d) 2) :
    eulerOfBundleOf K hgen (cpTaut d) (trace_cpTaut d) = hgen := by
  show eulerClassOf K hgen (cmap (Bundle.classifyOne (cpTaut d) _)) = hgen
  rw [Bundle.classifyOne_cpTaut]
  exact pull_id 2 hgen

/-- **Invariance, in the shape it is consumed.**  Homotopic classifying maps give the same
Euler class. -/
theorem eulerOfBundle_eq_of_homotopicOf (K : Type) [CommRing K] {d : ℕ}
    (hgen : Hmod K (CPtop d) 2) (p q : Bundle X (Fin (d + 1))) (hp : ∀ x, (p x).trace = 1)
    (hq : ∀ x, (q x).trace = 1)
    (h : (Bundle.classifyOne p hp).Homotopic (Bundle.classifyOne q hq)) :
    eulerOfBundleOf K hgen p hp = eulerOfBundleOf K hgen q hq :=
  pull_eq_of_homotopicOf K h 2 hgen

/-- **A bundle whose classifying map factors through a space without `H²` has vanishing Euler
class**, over `K` and for every choice of `hgen`. -/
theorem eulerOfBundle_eq_zero_of_factorsOf (K : Type) [CommRing K] {d : ℕ}
    (hgen : Hmod K (CPtop d) 2) (p : Bundle X (Fin (d + 1))) (hp : ∀ x, (p x).trace = 1)
    {P : TopCat.{0}} (u : TopCat.of X ⟶ P) (v : P ⟶ CPtop d)
    (hfac : cmap (Bundle.classifyOne p hp) = u ≫ v)
    (hP : ∀ a : Hmod K P 2, a = 0) :
    eulerOfBundleOf K hgen p hp = 0 := by
  show eulerClassOf K hgen (cmap (Bundle.classifyOne p hp)) = 0
  rw [eulerClassOf, hfac, pull_comp, hP (pull v 2 hgen), pull_zero]

/-! ## 3. A contractible space has the cohomology of a point -/

/-- **A contractible space has the cohomology of a point**, over any field: `H⁰ ≅ K` and every
positive degree vanishes. -/
theorem hasPointCohomology_of_contractibleOf (K : Type) [Field K] (Z : Type) [TopologicalSpace Z]
    [ContractibleSpace Z] : HasPointCohomologyOf K (TopCat.of Z) :=
  ⟨⟨cohZeroEquivOfContractibleOf K Z⟩, fun k hk a =>
    cohomology_eq_zero_of_contractibleOf K Z k (Nat.one_le_iff_ne_zero.mpr hk) a⟩

/-! ## 4. The `F₂` bridge -/

/-- At `F₂`, with the canonical generator, this is `eulerOfBundle`. -/
theorem eulerOfBundle_eq_eulerOfBundleOf {d : ℕ} (hd : 1 ≤ d) (p : Bundle X (Fin (d + 1)))
    (hp : ∀ x, (p x).trace = 1) :
    eulerOfBundle hd p hp = eulerOfBundleOf (ZMod 2) (cpGen d hd) p hp := rfl

end

end CharClass
end GroupApproximation
