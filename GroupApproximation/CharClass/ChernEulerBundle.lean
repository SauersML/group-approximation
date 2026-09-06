import GroupApproximation.CharClass.ChernEuler
import GroupApproximation.CharClass.ProjectiveSpaceComputation
import GroupApproximation.CharClass.BundleClassify

/-!
# The mod-2 Euler class of a line bundle

Item 2 of this lane's brief.  In the projection model a line bundle on `X` is a
rank-one projection-valued map, and `cc-bundle`'s `classifyOne` observes that
such a map **is** a continuous map `X → ℂP^d`: the three equations cutting out
`STW59.cpSet d` are exactly self-adjointness, idempotence and trace one.  So the
Euler class needs no classifying-space theory at all,

```text
e(L) := f_L^* h  ∈  H^2(X; F₂),
```

with `h` the degree-2 generator of `H^*(ℂP^d;F₂)`.  That generator is now
available unconditionally, from `hasCPCohomology_CP`, and it needs no orientation
choice: over `F₂` a line has a *unique* nonzero element, so `cpGen` is canonical
and `lineGen_eq` says any two constructions of it agree.

## Main declarations

* `cpGen d hd` — the degree-2 generator, and `cpGen_ne_zero`.
* `eulerOfBundle` — `e(L)`, and `eulerOfBundle_comap`, its naturality.
* `eulerOfBundle_cpTaut` — the normalisation `e(taut) = h`, which is what makes
  the Euler class of the tautological line the generator rather than some other
  class.
* `eulerOfBundle_eq_of_homotopic` — the shape in which invariance under
  isomorphism of bundles is consumed, once `cc-bundle`'s rotation homotopy is
  reindexed into a `ℂP`-valued statement.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory
open GroupApproximation.STW59

noncomputable section

/-! ## 1. The generator -/

/-- **The degree-2 generator of `H^*(ℂP^d; F₂)`** for `d ≥ 1`.  Canonical: an
`F₂`-line has exactly one nonzero element. -/
def cpGen (d : ℕ) (hd : 1 ≤ d) : Hmod2 (CPtop d) 2 :=
  lineGen (by simpa using ((hasCPCohomology_CP d).1 1 hd).some)

theorem cpGen_ne_zero (d : ℕ) (hd : 1 ≤ d) : cpGen d hd ≠ 0 :=
  lineGen_ne_zero _

/-- Any nonzero class of `H^2(ℂP^d;F₂)` is the generator. -/
theorem eq_cpGen_of_ne_zero {d : ℕ} (hd : 1 ≤ d) {a : Hmod2 (CPtop d) 2} (ha : a ≠ 0) :
    a = cpGen d hd :=
  eq_lineGen_of_ne_zero _ ha

/-! ## 2. The Euler class of a line bundle -/

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- **The mod-2 Euler class** of a line bundle, presented as a rank-one
projection-valued map. -/
def eulerOfBundle {d : ℕ} (hd : 1 ≤ d) (p : Bundle X (Fin (d + 1)))
    (hp : ∀ x, (p x).trace = 1) : Hmod2 (TopCat.of X) 2 :=
  eulerClass (cpGen d hd) (cmap (Bundle.classifyOne p hp))

/-- **Naturality.**  Pulling the bundle back along `f` pulls its Euler class back
along `f`. -/
theorem eulerOfBundle_comap {d : ℕ} (hd : 1 ≤ d) (p : Bundle X (Fin (d + 1)))
    (hp : ∀ x, (p x).trace = 1) (f : C(Y, X)) :
    eulerOfBundle hd (Bundle.comap f p) (fun y => hp (f y))
      = pull (cmap f) 2 (eulerOfBundle hd p hp) := by
  show eulerClass (cpGen d hd) (cmap (Bundle.classifyOne (Bundle.comap f p) _))
    = pull (cmap f) 2 (eulerClass (cpGen d hd) (cmap (Bundle.classifyOne p hp)))
  rw [Bundle.classifyOne_comap]
  exact eulerClass_comp (cpGen d hd) (cmap f) (cmap (Bundle.classifyOne p hp))

/-- **Normalisation.**  The Euler class of the tautological line of `ℂP^d` is the
generator.  This is what pins `e` rather than leaving it defined up to the choice
of a class on the target. -/
theorem eulerOfBundle_cpTaut (d : ℕ) (hd : 1 ≤ d) :
    eulerOfBundle hd (cpTaut d) (trace_cpTaut d) = cpGen d hd := by
  show eulerClass (cpGen d hd) (cmap (Bundle.classifyOne (cpTaut d) _)) = cpGen d hd
  rw [Bundle.classifyOne_cpTaut]
  exact pull_id 2 (cpGen d hd)

/-- **Invariance, in the shape it is consumed.**  Homotopic classifying maps give
the same Euler class; `cc-bundle`'s rotation homotopy is what supplies the
hypothesis for two embeddings of the same line, after it is reindexed into a
`ℂP`-valued statement. -/
theorem eulerOfBundle_eq_of_homotopic {d : ℕ} (hd : 1 ≤ d)
    (p q : Bundle X (Fin (d + 1))) (hp : ∀ x, (p x).trace = 1)
    (hq : ∀ x, (q x).trace = 1)
    (h : (Bundle.classifyOne p hp).Homotopic (Bundle.classifyOne q hq)) :
    eulerOfBundle hd p hp = eulerOfBundle hd q hq :=
  pull_eq_of_homotopic h 2 (cpGen d hd)

/-- **A bundle whose classifying map factors through a space without `H^2` has
vanishing Euler class**; in particular a trivial line bundle, whose classifying
map is constant. -/
theorem eulerOfBundle_eq_zero_of_factors {d : ℕ} (hd : 1 ≤ d)
    (p : Bundle X (Fin (d + 1))) (hp : ∀ x, (p x).trace = 1)
    {P : TopCat.{0}} (u : TopCat.of X ⟶ P) (v : P ⟶ CPtop d)
    (hfac : cmap (Bundle.classifyOne p hp) = u ≫ v)
    (hP : ∀ a : Hmod2 P 2, a = 0) :
    eulerOfBundle hd p hp = 0 := by
  show eulerClass (cpGen d hd) (cmap (Bundle.classifyOne p hp)) = 0
  rw [eulerClass, hfac, pull_comp, hP (pull v 2 (cpGen d hd)), pull_zero]

end

end CharClass
end GroupApproximation
