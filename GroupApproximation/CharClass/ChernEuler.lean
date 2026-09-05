import GroupApproximation.CharClass.ProjectiveSpaceRing
import GroupApproximation.CharClass.ProjectiveSpaceCover

/-!
# The mod-2 Euler class of a line bundle

In the projection model a line bundle on `X` is a rank-one projection-valued map
`p : X → Matrix (Fin K) (Fin K) ℂ`, which *is* a continuous map
`f_L : X → ℂP^{K-1}` into the model `CP (K-1)` of
`Analysis/LIXProjectiveSpaceModel.lean`.  Its mod-2 Euler class is the pullback
of the degree-2 generator:

```text
e(L) := f_L^* h  ∈  H^2(X; F₂).
```

Because `H^2(ℂP^{K-1}; F₂)` is one-dimensional over `F₂`, its nonzero element is
*unique*, so `h` needs no orientation choice — `lineGen` produces it and
`lineGen_eq` says any two constructions of it agree.  That is the whole reason
the mod-2 theory is cheaper than the integral one here.

What this file proves is everything about `e` that is formal: naturality, that a
bundle whose classifying map factors through a space with no `H^2` has `e = 0`
(in particular a trivial bundle, whose classifying map is constant), and that the
generator is stable along an inclusion `ℂP^d ⊆ ℂP^{d+1}` inducing an isomorphism
on `H^2`.

Invariance under isomorphism of bundles is *not* formal: it is the statement that
two embeddings of the same line differ by a rotation, whose classifying maps are
therefore homotopic.  The rotation homotopy is lane `cc-bundle`'s and homotopy
invariance of `pull` is lane `cc-cohom-api`'s; `eulerClass_congr_of_pull_eq`
below is the shape in which this file consumes them.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory

/-- **The mod-2 Euler class** of the line bundle classified by `f`, relative to a
chosen degree-2 class `hgen` on the target projective space. -/
def eulerClass {X : TopCat.{0}} {d : ℕ} (hgen : Hmod2 (CPtop d) 2) (f : X ⟶ CPtop d) :
    Hmod2 X 2 :=
  pull f 2 hgen

/-- **Naturality.**  Pulling a line bundle back along `g` pulls its Euler class
back along `g`. -/
theorem eulerClass_comp {X Y : TopCat.{0}} {d : ℕ} (hgen : Hmod2 (CPtop d) 2)
    (g : X ⟶ Y) (f : Y ⟶ CPtop d) :
    eulerClass hgen (g ≫ f) = pull g 2 (eulerClass hgen f) :=
  pull_comp g f 2 hgen

/-- **Vanishing.**  If the classifying map factors through a space with no second
cohomology — a point, for the trivial bundle — the Euler class vanishes. -/
theorem eulerClass_eq_zero_of_factors {X P : TopCat.{0}} {d : ℕ} (hgen : Hmod2 (CPtop d) 2)
    (u : X ⟶ P) (v : P ⟶ CPtop d) (hP : ∀ a : Hmod2 P 2, a = 0) :
    eulerClass hgen (u ≫ v) = 0 := by
  rw [eulerClass, pull_comp, hP (pull v 2 hgen), pull_zero]

/-- **Invariance under a change of classifying map.**  This is the shape in which
the isomorphism-invariance of `e` is consumed: `cc-bundle` supplies a homotopy
between the classifying maps of two embeddings of the same line, and
`cc-cohom-api` turns that into equality of the pullbacks. -/
theorem eulerClass_congr_of_pull_eq {X : TopCat.{0}} {d : ℕ} (hgen : Hmod2 (CPtop d) 2)
    {f f' : X ⟶ CPtop d} (h : pull f 2 hgen = pull f' 2 hgen) :
    eulerClass hgen f = eulerClass hgen f' := h

/-- **Stability of the generator.**  A map inducing an injection on `H^2` between
two lines carries the generator to the generator.  With `j` the hyperplane
inclusion `ℂP^d ⊆ ℂP^{d+1}` — for which restriction is an isomorphism on `H^2`
as soon as `d ≥ 1` — this is the compatibility of `h_d` with `h_{d+1}`. -/
theorem pull_lineGen {X Y : TopCat.{0}} (j : X ⟶ Y)
    (eX : Hmod2 X 2 ≃ₗ[ZMod 2] ZMod 2) (eY : Hmod2 Y 2 ≃ₗ[ZMod 2] ZMod 2)
    (hinj : Function.Injective (pull j 2)) :
    pull j 2 (lineGen eY) = lineGen eX := by
  refine eq_lineGen_of_ne_zero eX ?_
  intro hzero
  exact lineGen_ne_zero eY (hinj (by rw [hzero, pull_zero]))

/-- The Euler class of the tautological line on `ℂP^d` itself: the generator. -/
theorem eulerClass_id {d : ℕ} (hgen : Hmod2 (CPtop d) 2) :
    eulerClass hgen (𝟙 (CPtop d)) = hgen :=
  pull_id 2 hgen

end CharClass
end GroupApproximation
