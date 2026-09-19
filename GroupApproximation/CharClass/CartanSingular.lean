import GroupApproximation.CharClass.SteenrodDiagonal
import GroupApproximation.CharClass.AcyclicModels
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# The mod-2 singular chain complex with `Finsupp` carriers

Everything the Cartan comparison builds — the source `W ⊗ S(X)`, the target
`S(X)^{⊗4}` — is a free module on tuples of singular simplices, and
`cc-steenrod`'s diagonal is stated on exactly such free modules
(`tensorTwo X a b = (singularSimplices X a × singularSimplices X b) →₀ ZMod 2`).
So the substrate has to be the singular chain complex *presented with `Finsupp`
carriers*, not as the categorical coproduct that Mathlib's
`singularChainComplexFunctor` uses.

The cheap way to get that, and the point of this file, is to assemble it from
two Mathlib functors:

```text
TopCat --toSSet--> SSet --(free ZMod 2 on each level)--> SimplicialObject (ModuleCat (ZMod 2))
       --alternatingFaceMapComplex--> ChainComplex (ModuleCat (ZMod 2)) ℕ
```

`ModuleCat.free R` sends a type `T` to `ModuleCat.of R (T →₀ R)` *on the nose*,
so the degree-`n` object of the result is literally the free `ZMod 2`-module on
`singularSimplices X n`, with `Finsupp.basisSingleOne` as its basis; and
`d ∘ d = 0` comes free from `AlternatingFaceMapComplex.d_squared`, which holds
for any simplicial object in a preadditive category.

**This is what makes the concrete build affordable.**  The alternative — writing
the boundary by hand as a sum over faces — would require proving `∂∂ = 0` from
the simplicial identity `δ_i δ_j = δ_j δ_i'`, a genuine pairing argument over
`Fin (n+2) × Fin (n+3)` with all the attendant `Fin.pred`/`Fin.castPred` side
conditions.  Routing through `alternatingFaceMapComplex` removes that proof
entirely, at the cost of one lemma dropping the signs.

Dropping the signs is where the mod-2 hypothesis enters: `objD` is the
*alternating* sum `∑ (-1)^i • δ i`, and over `ZMod 2` every morphism satisfies
`f + f = 0`, so `-f = f` and the alternation collapses to the plain sum of the
face maps (`singFree_d`, `singFree_d_single`).
-/

namespace GroupApproximation.CharClass

open CategoryTheory AlgebraicTopology Simplicial SimplexCategory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

/-! ## 1. Characteristic two for morphisms of `ZMod 2`-modules -/

/-- Every morphism of `ZMod 2`-modules is `2`-torsion. -/
theorem ModuleCatZMod2.hom_add_self {A B : ModuleCat.{0} (ZMod 2)} (f : A ⟶ B) :
    f + f = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_zero, LinearMap.zero_apply]
  rw [← two_smul (ZMod 2) (f.hom x), show (2 : ZMod 2) = 0 from by decide, zero_smul]

/-- Negation is trivial on morphisms of `ZMod 2`-modules. -/
theorem ModuleCatZMod2.neg_eq_self {A B : ModuleCat.{0} (ZMod 2)} (f : A ⟶ B) : -f = f :=
  neg_eq_iff_add_eq_zero.2 (ModuleCatZMod2.hom_add_self f)

/-- The alternating sign is invisible over `ZMod 2`. -/
theorem ModuleCatZMod2.neg_one_pow_zsmul {A B : ModuleCat.{0} (ZMod 2)} (i : ℕ)
    (f : A ⟶ B) : ((-1 : ℤ) ^ i) • f = f := by
  rcases Nat.even_or_odd i with h | h
  · rw [h.neg_one_pow, one_zsmul]
  · rw [h.neg_one_pow, neg_zsmul, one_zsmul, ModuleCatZMod2.neg_eq_self]

/-! ## 2. The functor -/

/-- The singular simplicial set of a space, with free `ZMod 2`-coefficients
taken levelwise. -/
def singFreeSimplicial : TopCat.{0} ⥤ SimplicialObject (ModuleCat.{0} (ZMod 2)) :=
  TopCat.toSSet.{0} ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free (ZMod 2))

/-- **The mod-2 singular chain complex, with `Finsupp` carriers.** -/
def singFree : TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ :=
  singFreeSimplicial ⋙ alternatingFaceMapComplex (ModuleCat.{0} (ZMod 2))

/-- Degreewise, the chain complex is the free `ZMod 2`-module on the singular
simplices — on the nose, not up to isomorphism. -/
theorem singFree_obj_X (X : TopCat.{0}) (n : ℕ) :
    (singFree.obj X).X n = ModuleCat.of (ZMod 2) (singularSimplices X n →₀ ZMod 2) :=
  rfl

/-- The degreewise basis: the singular simplices themselves. -/
def singFreeBasis (X : TopCat.{0}) (n : ℕ) :
    Module.Basis (singularSimplices X n) (ZMod 2) ((singFree.obj X).X n) :=
  Finsupp.basisSingleOne

theorem singFreeBasis_apply (X : TopCat.{0}) (n : ℕ) (σ : singularSimplices X n) :
    singFreeBasis X n σ = Finsupp.single σ 1 :=
  congrFun (Finsupp.coe_basisSingleOne (ι := singularSimplices X n) (R := ZMod 2)) σ

/-! ## 3. The differential is the unsigned face sum

The face maps are introduced here **typed at the chain complex's own objects**
rather than as `(singFreeSimplicial.obj X).δ i`.  The two are definitionally
equal, but `(singFree.obj X).X (n+1)` and `singFreeSimplicial.obj X _⦋n+1⦌` are
defeq only after unfolding `alternatingFaceMapComplex` and `ChainComplex.of`,
which `rw`'s type-correctness check does not do; a rewrite producing a sum of
`δ i`s therefore leaves a goal that `rw` refuses to touch again.  Naming the
face maps at the right type removes that friction once and for all. -/

/-- The `i`-th face morphism of the mod-2 singular chain complex. -/
def singFace (X : TopCat.{0}) (n : ℕ) (i : Fin (n + 2)) :
    (singFree.obj X).X (n + 1) ⟶ (singFree.obj X).X n :=
  ModuleCat.ofHom (Finsupp.lmapDomain (ZMod 2) (ZMod 2) (faceSimplex X n i))

theorem singFace_single (X : TopCat.{0}) (n : ℕ) (i : Fin (n + 2))
    (σ : singularSimplices X (n + 1)) :
    (singFace X n i).hom (Finsupp.single σ 1)
      = Finsupp.single (faceSimplex X n i σ) 1 := by
  show (Finsupp.lmapDomain (ZMod 2) (ZMod 2) (faceSimplex X n i)) (Finsupp.single σ 1)
      = Finsupp.single (faceSimplex X n i σ) 1
  rw [Finsupp.lmapDomain_apply]
  exact Finsupp.mapDomain_single

/-- **The differential of `singFree`, with the signs gone.**  Over `ZMod 2` the
alternating sum of the face maps is the plain sum. -/
theorem singFree_d (X : TopCat.{0}) (n : ℕ) :
    (singFree.obj X).d (n + 1) n = ∑ i : Fin (n + 2), singFace X n i := by
  have h : (singFree.obj X).d (n + 1) n
      = ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • singFace X n i :=
    alternatingFaceMapComplex_obj_d (singFreeSimplicial.obj X) n
  rw [h]
  exact Finset.sum_congr rfl fun i _ => ModuleCatZMod2.neg_one_pow_zsmul _ _

/-- The differential on a basis element: the sum of the faces, unsigned. -/
theorem singFree_d_single (X : TopCat.{0}) (n : ℕ) (σ : singularSimplices X (n + 1)) :
    ((singFree.obj X).d (n + 1) n).hom (Finsupp.single σ 1)
      = ∑ i : Fin (n + 2), Finsupp.single (faceSimplex X n i σ) 1 := by
  rw [singFree_d, ModuleCat.hom_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ => singFace_single X n i σ

/-! ## 4. Functoriality on simplices -/

/-- The map induced on chains by a continuous map, on a basis element: pushing a
simplex forward.  `pushSimplex` is `cc-steenrod`'s name for the same operation,
so the two files agree without a translation lemma. -/
theorem singFree_map_single {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (σ : singularSimplices X n) :
    ((singFree.map f).f n).hom (Finsupp.single σ 1)
      = Finsupp.single (pushSimplex f n σ) 1 := by
  show (Finsupp.lmapDomain (ZMod 2) (ZMod 2)
      ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk n))))
        (Finsupp.single σ 1) = Finsupp.single (pushSimplex f n σ) 1
  rw [Finsupp.lmapDomain_apply]
  exact Finsupp.mapDomain_single

end

end GroupApproximation.CharClass
