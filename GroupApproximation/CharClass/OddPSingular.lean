import GroupApproximation.CharClass.OddPSourceFunctor
import GroupApproximation.CharClass.CartanSourceBoundary
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Category.ModuleCat.Adjunctions

/-!
# The signed singular boundary, and the instance of `OddPBoundaryData`

`OddPSource.lean` builds `W ⊗ C(X)` against an **abstract** `OddPBoundaryData p`,
so the complex and its `d ∘ d = 0` could be proved before the boundary was
pinned down.  This file supplies the instance, so `oddSrc` stops being
parameterized by a hypothesis.

## Why this is cheap, and why it is *cheaper* than at `p = 2`

`CartanSingular.lean` assembles the mod-2 singular chain complex as

```text
TopCat --toSSet--> SSet --(free R levelwise)--> SimplicialObject (ModuleCat R)
       --alternatingFaceMapComplex--> ChainComplex (ModuleCat R) ℕ
```

and every step of that is generic in `R`; `ModuleCat.free R` sends a type to
`ModuleCat.of R (T →₀ R)` **on the nose**, so degree `n` is literally the free
module on the singular `n`-simplices, and `∂ ∘ ∂ = 0` comes free from
`HomologicalComplex.d_comp_d`.  The mod-2 file then spends four lemmas
(`ModuleCatZMod2.hom_add_self`, `neg_eq_self`, `neg_one_pow_zsmul`,
`singFree_d`) **discarding the alternating signs**, which is the only place its
characteristic is used.

At odd `p` we keep them.  So this file is `CartanSingular.lean` with those four
lemmas deleted rather than replaced, and the signed formula it needs,
`alternatingFaceMapComplex_obj_d`, is the very statement the mod-2 file rewrites
*away from* one line before it drops the signs.

Contrast `CartanTargetBoundary.lean`'s `bdU`, the *unsigned* boundary: it is
defined over any `[CommRing Λ]`, but its `bdU_bdU` needs `[Algebra (ZMod 2) Λ]`,
and necessarily so — `∂ ∘ ∂ = 0` is false for the unsigned face sum outside
characteristic two.  Nothing downstream of `bdU` may be carried here; see §1.2a
of this lane's report for the same lesson about `singular_d_ι`.

`simplexEquiv` is **reused** from `CartanSourceBoundary.lean`: it is the single
`Equiv.ulift` between `singularSimplices X n` and the bare hom-set, it does not
mention the coefficient ring, and this file is the only place this lane spends
it.
-/

namespace GroupApproximation.CharClass

open CategoryTheory AlgebraicTopology Simplicial SimplexCategory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

variable (R : Type) [CommRing R]

/-! ## 1. The singular chain complex over an arbitrary ring -/

/-- The singular simplicial set with free `R`-coefficients levelwise. -/
def singFreeSimplicialR : TopCat.{0} ⥤ SimplicialObject (ModuleCat.{0} R) :=
  TopCat.toSSet.{0} ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free R)

/-- **The singular chain complex over `R`, with `Finsupp` carriers and its signs
intact.**  The generic twin of `CartanSingular.singFree`, which is this at
`R = ZMod 2`. -/
def singFreeR : TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} R) ℕ :=
  singFreeSimplicialR R ⋙ alternatingFaceMapComplex (ModuleCat.{0} R)

theorem singFreeR_obj_X (X : TopCat.{0}) (n : ℕ) :
    ((singFreeR R).obj X).X n
      = ModuleCat.of R (singularSimplices X n →₀ R) :=
  rfl

/-- The `i`-th face morphism, typed at the chain complex's own objects.  Naming
it here rather than reaching for `(singFreeSimplicialR R).δ i` is what keeps
`rw` usable downstream: the two are defeq only after unfolding
`alternatingFaceMapComplex` and `ChainComplex.of`, which `rw`'s type-correctness
check does not do. -/
def singFaceR (X : TopCat.{0}) (n : ℕ) (i : Fin (n + 2)) :
    ((singFreeR R).obj X).X (n + 1) ⟶ ((singFreeR R).obj X).X n :=
  ModuleCat.ofHom (Finsupp.lmapDomain R R (faceSimplex X n i))

theorem singFaceR_single (X : TopCat.{0}) (n : ℕ) (i : Fin (n + 2))
    (σ : singularSimplices X (n + 1)) :
    (singFaceR R X n i).hom (Finsupp.single σ (1 : R))
      = Finsupp.single (faceSimplex X n i σ) (1 : R) := by
  show (Finsupp.lmapDomain R R (faceSimplex X n i)) (Finsupp.single σ (1 : R))
      = Finsupp.single (faceSimplex X n i σ) (1 : R)
  rw [Finsupp.lmapDomain_apply]
  exact Finsupp.mapDomain_single

/-- **The differential, with its signs.**  This is exactly the statement
`CartanSingular.singFree_d` rewrites away from before collapsing the signs. -/
theorem singFreeR_d (X : TopCat.{0}) (n : ℕ) :
    ((singFreeR R).obj X).d (n + 1) n
      = ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • singFaceR R X n i :=
  alternatingFaceMapComplex_obj_d ((singFreeSimplicialR R).obj X) n

theorem singFreeR_d_single (X : TopCat.{0}) (n : ℕ) (σ : singularSimplices X (n + 1)) :
    (((singFreeR R).obj X).d (n + 1) n).hom (Finsupp.single σ (1 : R))
      = ∑ i : Fin (n + 2),
          ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (faceSimplex X n i σ) (1 : R) := by
  rw [singFreeR_d, ModuleCat.hom_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (((-1 : ℤ) ^ (i : ℕ)) • singFaceR R X n i).hom (Finsupp.single σ (1 : R)) = _
  rw [ModuleCat.hom_zsmul, LinearMap.smul_apply, singFaceR_single]
  -- `rw`'s trailing `rfl` does not fire here even though both sides are
  -- syntactically identical; cc-steenrod's trap, and it costs a probe either way.
  rfl

theorem singFreeR_map_single {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (σ : singularSimplices X n) :
    (((singFreeR R).map f).f n).hom (Finsupp.single σ (1 : R))
      = Finsupp.single (pushSimplex f n σ) (1 : R) := by
  show (Finsupp.lmapDomain R R
      ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk n))))
        (Finsupp.single σ (1 : R)) = Finsupp.single (pushSimplex f n σ) (1 : R)
  rw [Finsupp.lmapDomain_apply]
  exact Finsupp.mapDomain_single

/-- The chain map induced by `f`, as a map of `Finsupp`s. -/
theorem singFreeR_map_eq {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    ((singFreeR R).map f).f n
      = ModuleCat.ofHom (Finsupp.lmapDomain R R (pushSimplex f n)) :=
  rfl

/-! ## 2. The boundary on the bare hom-set model -/

/-- The signed singular boundary transported along the single `Equiv.ulift`
between `singularSimplices X n` and the bare hom-set. -/
def bdRHom (X : TopCat.{0}) (n : ℕ) :
    ((stdSimplexTop (n + 1) ⟶ X) →₀ R) →ₗ[R] ((stdSimplexTop n ⟶ X) →₀ R) :=
  (Finsupp.lmapDomain R R (simplexEquiv X n)).comp
    ((((singFreeR R).obj X).d (n + 1) n).hom.comp
      (Finsupp.lmapDomain R R (simplexEquiv X (n + 1)).symm))

theorem bdRHom_apply (X : TopCat.{0}) (n : ℕ)
    (c : (stdSimplexTop (n + 1) ⟶ X) →₀ R) :
    bdRHom R X n c
      = Finsupp.mapDomain (simplexEquiv X n)
          ((((singFreeR R).obj X).d (n + 1) n).hom
            (Finsupp.mapDomain (simplexEquiv X (n + 1)).symm c)) := rfl

/-- **`∂ ∘ ∂ = 0`**, free from `HomologicalComplex.d_comp_d`; no hypothesis on
the characteristic anywhere. -/
theorem bdRHom_bdRHom (X : TopCat.{0}) (n : ℕ)
    (c : (stdSimplexTop (n + 2) ⟶ X) →₀ R) :
    bdRHom R X n (bdRHom R X (n + 1) c) = 0 := by
  have hid : ((simplexEquiv X (n + 1)).symm ∘ simplexEquiv X (n + 1)) = id :=
    funext fun σ => (simplexEquiv X (n + 1)).symm_apply_apply σ
  have hdd : ∀ y : (((singFreeR R).obj X).X (n + 2)),
      (((singFreeR R).obj X).d (n + 1) n).hom
        ((((singFreeR R).obj X).d (n + 2) (n + 1)).hom y) = 0 := by
    intro y
    have h' := congrArg (fun (g : (((singFreeR R).obj X).X (n + 2))
        ⟶ (((singFreeR R).obj X).X n)) => g.hom y)
      (HomologicalComplex.d_comp_d ((singFreeR R).obj X) (n + 2) (n + 1) n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] at h'
    exact h'
  rw [bdRHom_apply, bdRHom_apply, ← Finsupp.mapDomain_comp, hid, Finsupp.mapDomain_id,
    hdd]
  -- The remaining `0` is typed at the `ModuleCat` carrier, not at the `Finsupp`,
  -- so `rw [Finsupp.mapDomain_zero]` cannot match it.  Cross the junction with a
  -- term, where defeq is checked at default transparency.
  exact Finsupp.mapDomain_zero

/-- The induced chain map, as a plain `Finsupp.mapDomain`. -/
theorem singFreeR_map_apply {X Y : TopCat.{0}} (f : X ⟶ Y) (m : ℕ)
    (z : singularSimplices X m →₀ R) :
    (((singFreeR R).map f).f m).hom z = Finsupp.mapDomain (pushSimplex f m) z := by
  rw [singFreeR_map_eq]
  show (Finsupp.lmapDomain R R (pushSimplex f m)) z = _
  rw [Finsupp.lmapDomain_apply]

/-- Naturality of the signed differential, in the `mapDomain` form the transport
below consumes.  This is `HomologicalComplex.Hom.comm` read on an element; there
is no computation. -/
theorem singFreeR_d_natural {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (c : singularSimplices X (n + 1) →₀ R) :
    (((singFreeR R).obj Y).d (n + 1) n).hom
        (Finsupp.mapDomain (pushSimplex f (n + 1)) c)
      = Finsupp.mapDomain (pushSimplex f n)
          ((((singFreeR R).obj X).d (n + 1) n).hom c) := by
  have h := congrArg (fun (g : (((singFreeR R).obj X).X (n + 1))
      ⟶ (((singFreeR R).obj Y).X n)) => g.hom c) (((singFreeR R).map f).comm (n + 1) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  simp only [singFreeR_map_apply] at h
  exact h

theorem bdRHom_natural {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (c : (stdSimplexTop (n + 1) ⟶ X) →₀ R) :
    bdRHom R Y n (Finsupp.mapDomain (· ≫ f) c)
      = Finsupp.mapDomain (· ≫ f) (bdRHom R X n c) := by
  have h1 : ((simplexEquiv Y (n + 1)).symm ∘ fun φ : stdSimplexTop (n + 1) ⟶ X => φ ≫ f)
      = (pushSimplex f (n + 1)) ∘ (simplexEquiv X (n + 1)).symm := rfl
  have h2 : ((fun ψ : stdSimplexTop n ⟶ X => ψ ≫ f) ∘ simplexEquiv X n)
      = (simplexEquiv Y n) ∘ (pushSimplex f n) := rfl
  rw [bdRHom_apply, bdRHom_apply, ← Finsupp.mapDomain_comp, h1, Finsupp.mapDomain_comp,
    singFreeR_d_natural, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, h2]

/-! ## 3. The instance -/

/-- **The signed singular boundary as `OddPBoundaryData`.**  With this,
`oddSrc p (oddSingularBoundary p)` is a concrete functor. -/
def oddSingularBoundary (p : ℕ) : OddPBoundaryData p where
  bd X n := bdRHom (GroupRingZMod p) X n
  bd_natural f n c := bdRHom_natural (GroupRingZMod p) f n c
  bd_bd X n c := bdRHom_bdRHom (GroupRingZMod p) X n c

end

end GroupApproximation.CharClass
