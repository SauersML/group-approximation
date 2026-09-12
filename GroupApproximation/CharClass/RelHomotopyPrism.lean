import GroupApproximation.CharClass.RelativeFunctorial

/-!
# The prism operator of a homotopy of pairs carries `A`-chains to `B`-chains

Lane `sp-relhomotopy`.  This file is the chain-level half of relative homotopy
invariance of singular cohomology **over an arbitrary commutative ring**; the
cochain-level half and the theorem itself are in `RelHomotopyInvariance.lean`.

Mathlib supplies the prism itself: for `H : TopCat.Homotopy f g` and any object `M`
of a preadditive category with coproducts,
`TopCat.Homotopy.singularChainComplexFunctorObjMap H M` is a genuine chain homotopy
between the induced maps of singular chain complexes, generic in `M`.  What it does
*not* supply is naturality of that chain homotopy in the space, and that is the one
piece of real work here.

The route avoids every computation with prism decompositions.  Writing
`i : A ↪ X` and `j : B ↪ Y` for the two subspace inclusions and `H_A` for the
corestriction of `H` to a homotopy of maps `A → B`:

1. `homotopyCorestrict` builds `H_A` (elementary).
2. `sInclusion_whiskerRight_h` : `i ▷ I ≫ H.h = H_A.h ≫ j` in `TopCat`, which is
   `rfl` after `ext` once one remembers that `TopCat.Homotopy.h` **swaps** its two
   coordinates (`h_hom_apply : F.h p = F (I.homeomorph p.2, p.1)`).
3. `toSSet_h_naturality` transports that square through `TopCat.Homotopy.toSSet`,
   whose `h` field is `_ ◁ toSSetObjI ≫ μ TopCat.toSSet _ _ ≫ TopCat.toSSet.map H.h`.
   The transport is `whisker_exchange` followed by
   `Functor.LaxMonoidal.μ_natural_left` and functoriality — no elementwise
   description of the lax monoidal structure map is needed anywhere.
4. `toSimplicialObjectHomotopy_h_naturality` descends the square to the
   combinatorial homotopy, using `SSet.yonedaEquiv_symm_comp`.
5. `toChainHomotopy_hom_naturality` sums it with signs:
   `ToChainHomotopy.hom H p (p+1) = -∑ k, (-1)^k • H.h k` is `@[simp]`, so the
   square passes termwise.  The coefficient functor is never required to be
   additive: the map is pushed *inside* the sum, never through it.
6. `prismHom_mapsTo_subChain` is then the statement we want, by
   `subChainSubmodule_induction`: a subordinate generator is a pushforward
   (`exists_pushSimplex_of_subordinate`), the square moves the prism past the
   pushforward, and `singularChainMap_sInclusion_mem` lands the result.

## Main definitions

* `homotopyCorestrict hf hg H hH` — the corestricted homotopy `A × I → B`.
* `prismHom R H p : C_p(X; R) ⟶ C_{p+1}(Y; R)` — the degree-`p` component of
  Mathlib's chain homotopy at coefficients `R`.

## Main results

* `prismHom_naturality` — the naturality square, the only new mathematics.
* `prismHom_mapsTo_subChain` — the prism carries `A`-chains to `B`-chains.
* `prism_comm_zero`, `prism_comm_succ` — the chain homotopy identity, with
  `dNext`/`prevD` already resolved.
-/

open CategoryTheory Limits AlgebraicTopology MonoidalCategory Simplicial Opposite
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AffineBarycentricSubdivision

namespace GroupApproximation.CharClass

noncomputable section

variable {X Y : TopCat.{0}}

/-! ## 1. The corestricted homotopy -/

/-- **The corestriction of a homotopy of maps of pairs.**  If `H` is a homotopy from
`f` to `g` carrying `I × A` into `B`, then it restricts to a homotopy between the
restrictions `f|_A, g|_A : A → B`. -/
def homotopyCorestrict {A : Set X} {B : Set Y} {f g : X ⟶ Y}
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B)
    (hg : ∀ x ∈ A, (ConcreteCategory.hom g) x ∈ B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ B) :
    TopCat.Homotopy (restrictPairMap f hf) (restrictPairMap g hg) where
  toFun p := ⟨H (p.1, p.2.1), hH p.1 p.2.1 p.2.2⟩
  continuous_toFun :=
    Continuous.subtype_mk
      ((map_continuous H).comp (continuous_id.prodMap continuous_subtype_val)) _
  map_zero_left a := Subtype.ext (H.map_zero_left a.1)
  map_one_left a := Subtype.ext (H.map_one_left a.1)

/-- **The `TopCat`-level naturality square.**  The inclusion of the subspace
intertwines the two homotopies, as morphisms out of the cylinder.  This is `rfl`
after `ext`; the only thing to get right is that `TopCat.Homotopy.h` swaps its
coordinates relative to the homotopy's application. -/
theorem sInclusion_whiskerRight_h {A : Set X} {B : Set Y} {f g : X ⟶ Y}
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B)
    (hg : ∀ x ∈ A, (ConcreteCategory.hom g) x ∈ B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ B) :
    sInclusion A ▷ TopCat.I ≫ TopCat.Homotopy.h H
      = TopCat.Homotopy.h (homotopyCorestrict hf hg H hH) ≫ sInclusion B := by
  ext p
  rfl

/-! ## 2. Naturality through the singular simplicial set -/

/-- The `h` field of `TopCat.Homotopy.toSSet`, spelled out. -/
theorem topCat_homotopy_toSSet_h {f g : X ⟶ Y} (H : TopCat.Homotopy f g) :
    (TopCat.Homotopy.toSSet H).h
      = TopCat.toSSet.obj X ◁ SSet.stdSimplex.toSSetObjI
          ≫ Functor.LaxMonoidal.μ TopCat.toSSet X TopCat.I
          ≫ TopCat.toSSet.map (TopCat.Homotopy.h H) := rfl

/-- **Naturality of `TopCat.Homotopy.toSSet`.**  This is the step the design note
flagged as the risk; at the Mathlib pin it is `whisker_exchange` followed by
`Functor.LaxMonoidal.μ_natural_left`, with no elementwise description of `μ`. -/
theorem toSSet_h_naturality {A : Set X} {B : Set Y} {f g : X ⟶ Y}
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B)
    (hg : ∀ x ∈ A, (ConcreteCategory.hom g) x ∈ B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ B) :
    TopCat.toSSet.map (sInclusion A) ▷ Δ[1]
        ≫ (TopCat.Homotopy.toSSet H).h
      = (TopCat.Homotopy.toSSet (homotopyCorestrict hf hg H hH)).h
          ≫ TopCat.toSSet.map (sInclusion B) := by
  rw [topCat_homotopy_toSSet_h, topCat_homotopy_toSSet_h, ← Category.assoc,
    ← whisker_exchange]
  simp only [Category.assoc]
  rw [Functor.LaxMonoidal.μ_natural_left_assoc, ← Functor.map_comp,
    sInclusion_whiskerRight_h hf hg H hH, Functor.map_comp]

/-- The structure map of `SSet.Homotopy.toSimplicialObjectHomotopy`, applied to a
simplex.  A `rfl` lemma, and the reason it is stated: it keeps the morphism
`yonedaEquiv.symm y ▷ Δ[1] ≫ H.h` **intact**, whereas `dsimp` distributes `.app`
over `▷` and `≫` and then no monoidal rewrite matches. -/
theorem toSimplicialObjectHomotopy_h_apply {S T : SSet.{0}} {f g : S ⟶ T}
    (H : SSet.Homotopy f g) {n : ℕ} (i : Fin (n + 1)) (y : S _⦋n⦌) :
    ((SSet.Homotopy.toSimplicialObjectHomotopy H).h i) y
      = ((SSet.yonedaEquiv.symm y ▷ Δ[1] ≫ H.h).app (op ⦋n + 1⦌))
          (SSet.prodStdSimplex.nonDegenerateEquiv₁ i).1 := rfl

/-- **Naturality of the combinatorial homotopy attached to a simplicial homotopy.**
Stated for arbitrary simplicial sets: a square of `SSet.Homotopy`s gives a square
of the structure maps of the induced `SimplicialObject.Homotopy`s. -/
theorem toSimplicialObjectHomotopy_h_naturality {S T S' T' : SSet.{0}}
    {f g : S ⟶ T} {f' g' : S' ⟶ T'}
    (Hs : SSet.Homotopy f g) (Ht : SSet.Homotopy f' g') (u : S ⟶ S') (v : T ⟶ T')
    (hu : u ▷ Δ[1] ≫ Ht.h = Hs.h ≫ v)
    (n : ℕ) (i : Fin (n + 1)) :
    u.app (op ⦋n⦌) ≫ (SSet.Homotopy.toSimplicialObjectHomotopy Ht).h i
      = (SSet.Homotopy.toSimplicialObjectHomotopy Hs).h i ≫ v.app (op ⦋n + 1⦌) := by
  ext x
  show ((SSet.Homotopy.toSimplicialObjectHomotopy Ht).h i) ((u.app (op ⦋n⦌)) x)
      = (v.app (op ⦋n + 1⦌)) (((SSet.Homotopy.toSimplicialObjectHomotopy Hs).h i) x)
  rw [toSimplicialObjectHomotopy_h_apply, toSimplicialObjectHomotopy_h_apply,
    ← SSet.yonedaEquiv_symm_comp, comp_whiskerRight, Category.assoc, hu,
    ← Category.assoc]
  all_goals rfl

/-- The composite of the previous two: the subspace inclusion intertwines the
combinatorial homotopies of `H` and of its corestriction. -/
theorem toSSet_toSimplicialObject_h_naturality {A : Set X} {B : Set Y} {f g : X ⟶ Y}
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B)
    (hg : ∀ x ∈ A, (ConcreteCategory.hom g) x ∈ B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ B)
    (n : ℕ) (i : Fin (n + 1)) :
    (TopCat.toSSet.map (sInclusion A)).app (op ⦋n⦌)
        ≫ (SSet.Homotopy.toSimplicialObjectHomotopy (TopCat.Homotopy.toSSet H)).h i
      = (SSet.Homotopy.toSimplicialObjectHomotopy
            (TopCat.Homotopy.toSSet (homotopyCorestrict hf hg H hH))).h i
          ≫ (TopCat.toSSet.map (sInclusion B)).app (op ⦋n + 1⦌) :=
  toSimplicialObjectHomotopy_h_naturality _ _ _ _ (toSSet_h_naturality hf hg H hH) n i

/-! ## 3. Naturality of the induced chain homotopy -/

/-- **Naturality of `SimplicialObject.Homotopy.toChainHomotopy`.**  Mathlib has no
such lemma; this is it, in the only bidegree that a chain homotopy ever uses.  The
proof is `ToChainHomotopy.hom_eq` plus `Preadditive` bookkeeping; the coefficient
functor is never asked to be additive. -/
theorem toChainHomotopy_hom_naturality {C : Type*} [Category C] [Preadditive C]
    {S T S' T' : SimplicialObject C} {f g : S ⟶ T} {f' g' : S' ⟶ T'}
    (Hs : SimplicialObject.Homotopy f g) (Ht : SimplicialObject.Homotopy f' g')
    (u : S ⟶ S') (v : T ⟶ T')
    (hu : ∀ (n : ℕ) (i : Fin (n + 1)),
      u.app (op ⦋n⦌) ≫ Ht.h i = Hs.h i ≫ v.app (op ⦋n + 1⦌))
    (p : ℕ) :
    u.app (op ⦋p⦌) ≫ SimplicialObject.Homotopy.ToChainHomotopy.hom Ht p (p + 1)
      = SimplicialObject.Homotopy.ToChainHomotopy.hom Hs p (p + 1)
          ≫ v.app (op ⦋p + 1⦌) := by
  rw [SimplicialObject.Homotopy.ToChainHomotopy.hom_eq,
    SimplicialObject.Homotopy.ToChainHomotopy.hom_eq, Preadditive.comp_neg,
    Preadditive.neg_comp, Preadditive.comp_sum, Preadditive.sum_comp]
  refine congrArg Neg.neg (Finset.sum_congr rfl fun i _ => ?_)
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, hu]

/-! ## 4. The prism at coefficients `R` -/

/-- The coefficient functor `Type ⥤ ModuleCat R` through which the singular chain
complex is built (`X ↦ ∐_{x : X} R`). -/
abbrev prismCoeffFunctor (R : Type) [CommRing R] : Type ⥤ ModuleCat.{0} R :=
  (Limits.sigmaConst).obj (ModuleCat.of R R)

/-- The combinatorial homotopy of `H`, pushed to `ModuleCat R`. -/
abbrev prismSimpHom (R : Type) [CommRing R] {f g : X ⟶ Y} (H : TopCat.Homotopy f g) :
    SimplicialObject.Homotopy
      (((SimplicialObject.whiskering _ _).obj (prismCoeffFunctor R)).map
        (TopCat.toSSet.map f))
      (((SimplicialObject.whiskering _ _).obj (prismCoeffFunctor R)).map
        (TopCat.toSSet.map g)) :=
  (SSet.Homotopy.toSimplicialObjectHomotopy
    (TopCat.Homotopy.toSSet H)).whiskerRight (prismCoeffFunctor R)

/-- **The prism operator** `P : C_p(X; R) ⟶ C_{p+1}(Y; R)` of a homotopy, at
coefficients in an arbitrary commutative ring.  This is Mathlib's chain homotopy,
read in the only bidegree a chain homotopy uses. -/
def prismHom (R : Type) [CommRing R] {f g : X ⟶ Y} (H : TopCat.Homotopy f g) (p : ℕ) :
    singularChainGroup R X p ⟶ singularChainGroup R Y (p + 1) :=
  (TopCat.Homotopy.singularChainComplexFunctorObjMap H (ModuleCat.of R R)).hom p (p + 1)

theorem prismHom_eq (R : Type) [CommRing R] {f g : X ⟶ Y} (H : TopCat.Homotopy f g)
    (p : ℕ) :
    prismHom R H p
      = SimplicialObject.Homotopy.ToChainHomotopy.hom (prismSimpHom R H) p (p + 1) := rfl

theorem singularChainMap_eq_app (R : Type) [CommRing R] (u : X ⟶ Y) (p : ℕ) :
    singularChainMap R u p
      = (((SimplicialObject.whiskering _ _).obj (prismCoeffFunctor R)).map
          (TopCat.toSSet.map u)).app (op ⦋p⦌) := rfl

/-- **The naturality square for the prism.**  `C(i) ≫ P_X = P_A ≫ C(j)`: this is
the statement Mathlib does not have, and the whole point of the file. -/
theorem prismHom_naturality (R : Type) [CommRing R] {A : Set X} {B : Set Y}
    {f g : X ⟶ Y}
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B)
    (hg : ∀ x ∈ A, (ConcreteCategory.hom g) x ∈ B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ B) (p : ℕ) :
    singularChainMap R (sInclusion A) p ≫ prismHom R H p
      = prismHom R (homotopyCorestrict hf hg H hH) p
          ≫ singularChainMap R (sInclusion B) (p + 1) := by
  have hu : ∀ (n : ℕ) (i : Fin (n + 1)),
      (((SimplicialObject.whiskering _ _).obj (prismCoeffFunctor R)).map
          (TopCat.toSSet.map (sInclusion A))).app (op ⦋n⦌)
          ≫ (prismSimpHom R H).h i
        = (prismSimpHom R (homotopyCorestrict hf hg H hH)).h i
          ≫ (((SimplicialObject.whiskering _ _).obj (prismCoeffFunctor R)).map
              (TopCat.toSSet.map (sInclusion B))).app (op ⦋n + 1⦌) := by
    intro n i
    show (prismCoeffFunctor R).map ((TopCat.toSSet.map (sInclusion A)).app (op ⦋n⦌))
          ≫ (prismCoeffFunctor R).map
            ((SSet.Homotopy.toSimplicialObjectHomotopy (TopCat.Homotopy.toSSet H)).h i)
        = (prismCoeffFunctor R).map
            ((SSet.Homotopy.toSimplicialObjectHomotopy
              (TopCat.Homotopy.toSSet (homotopyCorestrict hf hg H hH))).h i)
          ≫ (prismCoeffFunctor R).map
            ((TopCat.toSSet.map (sInclusion B)).app (op ⦋n + 1⦌))
    rw [← Functor.map_comp, ← Functor.map_comp,
      toSSet_toSimplicialObject_h_naturality hf hg H hH n i]
  exact toChainHomotopy_hom_naturality
    (prismSimpHom R (homotopyCorestrict hf hg H hH)) (prismSimpHom R H) _ _ hu p

/-! ## 5. The prism carries `A`-chains into `B`-chains -/

/-- **The transported statement.**  The prism of a homotopy of pairs sends singular
chains of `X` supported in `A` to singular chains of `Y` supported in `B`. -/
theorem prismHom_mapsTo_subChain (R : Type) [CommRing R] {A : Set X} {B : Set Y}
    {f g : X ⟶ Y}
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B)
    (hg : ∀ x ∈ A, (ConcreteCategory.hom g) x ∈ B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ B) (p : ℕ)
    {c : singularChainGroup R X p} (hc : c ∈ subChainSubmodule R X A p) :
    (prismHom R H p).hom c ∈ subChainSubmodule R Y B (p + 1) := by
  refine subChainSubmodule_induction (S := A)
    (p := fun x => (prismHom R H p).hom x ∈ subChainSubmodule R Y B (p + 1))
    ?_ ?_ ?_ ?_ hc
  · intro σ hσ
    obtain ⟨τ, rfl⟩ := exists_pushSimplex_of_subordinate A p hσ
    rw [← singularChainMap_generator R (sInclusion A) p τ]
    have hnat := congrArg
      (fun t : singularChainGroup R (TopCat.of A) p ⟶ singularChainGroup R Y (p + 1) =>
        t.hom (chainGenerator R (TopCat.of A) p τ))
      (prismHom_naturality R hf hg H hH p)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
    rw [hnat]
    exact singularChainMap_sInclusion_mem B (p + 1) _
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro x y hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  · intro a x hx
    rw [map_smul]
    exact Submodule.smul_mem _ _ hx

/-! ## 6. The chain homotopy identity, with `dNext` and `prevD` resolved -/

/-- The chain homotopy identity in degree `0`.  There is no `dNext` term: the
singular chain complex has nothing below degree `0`. -/
theorem prism_comm_zero (R : Type) [CommRing R] {f g : X ⟶ Y} (H : TopCat.Homotopy f g) :
    singularChainMap R f 0
      = prismHom R H 0 ≫ singularBoundary R Y 0 + singularChainMap R g 0 := by
  have hcomm := (TopCat.Homotopy.singularChainComplexFunctorObjMap H
    (ModuleCat.of R R)).comm 0
  rw [dNext_eq_zero _ 0 (by simp),
    prevD_eq _ (show (ComplexShape.down ℕ).Rel 1 0 from rfl), zero_add] at hcomm
  exact hcomm

/-- The chain homotopy identity in positive degree. -/
theorem prism_comm_succ (R : Type) [CommRing R] {f g : X ⟶ Y} (H : TopCat.Homotopy f g)
    (n : ℕ) :
    singularChainMap R f (n + 1)
      = singularBoundary R X n ≫ prismHom R H n
          + prismHom R H (n + 1) ≫ singularBoundary R Y (n + 1)
          + singularChainMap R g (n + 1) := by
  have hcomm := (TopCat.Homotopy.singularChainComplexFunctorObjMap H
    (ModuleCat.of R R)).comm (n + 1)
  rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl),
    prevD_eq _ (show (ComplexShape.down ℕ).Rel (n + 2) (n + 1) from rfl)] at hcomm
  exact hcomm

end

end GroupApproximation.CharClass
