import GroupApproximation.CharClass.RelHomotopyPrism
import GroupApproximation.CharClass.RelativeProdContractible
import GroupApproximation.Meta.AxiomGuard

/-!
# Relative homotopy invariance of singular cohomology, over any commutative ring

Lane `sp-relhomotopy`.  Two maps of pairs `(X, A) → (Y, B)` joined by a homotopy
that carries `I × A` into `B` induce the **same** pullback on relative cohomology,
with coefficients in an arbitrary commutative ring and in every degree:

```text
relPullback R f hf n = relPullback R g hg n
```

This is the coefficient-generic replacement for `CharClass/RelativeLineHomotopy.lean`,
whose `eq_of_injective_of_line` is a `decide` over `ZMod 2` and whose own docstring
says the mod-2 coefficients are load-bearing.  Nothing here is `ZMod 2`-specific,
nothing here needs the source pair's relative group to be a line, and nothing here
needs the degree to be positive.  **`RelativeLineHomotopy.lean` is deliberately not
imported.**

## The argument

The relative cochain complex `relCochainComplex R X A` is the *annihilator*
subcomplex of `C^*(X; R)` — the cochains vanishing on every simplex subordinate to
`A` — not a quotient.  So the transpose of "the prism carries `A`-chains into
`B`-chains" (`RelHomotopyPrism.prismHom_mapsTo_subChain`) says exactly that the
dual prism carries relative cochains of `(Y, B)` to relative cochains of `(X, A)`,
which is `relPrism` below.

The homotopy identity is then free.  On the cochain side everything is composition
in `ModuleCat` *definitionally*: `cochainPullback f p φ = singularChainMap R f p ≫ φ`
and `cochainCoboundary R Z p φ = ∂ ≫ φ`.  So the relative `Homotopy.comm` field is
Mathlib's chain-level `Homotopy.comm` composed on the right with `φ`, and no
elementwise computation with prisms occurs anywhere in this file.

## Main results

* `RelativeSupport.relPullback_eq_of_homotopy` — the theorem.
* `RelativeSupport.relPullback_eq_of_path_param` — the form a consumer with a
  parameter space and two slices wants (this is the shape of
  `RelativeLineHomotopy.relPullback_eq_of_homotopy_of_line`, over any `R`, in every
  degree, with no line hypothesis).
* `RelativeSupport.relPullback_eq_of_contractible_param` — the same with a
  contractible parameter space, which is what `LIXHsq.lean` has.
-/

open CategoryTheory Limits AlgebraicTopology
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AffineBarycentricSubdivision

namespace GroupApproximation.CharClass

noncomputable section

variable {X Y : TopCat.{0}}

/-! ## 1. A relative cochain annihilates the subordinate chains -/

/-- A relative cochain vanishes on the whole submodule of subordinate chains, not
only on its generators. -/
theorem relCochain_apply_eq_zero_of_mem_subChain (R : Type) [CommRing R]
    {Z : TopCat.{0}} {S : Set Z} {n : ℕ} {φ : singularCochainGroup R Z n}
    (hφ : φ ∈ relCochainSubmodule R Z S n) {c : singularChainGroup R Z n}
    (hc : c ∈ subChainSubmodule R Z S n) : φ.hom c = 0 := by
  refine subChainSubmodule_induction (S := S) (p := fun x => φ.hom x = 0) ?_ ?_ ?_ ?_ hc
  · intro σ hσ
    exact hφ σ hσ
  · exact map_zero _
  · intro x y hx hy
    rw [map_add, hx, hy, add_zero]
  · intro a x hx
    rw [map_smul, hx, smul_zero]

/-! ## 2. The dual prism on cochains -/

/-- **The dual prism** on absolute cochains: precomposition with the prism
operator, `C^{q+1}(Y; R) → C^q(X; R)`. -/
def prismCochain (R : Type) [CommRing R] {f g : X ⟶ Y} (H : TopCat.Homotopy f g)
    (q : ℕ) : singularCochainGroup R Y (q + 1) →ₗ[R] singularCochainGroup R X q where
  toFun φ := prismHom R H q ≫ φ
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

theorem prismCochain_apply (R : Type) [CommRing R] {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (q : ℕ) (φ : singularCochainGroup R Y (q + 1)) :
    prismCochain R H q φ = prismHom R H q ≫ φ := rfl

/-- **The transpose of the prism lemma.**  The dual prism of a homotopy of pairs
carries relative cochains of `(Y, B)` to relative cochains of `(X, A)`. -/
theorem prismCochain_mem_relCochainSubmodule (R : Type) [CommRing R]
    {A : Set X} {B : Set Y} {f g : X ⟶ Y}
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B)
    (hg : ∀ x ∈ A, (ConcreteCategory.hom g) x ∈ B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ B)
    (q : ℕ) (φ : singularCochainGroup R Y (q + 1))
    (hφ : φ ∈ relCochainSubmodule R Y B (q + 1)) :
    prismCochain R H q φ ∈ relCochainSubmodule R X A q := by
  intro σ hσ
  have h1 : cochainEval q (prismCochain R H q φ) σ
      = φ.hom ((prismHom R H q).hom (chainGenerator R X q σ)) := by
    show (prismHom R H q ≫ φ).hom (chainGenerator R X q σ) = _
    rw [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [h1]
  exact relCochain_apply_eq_zero_of_mem_subChain R hφ
    (prismHom_mapsTo_subChain R hf hg H hH q (chainGenerator_mem_subChainSubmodule hσ))

/-- The dual prism as a map of the relative cochain groups. -/
def relPrism (R : Type) [CommRing R] {A : Set X} {B : Set Y} {f g : X ⟶ Y}
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B)
    (hg : ∀ x ∈ A, (ConcreteCategory.hom g) x ∈ B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ B) (q : ℕ) :
    ModuleCat.of R (relCochainSubmodule R Y B (q + 1)) ⟶
      ModuleCat.of R (relCochainSubmodule R X A q) :=
  ModuleCat.ofHom
    ((prismCochain R H q).restrict
      (fun φ hφ => prismCochain_mem_relCochainSubmodule R hf hg H hH q φ hφ))

/-- The `Homotopy.hom` field: the dual prism in bidegree `(j+1, j)`, zero elsewhere. -/
def relPrismHom (R : Type) [CommRing R] {A : Set X} {B : Set Y} {f g : X ⟶ Y}
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B)
    (hg : ∀ x ∈ A, (ConcreteCategory.hom g) x ∈ B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ B) (i j : ℕ) :
    (relCochainComplex R Y B).X i ⟶ (relCochainComplex R X A).X j :=
  if h : j + 1 = i then
    eqToHom (show (relCochainComplex R Y B).X i
        = ModuleCat.of R (relCochainSubmodule R Y B (j + 1)) by subst h; rfl)
      ≫ relPrism R hf hg H hH j
  else 0

theorem relPrismHom_eq (R : Type) [CommRing R] {A : Set X} {B : Set Y} {f g : X ⟶ Y}
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B)
    (hg : ∀ x ∈ A, (ConcreteCategory.hom g) x ∈ B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ B) (j : ℕ) :
    relPrismHom R hf hg H hH (j + 1) j = relPrism R hf hg H hH j := by
  unfold relPrismHom
  rw [dif_pos (rfl : j + 1 = j + 1)]
  all_goals exact Category.id_comp _

theorem relPrismHom_eq_zero (R : Type) [CommRing R] {A : Set X} {B : Set Y}
    {f g : X ⟶ Y}
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B)
    (hg : ∀ x ∈ A, (ConcreteCategory.hom g) x ∈ B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ B) (i j : ℕ)
    (h : ¬ j + 1 = i) : relPrismHom R hf hg H hH i j = 0 := by
  unfold relPrismHom
  exact dif_neg h

/-! ## 3. The homotopy identity on absolute cochains -/

/-- The dual chain homotopy identity in degree `0`. -/
theorem prism_cochain_comm_zero (R : Type) [CommRing R] {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (φ : singularCochainGroup R Y 0) :
    cochainPullback f 0 φ
      = prismCochain R H 0 (cochainCoboundary R Y 0 φ) + cochainPullback g 0 φ := by
  show singularChainMap R f 0 ≫ φ
      = prismHom R H 0 ≫ singularBoundary R Y 0 ≫ φ + singularChainMap R g 0 ≫ φ
  rw [prism_comm_zero R H]
  simp only [Preadditive.add_comp, Category.assoc]

/-- The dual chain homotopy identity in positive degree. -/
theorem prism_cochain_comm_succ (R : Type) [CommRing R] {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (n : ℕ) (φ : singularCochainGroup R Y (n + 1)) :
    cochainPullback f (n + 1) φ
      = prismCochain R H (n + 1) (cochainCoboundary R Y (n + 1) φ)
        + cochainCoboundary R X n (prismCochain R H n φ)
        + cochainPullback g (n + 1) φ := by
  show singularChainMap R f (n + 1) ≫ φ
      = prismHom R H (n + 1) ≫ singularBoundary R Y (n + 1) ≫ φ
        + singularBoundary R X n ≫ prismHom R H n ≫ φ
        + singularChainMap R g (n + 1) ≫ φ
  rw [prism_comm_succ R H n]
  simp only [Preadditive.add_comp, Category.assoc]
  all_goals abel

/-! ## 4. The chain homotopy of relative cochain complexes -/

/-- **The chain homotopy between the two relative cochain maps.** -/
def relHomotopy (R : Type) [CommRing R] {A : Set X} {B : Set Y} {f g : X ⟶ Y}
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B)
    (hg : ∀ x ∈ A, (ConcreteCategory.hom g) x ∈ B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ B) :
    Homotopy (relCochainMap R f hf) (relCochainMap R g hg) where
  hom := relPrismHom R hf hg H hH
  zero i j h := relPrismHom_eq_zero R hf hg H hH i j h
  comm n := by
    cases n with
    | zero =>
      rw [dNext_eq _ (show (ComplexShape.up ℕ).Rel 0 (0 + 1) from rfl),
        prevD_eq_zero _ 0 (by simp), add_zero, relPrismHom_eq, relCochainComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      exact Subtype.ext (prism_cochain_comm_zero R H _)
    | succ n =>
      rw [dNext_eq _ (show (ComplexShape.up ℕ).Rel (n + 1) (n + 1 + 1) from rfl),
        prevD_eq _ (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl),
        relPrismHom_eq, relPrismHom_eq, relCochainComplex_d, relCochainComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      exact Subtype.ext (prism_cochain_comm_succ R H n _)

namespace RelativeSupport

/-! ## 5. The theorem -/

/-- **Relative homotopy invariance of singular cohomology, over an arbitrary
commutative ring.**  If `f` and `g` are maps of pairs `(X, A) → (Y, B)` and `H` is
a homotopy from `f` to `g` carrying `I × A` into `B`, then `f` and `g` induce the
same pullback on relative cohomology, in every degree. -/
theorem relPullback_eq_of_homotopy (R : Type) [CommRing R] {X Y : TopCat.{0}}
    {A : Set X} {B : Set Y} {f g : X ⟶ Y}
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B)
    (hg : ∀ x ∈ A, (ConcreteCategory.hom g) x ∈ B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ B) (n : ℕ) :
    relPullback R f hf n = relPullback R g hg n :=
  (relHomotopy R hf hg H hH).homologyMap_eq n

/-! ## 6. The parameter-space form -/

variable {P : Type} [TopologicalSpace P]

/-- **A homotopy through maps of pairs may be cut at either end**, with the homotopy
presented as a single map out of `P × X` and the two ends as two slices joined by a
path in `P`.  This is the interface of
`RelativeLineHomotopy.relPullback_eq_of_homotopy_of_line`, but over an arbitrary
commutative ring, in every degree, and with no hypothesis on the relative group. -/
theorem relPullback_eq_of_path_param (R : Type) [CommRing R]
    {E : Type} [TopologicalSpace E] {A : Set E} {Y : TopCat.{0}} {S : Set Y}
    {b b' : P} (γ : Path b b') (Hm : TopCat.of (P × E) ⟶ Y)
    (hHm : ∀ q ∈ {q : P × E | q.2 ∈ A}, (ConcreteCategory.hom Hm) q ∈ S)
    {f g : TopCat.of E ⟶ Y}
    (hbf : sliceMap b E ≫ Hm = f) (hbg : sliceMap b' E ≫ Hm = g)
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ S)
    (hg : ∀ x ∈ A, (ConcreteCategory.hom g) x ∈ S) (n : ℕ) :
    relPullback R f hf n = relPullback R g hg n := by
  refine relPullback_eq_of_homotopy R hf hg
    { toFun := fun p => (ConcreteCategory.hom Hm) (γ p.1, p.2)
      continuous_toFun := by
        exact (ConcreteCategory.hom Hm).continuous.comp
          ((γ.continuous.comp continuous_fst).prodMk continuous_snd)
      map_zero_left := fun x => by
        have hs : (ConcreteCategory.hom (sliceMap b E ≫ Hm)) x
            = (ConcreteCategory.hom Hm) (b, x) := rfl
        exact (congrArg (fun p : P => (ConcreteCategory.hom Hm) (p, x)) γ.source).trans
          (hs.symm.trans (congrArg (fun m : TopCat.of E ⟶ Y => (ConcreteCategory.hom m) x) hbf))
      map_one_left := fun x => by
        have hs : (ConcreteCategory.hom (sliceMap b' E ≫ Hm)) x
            = (ConcreteCategory.hom Hm) (b', x) := rfl
        exact (congrArg (fun p : P => (ConcreteCategory.hom Hm) (p, x)) γ.target).trans
          (hs.symm.trans (congrArg (fun m : TopCat.of E ⟶ Y => (ConcreteCategory.hom m) x) hbg)) } ?_ n
  intro t x hx
  exact hHm (γ t, x) hx

/-- The same with a contractible parameter space, which is the hypothesis the
`LIX` consumers have. -/
theorem relPullback_eq_of_contractible_param (R : Type) [CommRing R]
    {E : Type} [TopologicalSpace E] {A : Set E} {Y : TopCat.{0}} {S : Set Y}
    (hP : ContractibleSpace P) (b b' : P) (Hm : TopCat.of (P × E) ⟶ Y)
    (hHm : ∀ q ∈ {q : P × E | q.2 ∈ A}, (ConcreteCategory.hom Hm) q ∈ S)
    {f g : TopCat.of E ⟶ Y}
    (hbf : sliceMap b E ≫ Hm = f) (hbg : sliceMap b' E ≫ Hm = g)
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ S)
    (hg : ∀ x ∈ A, (ConcreteCategory.hom g) x ∈ S) (n : ℕ) :
    relPullback R f hf n = relPullback R g hg n := by
  haveI := hP
  exact relPullback_eq_of_path_param R (PathConnectedSpace.somePath b b') Hm hHm hbf hbg
    hf hg n

end RelativeSupport

end

/-! Audited on every build: `#audit_axioms` prints the closure **and fails the
build** if it leaves the classical allowlist, which `#print axioms` does not. -/

#audit_axioms RelativeSupport.relPullback_eq_of_homotopy
#audit_axioms RelativeSupport.relPullback_eq_of_contractible_param

end GroupApproximation.CharClass
