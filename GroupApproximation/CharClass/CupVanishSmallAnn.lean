import GroupApproximation.CharClass.RelativeSmallChains
import GroupApproximation.CharClass.CartanCohomologous

/-!
# A cocycle killing every small chain has zero class

The small-annihilator complex is acyclic, so a cocycle that vanishes on every
simplex small for a cover is a coboundary *of a cochain that also vanishes on
small chains*, and in particular a coboundary.  That is the step that turns the
cochain-level statement of `CupVanishCochain` into a statement about classes, and
it is the only place subdivision enters — through `smallAnnComplex_acyclic`,
which is already on `origin/main`.

Stated in degree `n + 1` because that is where cycles become boundaries.  In
degree zero acyclicity says something stronger and differently shaped, and no
consumer needs it: the products this is applied to are products of degree-two
classes.

## Main declarations

* `exists_smallAnn_preimage` — vanishing homology makes a small cocycle a small
  coboundary.
* `cocycleClass_eq_zero_of_mem_smallAnn` — **the class is zero**.
-/

set_option autoImplicit false

namespace GroupApproximation.CharClass

open CategoryTheory CategoryTheory.Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

variable {X : TopCat.{0}}

/-- **Cycles are boundaries in the small-annihilator complex.**  Stated at the
submodule rather than at the complex's object, because the coercion out of a
`ModuleCat` built by `CochainComplex.of` does not reduce to the submodule on its
own and every consumer wants the underlying cochain. -/
theorem exists_smallAnn_preimage (X : TopCat.{0}) (𝒰 : OpenCoverData X) (n : ℕ)
    (w : smallAnnSubmodule (ZMod 2) X 𝒰 (n + 1))
    (hw : (smallAnnD (ZMod 2) X 𝒰 (n + 1)).hom w = 0) :
    ∃ z : smallAnnSubmodule (ZMod 2) X 𝒰 n,
      (smallAnnD (ZMod 2) X 𝒰 n).hom z = w := by
  have hprev : (ComplexShape.up ℕ).prev (n + 1) = n := by simp
  have hnext : (ComplexShape.up ℕ).next (n + 1) = n + 2 := by simp
  have hex : (smallAnnComplex (ZMod 2) X 𝒰).ExactAt (n + 1) :=
    smallAnnComplex_acyclic X 𝒰 (n + 1)
  rw [HomologicalComplex.exactAt_iff' (K := smallAnnComplex (ZMod 2) X 𝒰)
      (i := n) (j := n + 1) (k := n + 2) hprev hnext,
    ShortComplex.moduleCat_exact_iff] at hex
  have hw' : ((smallAnnComplex (ZMod 2) X 𝒰).d (n + 1) (n + 2)).hom w = 0 := by
    rw [smallAnnComplex_d]
    exact hw
  obtain ⟨z, hz⟩ := hex w hw'
  refine ⟨z, ?_⟩
  rw [← smallAnnComplex_d]
  exact hz

/-- **A cocycle vanishing on every small simplex has zero class.**  It is a
coboundary, by acyclicity of the small-annihilator complex. -/
theorem cocycleClass_eq_zero_of_mem_smallAnn (X : TopCat.{0}) (𝒰 : OpenCoverData X) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) X (n + 1))
    (hmem : φ ∈ smallAnnSubmodule (ZMod 2) X 𝒰 (n + 1))
    (hφ : cochainCoboundary (ZMod 2) X (n + 1) φ = 0) :
    cocycleClass X (n + 1) φ hφ = 0 := by
  have hd : (smallAnnD (ZMod 2) X 𝒰 (n + 1)).hom
      (⟨φ, hmem⟩ : smallAnnSubmodule (ZMod 2) X 𝒰 (n + 1)) = 0 := Subtype.ext hφ
  obtain ⟨z, hz⟩ := exists_smallAnn_preimage X 𝒰 n ⟨φ, hmem⟩ hd
  have hz' : cochainCoboundary (ZMod 2) X n (z : singularCochainGroup (ZMod 2) X n) = φ :=
    congrArg Subtype.val hz
  have hzero : cochainCoboundary (ZMod 2) X (n + 1)
      (0 : singularCochainGroup (ZMod 2) X (n + 1)) = 0 := map_zero _
  rw [cocycleClass_eq_of_add_coboundary X n φ 0 hφ hzero
    (z : singularCochainGroup (ZMod 2) X n) (by rw [zero_add, hz'])]
  exact cocycleClass_zero X (n + 1) hzero

end

end GroupApproximation.CharClass
