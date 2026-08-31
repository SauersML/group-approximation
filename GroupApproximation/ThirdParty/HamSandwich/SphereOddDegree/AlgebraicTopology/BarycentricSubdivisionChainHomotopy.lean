import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionChainMap
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionHomotopyFormula
import Mathlib

/-!
# Barycentric subdivision is chain-homotopic to the identity

This file packages the degree-wise chain-homotopy formula proved in
`BarycentricSubdivisionHomotopyFormula.lean`,

```text
∂ H(c) + H(∂ c) = c - sd(c),
```

into the project's actual chain-homotopy API: a `Homotopy` between the barycentric
subdivision chain map `barycentricSubdivisionChainMap R X` and the identity chain
map of the singular chain complex.

Mathlib's `Homotopy f g` of homological complexes carries the sign convention
`f = dNext H + prevD H + g`.  With `f = sd` and `g = 𝟙`, the degree-wise data
`dNext + prevD` evaluates to `sd - id`, while the project's formula gives
`∂H + H∂ = id - sd`.  We therefore use **`-H`** as the homotopy components.

## Main results

* `barycentricSubdivision_chainHomotopic_id`: the chain homotopy
  `Homotopy (barycentricSubdivisionChainMap R X) (𝟙 _)`.
* `barycentricSubdivision_induces_identity_on_homology` /
  `barycentricSubdivision_homologyMap_eq_id`: the induced map on homology is the
  identity.
* `barycentricSubdivision_sub_id_is_boundary`: the explicit chain-level formula
  expressing `sd(c) - c` through the homotopy operator.
-/

open scoped BigOperators
open CategoryTheory AlgebraicTopology Simplicial SimplexCategory Limits

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace AffineBarycentricSubdivision

/-- The components of the chain homotopy between barycentric subdivision and the
identity: in the slot `(p, q)` it is `-H_p` when `q = p + 1` and `0` otherwise. -/
noncomputable def barycentricSubdivisionChainHomotopyHom
    (R : Type) [CommRing R] (X : TopCat.{0}) (p q : ℕ) :
    (singularChainComplex R X).X p ⟶ (singularChainComplex R X).X q :=
  if h : p + 1 = q then
    -((barycentricSubdivisionHomotopyLinearMap R X p) ≫ eqToHom (by rw [h]))
  else 0

/-- In the relevant slot, the homotopy component is `-H_p`. -/
theorem barycentricSubdivisionChainHomotopyHom_succ
    (R : Type) [CommRing R] (X : TopCat.{0}) (p : ℕ) :
    barycentricSubdivisionChainHomotopyHom R X p (p + 1)
      = -(barycentricSubdivisionHomotopyLinearMap R X p) := by
  rw [barycentricSubdivisionChainHomotopyHom, dif_pos rfl, eqToHom_refl, Category.comp_id]

/-- Outside the relevant slot, the homotopy component vanishes. -/
theorem barycentricSubdivisionChainHomotopyHom_zero
    (R : Type) [CommRing R] (X : TopCat.{0}) (p q : ℕ) (h : p + 1 ≠ q) :
    barycentricSubdivisionChainHomotopyHom R X p q = 0 := by
  rw [barycentricSubdivisionChainHomotopyHom, dif_neg h]

/-
**The chain-homotopy identity in Mathlib's sign convention.** For every degree
`n`, the degree-`n` component of the subdivision chain map equals
`dNext + prevD` of the homotopy operator plus the identity component.  This is the
`comm` field of the `Homotopy` structure, isolated as a theorem.
-/
theorem barycentricSubdivisionChainHomotopy_comm
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    (barycentricSubdivisionChainMap R X).f n
      = dNext n (barycentricSubdivisionChainHomotopyHom R X)
        + prevD n (barycentricSubdivisionChainHomotopyHom R X)
        + HomologicalComplex.Hom.f (𝟙 (singularChainComplex R X)) n := by
  -- In this case, we have n = 0, and the goal simplifies to showing that the identity map equals itself, which is trivially true.
  by_cases hn : n = 0;
  · subst hn;
    simp +decide [ dNext, prevD, barycentricSubdivisionChainMap, barycentricSubdivisionChainHomotopyHom ];
    ext c;
    have h := barycentricSubdivisionHomotopy_boundary_formula R X 0 c; simp_all +decide [ homotopyBoundaryTerm_zero, singularBoundary ] ;
  · obtain ⟨ m, rfl ⟩ := Nat.exists_eq_succ_of_ne_zero hn;
    unfold dNext prevD;
    simp +decide [ singularChainComplex, barycentricSubdivisionChainHomotopyHom, barycentricSubdivisionChainMap ];
    ext c;
    have := barycentricSubdivisionHomotopy_boundary_formula R X ( m + 1 ) c;
    simp_all +decide [ homotopyBoundaryTerm_succ, singularBoundary ];
    grind

/-- **Barycentric subdivision is chain-homotopic to the identity.**

A `Homotopy` between the barycentric subdivision chain map and the identity chain
map of the singular chain complex, built from the homotopy operator `-H`. -/
noncomputable def barycentricSubdivision_chainHomotopic_id
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    Homotopy (barycentricSubdivisionChainMap R X) (𝟙 (singularChainComplex R X)) where
  hom := barycentricSubdivisionChainHomotopyHom R X
  zero i j hij := by
    apply barycentricSubdivisionChainHomotopyHom_zero
    rw [ComplexShape.down_Rel] at hij; omega
  comm := barycentricSubdivisionChainHomotopy_comm R X

/-- **Induced map on homology is the identity (named form).**

Since barycentric subdivision is chain-homotopic to the identity, it induces the
identity on every singular homology group. -/
theorem barycentricSubdivision_induces_identity_on_homology
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    HomologicalComplex.homologyMap (barycentricSubdivisionChainMap R X) n
      = 𝟙 ((singularChainComplex R X).homology n) := by
  rw [(barycentricSubdivision_chainHomotopic_id R X).homologyMap_eq n,
    HomologicalComplex.homologyMap_id]

/-- **Induced map on homology is the identity (alias).**  Same statement as
`barycentricSubdivision_induces_identity_on_homology`, kept under the prompt's
preferred name. -/
theorem barycentricSubdivision_homologyMap_eq_id
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    HomologicalComplex.homologyMap (barycentricSubdivisionChainMap R X) n
      = 𝟙 ((singularChainComplex R X).homology n) :=
  barycentricSubdivision_induces_identity_on_homology R X n

/-- **Chain-level boundary witness.**

The difference `sd(c) - c` is the (negative of the) chain-homotopy boundary
`∂ H(c) + H(∂ c)`.  Concretely, with the project's index convention,
```text
sd(c) - c = -(∂ H(c) + H(∂ c)),
```
where `H(∂ c)` is `homotopyBoundaryTerm R X n c`.  This is the explicit formula
needed later to show that a cycle and its subdivision represent the same homology
class. -/
theorem barycentricSubdivision_sub_id_is_boundary
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (c : singularChainGroup R X n) :
    (barycentricSubdivisionLinearMap R X n).hom c - c
      = -((singularBoundary R X n).hom
            ((barycentricSubdivisionHomotopyLinearMap R X n).hom c)
          + homotopyBoundaryTerm R X n c) := by
  rw [show (singularBoundary R X n).hom
        ((barycentricSubdivisionHomotopyLinearMap R X n).hom c)
        + homotopyBoundaryTerm R X n c
        = c - (barycentricSubdivisionLinearMap R X n).hom c from
      barycentricSubdivisionHomotopy_boundary_formula R X n c]
  abel

end AffineBarycentricSubdivision
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
