import GroupApproximation.CharClass.LIXKRelativeMV
import GroupApproximation.Meta.AxiomGuard

/-!
# Relative Mayer–Vietoris at cochain level, over any field

Lane `lix-coeff` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.3.4 and §1.5).

`CharClass/LIXKRelativeMV.lean` proves the cochain-level splitting of a relative cocycle,
`exists_relCocycle_split_of_acyclic`, over any commutative ring, with the acyclicity of the
small-annihilator complex as a hypothesis `hacyclic`; it discharges that hypothesis only at
`ZMod 2`, through `CupVanishSmallAnn.exists_smallAnn_preimage`.  The acyclicity itself is
proved over every field in `RelativeSmallChains.smallAnnComplexOf_acyclic`, so what was
missing is its element form over `K` and the instantiation.  Both are here, so the odd-`p`
Step C has the splitting at `K = ZMod p` with no hypothesis left.

The field is needed and is not an artefact of the route: the acyclicity is the dual of a
quasi-isomorphism being a quasi-isomorphism, which rests on `K` being injective over itself.

## Main results

* `exists_smallAnnOf_preimage` — a small cocycle is the coboundary of a small cochain, over `K`.
* `LIXKRelMV.exists_relCocycle_splitOf` — **the splitting over any field**.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AffineBarycentricSubdivision

namespace GroupApproximation.CharClass

noncomputable section

/-- **Cycles are boundaries in the small-annihilator complex, over any field.**  The
`ZMod 2` statement is `CupVanishSmallAnn.exists_smallAnn_preimage`; the proof is the same,
fed `smallAnnComplexOf_acyclic`. -/
theorem exists_smallAnnOf_preimage (K : Type) [Field K] (X : TopCat.{0})
    (𝒰 : OpenCoverData X) (n : ℕ)
    (w : smallAnnSubmodule K X 𝒰 (n + 1))
    (hw : (smallAnnD K X 𝒰 (n + 1)).hom w = 0) :
    ∃ z : smallAnnSubmodule K X 𝒰 n, (smallAnnD K X 𝒰 n).hom z = w := by
  have hprev : (ComplexShape.up ℕ).prev (n + 1) = n := by simp
  have hnext : (ComplexShape.up ℕ).next (n + 1) = n + 2 := by simp
  have hex : (smallAnnComplex K X 𝒰).ExactAt (n + 1) :=
    smallAnnComplexOf_acyclic K X 𝒰 (n + 1)
  rw [HomologicalComplex.exactAt_iff' (K := smallAnnComplex K X 𝒰)
      (i := n) (j := n + 1) (k := n + 2) hprev hnext,
    ShortComplex.moduleCat_exact_iff] at hex
  have hw' : ((smallAnnComplex K X 𝒰).d (n + 1) (n + 2)).hom w = 0 := by
    rw [smallAnnComplex_d]
    exact hw
  obtain ⟨z, hz⟩ := hex w hw'
  refine ⟨z, ?_⟩
  rw [← smallAnnComplex_d]
  exact hz

namespace LIXKRelMV

/-- **Relative Mayer–Vietoris, cochain level, over any field.**  For opens `U, V` covering
`X`, a relative cocycle of `(X, U ∩ V)` with coefficients in `K` is the sum of a relative
cocycle of `(X, U)` and one of `(X, V)`.  The acyclicity input of
`exists_relCocycle_split_of_acyclic` is discharged by `exists_smallAnnOf_preimage`. -/
theorem exists_relCocycle_splitOf (K : Type) [Field K] {X : TopCat.{0}}
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    {φ : singularCochainGroup K X n}
    (hφ : φ ∈ relCochainSubmodule K X ((U : Set X) ∩ (V : Set X)) n)
    (hδ : cochainCoboundary K X n φ = 0) :
    ∃ α β : singularCochainGroup K X n,
      α ∈ relCochainSubmodule K X (U : Set X) n ∧
        β ∈ relCochainSubmodule K X (V : Set X) n ∧
        cochainCoboundary K X n α = 0 ∧
        cochainCoboundary K X n β = 0 ∧
        α + β = φ :=
  exists_relCocycle_split_of_acyclic U V hUV n
    (fun w hw => exists_smallAnnOf_preimage K X (twoSetCover U V hUV) n w hw) hφ hδ

end LIXKRelMV

end

/-! Audited on every build. -/

#audit_axioms exists_smallAnnOf_preimage
#audit_axioms LIXKRelMV.exists_relCocycle_splitOf

end GroupApproximation.CharClass
