import GroupApproximation.AlgTop.SingularCohomology
import GroupApproximation.AlgTop.FreeSubmodulePID

/-!
# The singular chain groups are free, and the cycles are a direct summand

This is the bridge between `FreeSubmodulePID.lean` (pure algebra) and the
universal coefficient theorem. It records three facts:

* the degree-`n` singular chain group is the coproduct of one copy of `R` per
  singular `n`-simplex — **by `rfl`** — hence free;
* over a principal ideal domain the image of any boundary map is therefore free,
  being a submodule of a free module (this is where the arbitrary-rank theorem of
  `FreeSubmodulePID.lean` is used: singular chains have uncountable rank, so
  Mathlib's finite-rank `Submodule.basisOfPid` does not apply);
* consequently `Cₙ ⧸ ker ∂ₙ` is projective, i.e. the cycles are a direct summand
  of the chains.

That last statement is exactly the splitting of

```text
0 → Zₙ(C) → Cₙ → Bₙ₋₁(C) → 0
```

that both halves of the universal coefficient theorem consume; combined with
`exists_extend_of_projective_quotient` it says every linear functional on the
cycles extends to the chains, which is the surjectivity of the Kronecker map.

Also recorded here is the identity `δφ = ∂ ≫ φ` (true by `rfl`), which is the
only thing relating the cochain coboundary of the vendored development to the
chain boundary.
-/

open CategoryTheory Limits AlgebraicTopology
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.AlgTop

noncomputable section

/-- The singular chain complex `C_•(X; R)` with coefficients in the ring `R`. -/
abbrev chainCx (R : Type) [CommRing R] (X : TopCat.{0}) : ChainComplex (ModuleCat.{0} R) ℕ :=
  ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj X

/-- The degree-`n` chain group is the coproduct of one copy of `R` per singular
`n`-simplex. This holds by `rfl`, which is what makes the freeness transport
below go through. -/
theorem chainCx_X_eq_sigma (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    (chainCx R X).X n = ∐ (fun (_ : singularSimplices X n) => ModuleCat.of R R) := rfl

/-- **The singular chain groups are free.** -/
theorem free_chainCx_X (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    Module.Free R ((chainCx R X).X n) :=
  Module.Free.of_equiv
    ((ModuleCat.coprodIsoDirectSum
      (fun (_ : singularSimplices X n) => ModuleCat.of R R)).symm.toLinearEquiv)

/-- **The image of a boundary map is free.** It is a submodule of a free chain
group, and `R` is a principal ideal domain — this is the arbitrary-rank
statement, which Mathlib does not have. -/
theorem free_range_d (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : TopCat.{0}) (n m : ℕ) :
    Module.Free R (LinearMap.range ((chainCx R X).d n m).hom) :=
  haveI := free_chainCx_X R X m
  PID.free_of_submodule_of_pid _

/-- **The cycles are a direct summand of the chains**: the quotient of a chain
group by the kernel of a boundary map is projective. -/
theorem projective_quot_ker_d (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : TopCat.{0}) (n m : ℕ) :
    Module.Projective R ((chainCx R X).X n ⧸ LinearMap.ker ((chainCx R X).d n m).hom) :=
  haveI := free_range_d R X n m
  haveI : Module.Projective R (LinearMap.range ((chainCx R X).d n m).hom) :=
    Module.Projective.of_basis (Module.Free.chooseBasis R _)
  Module.Projective.of_equiv' (LinearMap.quotKerEquivRange ((chainCx R X).d n m).hom).symm

/-- **Every linear functional on the cycles extends to the chains.** This is the
surjectivity half of the universal coefficient theorem, stripped of all
homological bookkeeping. -/
theorem exists_extend_off_ker_d (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : TopCat.{0}) (n m : ℕ) {P : Type} [AddCommGroup P] [Module R P]
    (f : LinearMap.ker ((chainCx R X).d n m).hom →ₗ[R] P) :
    ∃ F : (chainCx R X).X n →ₗ[R] P,
      ∀ x : LinearMap.ker ((chainCx R X).d n m).hom, F x = f x :=
  haveI := projective_quot_ker_d R X n m
  PID.exists_extend_of_projective_quotient _ f

/-- The cochain coboundary is precomposition with the chain boundary. -/
theorem cochainCoboundary_eq_comp (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup R X n) :
    cochainCoboundary R X n φ = (chainCx R X).d (n + 1) n ≫ φ := rfl

/-- A cochain is a cocycle exactly when it annihilates the boundaries. -/
theorem isCocycle_iff (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup R X n) :
    IsCocycle R X n φ ↔ (chainCx R X).d (n + 1) n ≫ φ = 0 := by
  show cochainCoboundary R X n φ = 0 ↔ _
  rw [cochainCoboundary_eq_comp]

end

end GroupApproximation.AlgTop
