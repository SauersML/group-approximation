import GroupApproximation.AlgTop.Kronecker

/-!
# Universal coefficients: the Kronecker map is surjective

Over a principal ideal domain the Kronecker map

```text
κ : Hⁿ(X; R) → Hom(Hₙ(X; R), R)
```

is surjective. Given a functional `f` on homology, pull it back to the cycles,
extend it over the chains — possible because the cycles are a direct summand,
which is `exists_extend_off_ker_d`, which in turn rests on the arbitrary-rank
statement "a submodule of a free module over a PID is free" that Mathlib lacks —
and observe that the extension is automatically a cocycle, because a boundary is
a cycle whose homology class is zero.

This is the half of the universal coefficient theorem that **constructs** classes,
and it is the half the counterexample programme needs: it produces a class in
`Hⁿ(Sⁿ; ℤ)` pairing to `1` against the generator of `Hₙ(Sⁿ; ℤ)`, hence a
generator and a normalised top-degree pairing.

The other half — injectivity when `Hₙ₋₁(X; R)` is projective, which upgrades this
to an isomorphism — uses the same splitting twice and is stated in
`notes/algtop-remaining-route-2026-09-05.md`.

## Main results

* `kronecker_surjective`
* `exists_cocycle_pairing` — the same statement in cocycle form.
-/

open CategoryTheory Limits AlgebraicTopology
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.AlgTop

noncomputable section

variable (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable (X : TopCat.{0}) (n : ℕ)

/-- The short complex whose homology is `Hₙ(X;R)`. -/
abbrev chainSc : ShortComplex (ModuleCat.{0} R) := (chainCx R X).sc n

/-- The cycles of the singular chain complex, concretely as a kernel. -/
theorem chainSc_g : (chainSc R X n).g
    = (chainCx R X).d n ((ComplexShape.down ℕ).next n) := rfl

/-- `iCycles` factors through the concrete kernel description. -/
theorem iCycles_eq_subtype (z : (chainCx R X).cycles n) :
    ((chainCx R X).iCycles n).hom z
      = (((chainSc R X n).moduleCatCyclesIso.hom).hom z : (chainCx R X).X n) := by
  have h := (chainSc R X n).moduleCatCyclesIso_hom_i
  have := ConcreteCategory.congr_hom h z
  simpa using this.symm

/-- The inverse of the cycles isomorphism is determined by its image in the
chain group. -/
theorem cyclesIso_inv_val (y : LinearMap.ker (chainSc R X n).g.hom) :
    ((chainCx R X).iCycles n).hom (((chainSc R X n).moduleCatCyclesIso.inv).hom y)
      = (y : (chainCx R X).X n) := by
  have h := (chainSc R X n).moduleCatCyclesIso_inv_iCycles
  have := ConcreteCategory.congr_hom h y
  simpa using this

/-- **Surjectivity of the Kronecker map.** -/
theorem kronecker_surjective (f : homologyOf R X n →ₗ[R] R) :
    ∃ a : cohomology R X n, (kronecker R X n).hom a = f := by
  classical
  -- the functional pulled back to the cycles, then to the concrete kernel
  set g : (chainCx R X).cycles n →ₗ[R] R :=
    f.comp ((chainCx R X).homologyπ n).hom with hg
  set g' : LinearMap.ker (chainSc R X n).g.hom →ₗ[R] R :=
    g.comp ((chainSc R X n).moduleCatCyclesIso.inv).hom with hg'
  obtain ⟨F, hF⟩ :=
    exists_extend_off_ker_d R X n ((ComplexShape.down ℕ).next n) g'
  -- the extension is a cocycle
  have hmem : ∀ c : (chainCx R X).X (n + 1),
      ((chainCx R X).d (n + 1) n).hom c ∈ LinearMap.ker (chainSc R X n).g.hom := by
    intro c
    rw [LinearMap.mem_ker, chainSc_g, ← ModuleCat.comp_apply, (chainCx R X).d_comp_d]
    rfl
  have hboundary : ∀ c : (chainCx R X).X (n + 1),
      ((chainSc R X n).moduleCatCyclesIso.inv).hom
          ⟨((chainCx R X).d (n + 1) n).hom c, hmem c⟩
        = ((chainCx R X).toCycles (n + 1) n).hom c := by
    intro c
    apply (ModuleCat.mono_iff_injective ((chainCx R X).iCycles n)).1 inferInstance
    rw [cyclesIso_inv_val, ← ModuleCat.comp_apply, (chainCx R X).toCycles_i]
  have hφ : IsCocycle R X n (ModuleCat.ofHom F) := by
    rw [isCocycle_iff]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    show F (((chainCx R X).d (n + 1) n).hom c) = 0
    rw [show (((chainCx R X).d (n + 1) n).hom c)
        = ((⟨((chainCx R X).d (n + 1) n).hom c, hmem c⟩ :
            LinearMap.ker (chainSc R X n).g.hom) : (chainCx R X).X n) from rfl,
      hF, hg', LinearMap.comp_apply, hboundary, hg, LinearMap.comp_apply,
      ← ModuleCat.comp_apply, (chainCx R X).toCycles_comp_homologyπ]
    simp
  -- the class of the extension has the prescribed Kronecker image
  refine ⟨cocycleClass R X n (ModuleCat.ofHom F) hφ, ?_⟩
  rw [kronecker_cocycleClass]
  have hcomp : (chainCx R X).homologyπ n ≫ kronOfCocycle R X n (ModuleCat.ofHom F) hφ
      = (chainCx R X).homologyπ n ≫ ModuleCat.ofHom f := by
    rw [homologyπ_kronOfCocycle]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    show F (((chainCx R X).iCycles n).hom z) = f (((chainCx R X).homologyπ n).hom z)
    rw [iCycles_eq_subtype, hF, hg', LinearMap.comp_apply]
    have hz : ((chainSc R X n).moduleCatCyclesIso.inv).hom
        (((chainSc R X n).moduleCatCyclesIso.hom).hom z) = z := by
      rw [← ModuleCat.comp_apply, (chainSc R X n).moduleCatCyclesIso.hom_inv_id]
      rfl
    rw [hz, hg, LinearMap.comp_apply]
  have := (cancel_epi ((chainCx R X).homologyπ n)).mp hcomp
  exact congrArg ModuleCat.Hom.hom this

/-- The same statement in cocycle form: every functional on homology is
represented by a cocycle. -/
theorem exists_cocycle_pairing (f : homologyOf R X n →ₗ[R] R) :
    ∃ (φ : singularCochainGroup R X n) (hφ : IsCocycle R X n φ),
      (kronOfCocycle R X n φ hφ).hom = f := by
  obtain ⟨a, ha⟩ := kronecker_surjective R X n f
  obtain ⟨φ, hφ, rfl⟩ := cocycleClass_surjective R X n a
  exact ⟨φ, hφ, by rw [← kronecker_cocycleClass, ha]⟩

end

end GroupApproximation.AlgTop
