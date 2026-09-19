import GroupApproximation.AlgTop.SingularChainFree

/-!
# The Kronecker map `Hⁿ(X; R) → Hom(Hₙ(X; R), R)`

Evaluating a cocycle on a cycle descends to a pairing between cohomology and
homology. This file constructs that pairing and shows it is a `ModuleCat`
morphism; the universal coefficient theorem — that it is surjective always, and
injective when `Hₙ₋₁(X;R)` is projective — is the next step, and its two
splitting inputs are already available as `exists_extend_off_ker_d` and
`projective_quot_ker_d`.

## Main definitions

* `homologyOf R X n` — singular homology `Hₙ(X; R)`.
* `kronOfCocycle R X n φ hφ : Hₙ(X;R) ⟶ R` — evaluation of a cocycle.
* `kronecker R X n : Hⁿ(X;R) ⟶ ModuleCat.of R (Hₙ(X;R) →ₗ[R] R)`.

## Main results

* `homologyπ_kronOfCocycle` — the defining property.
* `kronOfCocycle_add`, `kronOfCocycle_smul` — linearity in the cochain.
* `kronOfCocycle_coboundary` — a coboundary pairs to zero, which is what lets the
  map descend to cohomology classes.
* `kronecker_cocycleClass` — the computation rule on a cocycle class.
-/

open CategoryTheory Limits AlgebraicTopology
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.AlgTop

noncomputable section

/-- Singular homology `Hₙ(X; R)`. -/
abbrev homologyOf (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} R :=
  (chainCx R X).homology n

/-- In the chain-complex shape the previous index of `n` is `n + 1`. -/
theorem down_prev (n : ℕ) : (ComplexShape.down ℕ).prev n = n + 1 :=
  (ComplexShape.down ℕ).prev_eq (by simp [ComplexShape.down_Rel])

/-! ## 1. Evaluation of a single cocycle -/

/-- **Kronecker evaluation of a cocycle.** A cocycle `φ` restricted to cycles
kills boundaries, so it descends to a map out of homology. -/
def kronOfCocycle (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup R X n) (hφ : IsCocycle R X n φ) :
    homologyOf R X n ⟶ ModuleCat.of R R :=
  ((chainCx R X).homologyIsCokernel (n + 1) n (down_prev n)).desc
    (CokernelCofork.ofπ ((chainCx R X).iCycles n ≫ φ) (by
      rw [← Category.assoc, (chainCx R X).toCycles_i]
      exact (isCocycle_iff R X n φ).mp hφ))

/-- The defining property of `kronOfCocycle`. -/
theorem homologyπ_kronOfCocycle (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup R X n) (hφ : IsCocycle R X n φ) :
    (chainCx R X).homologyπ n ≫ kronOfCocycle R X n φ hφ
      = (chainCx R X).iCycles n ≫ φ :=
  ((chainCx R X).homologyIsCokernel (n + 1) n (down_prev n)).fac
    (CokernelCofork.ofπ ((chainCx R X).iCycles n ≫ φ) (by
      rw [← Category.assoc, (chainCx R X).toCycles_i]
      exact (isCocycle_iff R X n φ).mp hφ))
    WalkingParallelPair.one

theorem kronOfCocycle_congr (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    {φ φ' : singularCochainGroup R X n} (h : φ = φ') (hφ : IsCocycle R X n φ)
    (hφ' : IsCocycle R X n φ') :
    kronOfCocycle R X n φ hφ = kronOfCocycle R X n φ' hφ' := by
  subst h; rfl

theorem kronOfCocycle_add (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (φ ψ : singularCochainGroup R X n) (hφ : IsCocycle R X n φ) (hψ : IsCocycle R X n ψ)
    (hs : IsCocycle R X n (φ + ψ)) :
    kronOfCocycle R X n (φ + ψ) hs
      = kronOfCocycle R X n φ hφ + kronOfCocycle R X n ψ hψ := by
  apply (cancel_epi ((chainCx R X).homologyπ n)).mp
  simp only [homologyπ_kronOfCocycle, Preadditive.comp_add]

theorem kronOfCocycle_smul (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) (s : R)
    (φ : singularCochainGroup R X n) (hφ : IsCocycle R X n φ)
    (hs : IsCocycle R X n (s • φ)) :
    kronOfCocycle R X n (s • φ) hs = s • kronOfCocycle R X n φ hφ := by
  apply (cancel_epi ((chainCx R X).homologyπ n)).mp
  simp only [homologyπ_kronOfCocycle, Linear.comp_smul]

/-- **A coboundary pairs to zero.** This is what makes the Kronecker map descend
to cohomology classes. -/
theorem kronOfCocycle_coboundary (R : Type) [CommRing R] (X : TopCat.{0}) (m : ℕ)
    (ψ : singularCochainGroup R X m)
    (h : IsCocycle R X (m + 1) (cochainCoboundary R X m ψ)) :
    kronOfCocycle R X (m + 1) (cochainCoboundary R X m ψ) h = 0 := by
  apply (cancel_epi ((chainCx R X).homologyπ (m + 1))).mp
  rw [homologyπ_kronOfCocycle, comp_zero, cochainCoboundary_eq_comp, ← Category.assoc,
    (chainCx R X).iCycles_d, zero_comp]

/-! ## 2. The Kronecker map on cohomology -/

/-- Evaluation of a cochain-level cycle, as an `R`-linear map into the dual of
homology. -/
def kronCycleMor (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    (cochainCx R X).cycles n ⟶ ModuleCat.of R (homologyOf R X n →ₗ[R] R) :=
  ModuleCat.ofHom
    { toFun := fun c => (kronOfCocycle R X n (((cochainCx R X).iCycles n).hom c)
        (cochainCoboundary_iCycles R X n c)).hom
      map_add' := fun c c' => by
        have h := kronOfCocycle_add R X n (((cochainCx R X).iCycles n).hom c)
          (((cochainCx R X).iCycles n).hom c') (cochainCoboundary_iCycles R X n c)
          (cochainCoboundary_iCycles R X n c')
          (by rw [← map_add]; exact cochainCoboundary_iCycles R X n (c + c'))
        rw [← map_add] at h
        rw [show (((cochainCx R X).iCycles n).hom (c + c')) = _ from map_add _ c c']
        exact congrArg ModuleCat.Hom.hom h
      map_smul' := fun s c => by
        have h := kronOfCocycle_smul R X n s (((cochainCx R X).iCycles n).hom c)
          (cochainCoboundary_iCycles R X n c)
          (by rw [← map_smul]; exact cochainCoboundary_iCycles R X n (s • c))
        rw [← map_smul] at h
        rw [show (((cochainCx R X).iCycles n).hom (s • c)) = _ from map_smul _ s c]
        exact congrArg ModuleCat.Hom.hom h }

@[simp] theorem kronCycleMor_hom (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (c : (cochainCx R X).cycles n) :
    (kronCycleMor R X n).hom c
      = (kronOfCocycle R X n (((cochainCx R X).iCycles n).hom c)
          (cochainCoboundary_iCycles R X n c)).hom := rfl

/-- The evaluation map kills cochain coboundaries. -/
theorem kronCycleMor_toCycles (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    (cochainCx R X).toCycles ((ComplexShape.up ℕ).prev n) n ≫ kronCycleMor R X n = 0 := by
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro η
  show (kronOfCocycle R X n (((cochainCx R X).iCycles n).hom
      (((cochainCx R X).toCycles ((ComplexShape.up ℕ).prev n) n).hom η)) _).hom = _
  have heq : ((cochainCx R X).iCycles n).hom
        (((cochainCx R X).toCycles ((ComplexShape.up ℕ).prev n) n).hom η)
      = ((cochainCx R X).d ((ComplexShape.up ℕ).prev n) n).hom η := by
    rw [← ModuleCat.comp_apply, (cochainCx R X).toCycles_i]
  have hzero : kronOfCocycle R X n (((cochainCx R X).d ((ComplexShape.up ℕ).prev n) n).hom η)
      (by rw [← heq]; exact cochainCoboundary_iCycles R X n _) = 0 := by
    by_cases hrel : (ComplexShape.up ℕ).Rel ((ComplexShape.up ℕ).prev n) n
    · obtain ⟨m, hm⟩ : ∃ m, m + 1 = n := ⟨(ComplexShape.up ℕ).prev n, hrel⟩
      subst hm
      exact kronOfCocycle_coboundary R X _ η _
    · have hz : ((cochainCx R X).d ((ComplexShape.up ℕ).prev n) n).hom η = 0 := by
        rw [(cochainCx R X).shape _ _ hrel]; simp
      rw [kronOfCocycle_congr R X n hz _ (cochainCoboundary_zero R X n)]
      apply (cancel_epi ((chainCx R X).homologyπ n)).mp
      rw [homologyπ_kronOfCocycle, comp_zero, comp_zero]
  rw [kronOfCocycle_congr R X n heq _
    (by rw [← heq]; exact cochainCoboundary_iCycles R X n _), hzero]
  rfl

/-- **The Kronecker map** `Hⁿ(X; R) → Hom(Hₙ(X; R), R)`. -/
def kronecker (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    cohomology R X n ⟶ ModuleCat.of R (homologyOf R X n →ₗ[R] R) :=
  ((cochainCx R X).homologyIsCokernel ((ComplexShape.up ℕ).prev n) n rfl).desc
    (CokernelCofork.ofπ (kronCycleMor R X n) (kronCycleMor_toCycles R X n))

theorem homologyπ_kronecker (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    (cochainCx R X).homologyπ n ≫ kronecker R X n = kronCycleMor R X n :=
  ((cochainCx R X).homologyIsCokernel ((ComplexShape.up ℕ).prev n) n rfl).fac
    (CokernelCofork.ofπ (kronCycleMor R X n) (kronCycleMor_toCycles R X n))
    WalkingParallelPair.one

/-- **Computation rule.** On the class of a cocycle the Kronecker map is
evaluation of that cocycle. -/
theorem kronecker_cocycleClass (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup R X n) (hφ : IsCocycle R X n φ) :
    (kronecker R X n).hom (cocycleClass R X n φ hφ)
      = (kronOfCocycle R X n φ hφ).hom := by
  rw [cocycleClass,
    show (kronecker R X n).hom
          (((cochainCx R X).homologyπ n).hom
            ((cochainCx R X).cyclesMk φ (n + 1) (by simp [ComplexShape.next]) hφ))
        = ((cochainCx R X).homologyπ n ≫ kronecker R X n).hom
            ((cochainCx R X).cyclesMk φ (n + 1) (by simp [ComplexShape.next]) hφ) from rfl,
    homologyπ_kronecker, kronCycleMor_hom]
  exact congrArg ModuleCat.Hom.hom
    (kronOfCocycle_congr R X n (iCycles_cyclesMk R X n φ hφ) _ hφ)

end

end GroupApproximation.AlgTop
