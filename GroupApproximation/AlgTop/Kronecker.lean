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

/-- In the chain-complex shape the previous index of `n` is `n + 1`.

`ComplexShape.prev_eq` is the *structure field* `Rel i j → Rel i' j → i = i'`,
so it takes two `Rel` arguments and cannot compute `prev`; the lemma that reads
a `Rel` off into a `prev` is `ComplexShape.prev_eq'`. -/
theorem down_prev (n : ℕ) : (ComplexShape.down ℕ).prev n = n + 1 :=
  (ComplexShape.down ℕ).prev_eq' (by simp [ComplexShape.down_Rel])

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
        -- Do *not* rewrite `iCycles (c + c')` inside `kronOfCocycle`: its second
        -- argument is a proof whose type mentions the first, so the motive is not
        -- type correct.  Move along `kronOfCocycle_congr` instead.
        have hsum : ((cochainCx R X).iCycles n).hom (c + c')
            = ((cochainCx R X).iCycles n).hom c + ((cochainCx R X).iCycles n).hom c' :=
          map_add _ _ _
        have hcoc : IsCocycle R X n (((cochainCx R X).iCycles n).hom c
            + ((cochainCx R X).iCycles n).hom c') := by
          rw [← hsum]; exact cochainCoboundary_iCycles R X n (c + c')
        exact congrArg ModuleCat.Hom.hom
          ((kronOfCocycle_congr R X n hsum _ hcoc).trans
            (kronOfCocycle_add R X n _ _ (cochainCoboundary_iCycles R X n c)
              (cochainCoboundary_iCycles R X n c') hcoc))
      map_smul' := fun s c => by
        have hsmul : ((cochainCx R X).iCycles n).hom (s • c)
            = s • ((cochainCx R X).iCycles n).hom c := map_smul _ _ _
        have hcoc : IsCocycle R X n (s • ((cochainCx R X).iCycles n).hom c) := by
          rw [← hsmul]; exact cochainCoboundary_iCycles R X n (s • c)
        exact congrArg ModuleCat.Hom.hom
          ((kronOfCocycle_congr R X n hsmul _ hcoc).trans
            (kronOfCocycle_smul R X n s _ (cochainCoboundary_iCycles R X n c) hcoc)) }

@[simp] theorem kronCycleMor_hom (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (c : (cochainCx R X).cycles n) :
    (kronCycleMor R X n).hom c
      = (kronOfCocycle R X n (((cochainCx R X).iCycles n).hom c)
          (cochainCoboundary_iCycles R X n c)).hom := rfl

/-- The evaluation map kills cochain coboundaries. -/
theorem kronCycleMor_toCycles (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    (cochainCx R X).toCycles ((ComplexShape.up ℕ).prev n) n ≫ kronCycleMor R X n = 0 := by
  -- Split on the shape *before* introducing the element: after `subst` the
  -- source index is literally `m`, so `η` never acquires a type mentioning
  -- `(ComplexShape.up ℕ).prev`, whose value is an opaque `Exists.choose` that
  -- no arithmetic tactic can identify with `m`.
  by_cases hrel : (ComplexShape.up ℕ).Rel ((ComplexShape.up ℕ).prev n) n
  · obtain ⟨m, hm⟩ : ∃ m, m + 1 = n := ⟨(ComplexShape.up ℕ).prev n, hrel⟩
    subst hm
    rw [show (ComplexShape.up ℕ).prev (m + 1) = m from (ComplexShape.up ℕ).prev_eq' rfl]
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro η
    show (kronOfCocycle R X (m + 1) (((cochainCx R X).iCycles (m + 1)).hom
        (((cochainCx R X).toCycles m (m + 1)).hom η)) _).hom = _
    have heq : ((cochainCx R X).iCycles (m + 1)).hom
          (((cochainCx R X).toCycles m (m + 1)).hom η)
        = cochainCoboundary R X m η :=
      ConcreteCategory.congr_hom ((cochainCx R X).toCycles_i m (m + 1)) η
    rw [kronOfCocycle_congr R X (m + 1) heq _
        (by rw [← heq]; exact cochainCoboundary_iCycles R X (m + 1) _),
      kronOfCocycle_coboundary R X m η _]
    rfl
  · have hzero : (cochainCx R X).toCycles ((ComplexShape.up ℕ).prev n) n = 0 := by
      rw [← cancel_mono ((cochainCx R X).iCycles n), (cochainCx R X).toCycles_i, zero_comp]
      exact (cochainCx R X).shape _ _ hrel
    rw [hzero, zero_comp]

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
  -- Go through `cyclesMk'`, which already carries the `next`-index proof: written
  -- out here, `by simp [ComplexShape.next]` unfolds `next` to its `dif` and stalls
  -- on the bare `Exists.choose`, which no arithmetic tactic can identify with `n + 1`.
  show (kronecker R X n).hom (((cochainCx R X).homologyπ n).hom (cyclesMk' R X n φ hφ))
      = (kronOfCocycle R X n φ hφ).hom
  rw [show (kronecker R X n).hom (((cochainCx R X).homologyπ n).hom (cyclesMk' R X n φ hφ))
        = ((cochainCx R X).homologyπ n ≫ kronecker R X n).hom (cyclesMk' R X n φ hφ) from rfl,
    homologyπ_kronecker, kronCycleMor_hom]
  exact congrArg ModuleCat.Hom.hom
    (kronOfCocycle_congr R X n (iCycles_cyclesMk' R X n φ hφ) _ hφ)

end

end GroupApproximation.AlgTop
