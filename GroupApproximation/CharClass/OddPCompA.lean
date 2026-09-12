import GroupApproximation.CharClass.OddPProductAW
import GroupApproximation.CharClass.OddPDiagonal

/-!
# The first composite of the odd-primary Cartan comparison

The Cartan formula at odd `p` compares two natural `F_p[ℤ/p]`-linear chain maps
`W ⊗ C(X) → C(X)^{⊗2p}`, the generator acting on the `2p`-fold power through `T²`.  This file
builds the first one:

```text
compA = (slotwise Alexander–Whitney) ∘ Δ :  W ⊗ C(X) → C(X)^{⊗p} → C(X)^{⊗2p},
```

where slot `2j` of the output holds the front face of slot `j` and slot `2j + 1` its back face.
Slotwise Alexander–Whitney has degree `0`, so it carries no Koszul sign, and it turns the rotation by
one slot of a `p`-tuple into the rotation by two slots of the interleaved `2p`-tuple.  So it is a
natural transformation `oddTgt p p 1 ⟶ oddTgt p (2p) 2`, and `compA` is the equivariant diagonal
followed by it.

Evaluated against `u ⊗ v ⊗ u ⊗ v ⊗ ⋯`, the first composite is the diagonal evaluated against
`(u ⌣ v)^{⊗p}`: on the generator `e_i ⊗ σ` it is `D_i(u ⌣ v)(σ)`.

## Main results

* `awNat` — slotwise Alexander–Whitney as a natural chain map between the two target functors.
* `compA` — **the first composite.**
* `compA_zero` — in degree `0` it sends `e_0 ⊗ x` to the constant tuple `x^{⊗2p}`.
* `tupEval_compA`, `tupEval_compA_oddD` — **the first composite, evaluated.**
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

variable (p : ℕ) [NeZero p]

/-- The divisibility under which the generator acts on the `2p`-fold power through `T²`. -/
theorem dvd_two_mul_self : 2 * p ∣ 2 * p := dvd_refl (2 * p)

/-! ## 1. Slotwise Alexander–Whitney over the group ring -/

/-- **Slotwise Alexander–Whitney on the degree-`k` carrier, over the group ring**: the generator acts
through `T` on the source and through `T²` on the target. -/
def awTupLin (X : TopCat.{0}) (k : ℕ) :
    @LinearMap (GroupRingZMod p) (GroupRingZMod p) _ _ (RingHom.id (GroupRingZMod p))
      (tupMod (ZMod p) X p k) (tupMod (ZMod p) X (2 * p) k) _ _
      (tupModule p X p k 1 (dvd_mul_left p 1)) (tupModule p X (2 * p) k 2 (dvd_two_mul_self p)) :=
  letI := tupModule p X p k 1 (dvd_mul_left p 1)
  letI := tupModule p X (2 * p) k 2 (dvd_two_mul_self p)
  { toFun := awTup (ZMod p) X p k
    map_add' := fun u v => map_add _ u v
    map_smul' := fun c y =>
      galAlgHomP_comm p (tupT (ZMod p) X p k ^ 1) (tupT_pow_pow p X p k 1 (dvd_mul_left p 1))
        (tupT (ZMod p) X (2 * p) k ^ 2) (tupT_pow_pow p X (2 * p) k 2 (dvd_two_mul_self p))
        (awTup (ZMod p) X p k) (fun v => by rw [pow_one, awTup_tupT]) c y }

/-- The degree-`k` component, as a morphism over the group ring. -/
def awTupHom (X : TopCat.{0}) (k : ℕ) :
    tupObj p X p k 1 (dvd_mul_left p 1) ⟶ tupObj p X (2 * p) k 2 (dvd_two_mul_self p) :=
  letI := tupModule p X p k 1 (dvd_mul_left p 1)
  letI := tupModule p X (2 * p) k 2 (dvd_two_mul_self p)
  ModuleCat.ofHom (awTupLin p X k)

theorem awTupHom_hom_apply (X : TopCat.{0}) (k : ℕ) (y : tupMod (ZMod p) X p k) :
    (awTupHom p X k).hom y = awTup (ZMod p) X p k y := by
  unfold awTupHom
  rfl

/-- **Slotwise Alexander–Whitney as a map of complexes.** -/
def awTupCx (X : TopCat.{0}) :
    tupCx p X p 1 (dvd_mul_left p 1) ⟶ tupCx p X (2 * p) 2 (dvd_two_mul_self p) where
  f k := awTupHom p X k
  comm' i j hij := by
    have hij' : j + 1 = i := hij
    subst hij'
    rw [tupCx_d, tupCx_d]
    letI := tupModule p X p (j + 1) 1 (dvd_mul_left p 1)
    letI := tupModule p X p j 1 (dvd_mul_left p 1)
    letI := tupModule p X (2 * p) (j + 1) 2 (dvd_two_mul_self p)
    letI := tupModule p X (2 * p) j 2 (dvd_two_mul_self p)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, awTupHom_hom_apply, tupDHom_hom_apply]
    exact awTup_tupD (ZMod p) X p j y

theorem awTupCx_f (X : TopCat.{0}) (k : ℕ) : (awTupCx p X).f k = awTupHom p X k := rfl

/-- **Slotwise Alexander–Whitney as a natural transformation** `oddTgt p p 1 ⟶ oddTgt p (2p) 2`. -/
def awNat : oddTgt p p 1 (dvd_mul_left p 1) ⟶ oddTgt p (2 * p) 2 (dvd_two_mul_self p) where
  app X := awTupCx p X
  naturality X Y φ := by
    refine HomologicalComplex.hom_ext _ _ fun k => ?_
    letI := tupModule p X p k 1 (dvd_mul_left p 1)
    letI := tupModule p Y (2 * p) k 2 (dvd_two_mul_self p)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
    show (awTupHom p Y k).hom ((tupMapHom p φ p k 1 (dvd_mul_left p 1)).hom y)
      = (tupMapHom p φ (2 * p) k 2 (dvd_two_mul_self p)).hom ((awTupHom p X k).hom y)
    simp only [awTupHom_hom_apply, tupMapHom_hom_apply]
    exact (awTup_tupMap (ZMod p) φ p k y).symm

/-! ## 2. The first composite -/

/-- **The first composite** `W ⊗ C(X) → C(X)^{⊗p} → C(X)^{⊗2p}`: the equivariant diagonal, then
slotwise Alexander–Whitney. -/
def compA [Fact p.Prime] :
    oddSrc p (oddSingularBoundary p) ⟶ oddTgt p (2 * p) 2 (dvd_two_mul_self p) :=
  oddDiagonal p p 1 (dvd_mul_left p 1) ≫ awNat p

/-- The components of the first composite, as functions. -/
theorem compA_app_f_apply [Fact p.Prime] (X : TopCat.{0}) (k : ℕ) (x : OddWTensor p k X) :
    (((compA p).app X).f k).hom x = awTup (ZMod p) X p k (oddDiagApp p X k x) := by
  show (awTupHom p X k).hom ((((oddDiagonal p p 1 (dvd_mul_left p 1)).app X).f k).hom x) = _
  rw [awTupHom_hom_apply]
  rfl

/-- **In degree `0` the first composite is the constant tuple** `x^{⊗2p}`. -/
theorem compA_zero [Fact p.Prime] (X : TopCat.{0}) (x : stdSimplexTop 0 ⟶ X) :
    (((compA p).app X).f 0).hom (Finsupp.single (⟨0, x⟩ : WSIndex 0 X) (1 : GroupRingZMod p))
      = Finsupp.single (diagPt X (2 * p) x) (1 : ZMod p) := by
  rw [compA_app_f_apply, oddDiagApp_zero, awTup_diagPt]

/-! ## 3. The first composite, evaluated -/

/-- **The first composite, evaluated** against `u ⊗ v ⊗ u ⊗ v ⊗ ⋯`: it is the diagonal evaluated
against `(u ⌣ v)^{⊗p}`.  No sign: slotwise Alexander–Whitney has degree `0` and evaluation carries
none. -/
theorem tupEval_compA [Fact p.Prime] (X : TopCat.{0}) (k q q' : ℕ)
    (u : singularCochainGroup (ZMod p) X q) (v : singularCochainGroup (ZMod p) X q')
    (x : OddWTensor p k X) :
    tupEval (ZMod p) X (2 * p) k
        (tupInterleave p (fun _ => Pi.single q u) (fun _ => Pi.single q' v))
        ((((compA p).app X).f k).hom x)
      = tupEval (ZMod p) X p k (fun _ => Pi.single (q + q') (cochainCup q q' u v))
          (oddDiagApp p X k x) := by
  rw [compA_app_f_apply, ← tupEvalAll_tupIncl,
    ← LinearMap.comp_apply (tupIncl (ZMod p) X (2 * p) k) (awTup (ZMod p) X p k),
    tupIncl_comp_awTup, LinearMap.comp_apply, tupEvalAll_awTupAll, tupEvalAll_tupIncl]
  simp only [gCupFun_piSingle]

/-- **On a generator, the first composite evaluates to `D_i(u ⌣ v)`.** -/
theorem tupEval_compA_oddD [Fact p.Prime] (X : TopCat.{0}) (q q' i : ℕ)
    (u : singularCochainGroup (ZMod p) X q) (v : singularCochainGroup (ZMod p) X q')
    (σ : singularSimplices X (p * (q + q') - i)) :
    tupEval (ZMod p) X (2 * p) (p * (q + q'))
        (tupInterleave p (fun _ => Pi.single q u) (fun _ => Pi.single q' v))
        ((((compA p).app X).f (p * (q + q'))).hom
          (Finsupp.single (⟨⟨p * (q + q') - i, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,
            simplexEquiv X (p * (q + q') - i) σ⟩ : WSIndex (p * (q + q')) X) (1 : GroupRingZMod p)))
      = cochainEval (p * (q + q') - i) (oddD p (q + q') i (cochainCup q q' u v)) σ := by
  rw [tupEval_compA, oddD_eval]

end

end GroupApproximation.CharClass

open GroupApproximation.CharClass

#audit_axioms compA
#audit_axioms compA_zero
#audit_axioms tupEval_compA_oddD
