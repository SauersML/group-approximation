import GroupApproximation.CharClass.OddPDiagonalSrc
import GroupApproximation.CharClass.OddPAcyclicZeroAug

/-!
# The equivariant diagonal at odd `p`

`oddDiagonal p r s hs : oddSrc p (oddSingularBoundary p) ⟶ oddTgt p r s hs` is the natural
`F_p[ℤ/p]`-linear chain map `W ⊗ C(X) → C(X)^{⊗r}` extending `e_0 ⊗ x ↦ (x, …, x)`, produced by the
acyclic-models existence theorem `acyclicModelsMap` from:

* freeness of the source on the standard simplices (`oddSrcFree`);
* acyclicity of the target on the models in positive degrees (`oddTgt_acyclicOnModels`) and in
  degree `0` relative to the augmentation (`oddTgt_acyclicZeroOnModels`, from lix-cupone's
  `tupD_exists_preimage_zero_stdSimplexTop`);
* the two augmentations and the degree-`0` diagonal (`OddPDiagonalSrc.lean`).

At the Steenrod arity `r = p` (the generator acting through `T`, `s = 1`) its components are named
`oddDiagApp`, with the consumer interface the cochain operations are written against:
`oddDiagApp_d` (chain map), `oddDiagApp_natural`, `oddDiagApp_add`, `oddDiagApp_smul` /
`oddDiagApp_grGen` (equivariance), `oddDiagApp_zero` (degree `0`).
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

variable (p : ℕ) [NeZero p]

/-! ## 1. Degree-`0` acyclicity of the target -/

omit [NeZero p] in
/-- lix-cupone's degree-`0` export, stated at the commutative-ring structure of `ZMod p` the target
uses. -/
theorem tupD_exists_preimage_zero_stdSimplexTop_zmod [Fact p.Prime] (n r : ℕ)
    (y : tupMod (ZMod p) (stdSimplexTop n) r 0)
    (hy : tupAug (ZMod p) (stdSimplexTop n) r y = 0) :
    ∃ z : tupMod (ZMod p) (stdSimplexTop n) r 1, tupD (ZMod p) (stdSimplexTop n) r 0 z = y := by
  have h := tupD_exists_preimage_zero_stdSimplexTop (ZMod p) n r
  exact h y hy

/-- **The target is acyclic on the models in degree `0`**, relative to its augmentation. -/
theorem oddTgt_acyclicZeroOnModels [Fact p.Prime] (r s : ℕ) (hs : r ∣ s * p) :
    AcyclicZeroOnModels stdSimplexTop (tgtAug p r s hs) where
  exists_preimage_zero n y hy := by
    have hy' : tupAug (ZMod p) (stdSimplexTop n) r y = 0 := hy
    obtain ⟨z, hz⟩ := tupD_exists_preimage_zero_stdSimplexTop_zmod p n r y hy'
    rw [show ((oddTgt p r s hs).obj (stdSimplexTop n)).d 1 0
        = tupDHom p (stdSimplexTop n) r 0 s hs from oddTgt_obj_d p r s hs (stdSimplexTop n) 0]
    exact ⟨z, hz⟩

/-! ## 2. The diagonal -/

/-- **The equivariant diagonal** `W ⊗ C(X) → C(X)^{⊗r}`. -/
def oddDiagonal [Fact p.Prime] (r s : ℕ) (hs : r ∣ s * p) :
    oddSrc p (oddSingularBoundary p) ⟶ oddTgt p r s hs :=
  acyclicModelsMap (oddSrcFree p (oddSingularBoundary p)) (oddTgt_acyclicOnModels p r s hs)
    (srcAug p) (tgtAug p r s hs) (oddTgt_acyclicZeroOnModels p r s hs) (diagF0 p r s hs)
    (diagF0_natural p r s hs) (diagF0_aug p r s hs)

/-- The component of the diagonal at the Steenrod arity, as a function. -/
def oddDiagApp [Fact p.Prime] (X : TopCat.{0}) (k : ℕ) (x : OddWTensor p k X) :
    tupMod (ZMod p) X p k :=
  (((oddDiagonal p p 1 (dvd_mul_left p 1)).app X).f k).hom x

omit [NeZero p] in
/-- The differential of the source, as the named map. -/
theorem oddSrc_obj_d (data : OddPBoundaryData p) (X : TopCat.{0}) (k : ℕ) :
    ((oddSrc p data).obj X).d (k + 1) k = ModuleCat.ofHom (oddDiff p data X k) :=
  oddSrcComplex_d p data X k

/-- **The diagonal is a chain map.** -/
theorem oddDiagApp_d [Fact p.Prime] (X : TopCat.{0}) (k : ℕ) (x : OddWTensor p (k + 1) X) :
    tupD (ZMod p) X p k (oddDiagApp p X (k + 1) x)
      = oddDiagApp p X k (oddDiff p (oddSingularBoundary p) X k x) := by
  have h := congrArg (fun g => ModuleCat.Hom.hom g x)
    (((oddDiagonal p p 1 (dvd_mul_left p 1)).app X).comm (k + 1) k)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [oddTgt_obj_d p p 1 (dvd_mul_left p 1) X k, oddSrc_obj_d p (oddSingularBoundary p) X k] at h
  exact h

/-- **The diagonal is natural.** -/
theorem oddDiagApp_natural [Fact p.Prime] {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ)
    (x : OddWTensor p k X) :
    tupMap (ZMod p) f p k (oddDiagApp p X k x)
      = oddDiagApp p Y k
          (Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p) (srcMapIdx f k) x) := by
  have h := congrArg (fun g => ModuleCat.Hom.hom (HomologicalComplex.Hom.f g k) x)
    ((oddDiagonal p p 1 (dvd_mul_left p 1)).naturality f)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

/-- The diagonal is additive. -/
theorem oddDiagApp_add [Fact p.Prime] (X : TopCat.{0}) (k : ℕ) (x y : OddWTensor p k X) :
    oddDiagApp p X k (x + y) = oddDiagApp p X k x + oddDiagApp p X k y :=
  map_add (((oddDiagonal p p 1 (dvd_mul_left p 1)).app X).f k).hom x y

/-- **The diagonal is equivariant**: the group ring acts on the target through `T`. -/
theorem oddDiagApp_smul [Fact p.Prime] (X : TopCat.{0}) (k : ℕ) (c : GroupRingZMod p)
    (x : OddWTensor p k X) :
    oddDiagApp p X k (c • x)
      = galAlgHomP (tupT (ZMod p) X p k ^ 1) (tupT_pow_pow p X p k 1 (dvd_mul_left p 1)) c
          (oddDiagApp p X k x) :=
  map_smul (((oddDiagonal p p 1 (dvd_mul_left p 1)).app X).f k).hom c x

/-- The generator of the group ring acts on the target as the cyclic permutation `T`. -/
theorem oddDiagApp_grGen [Fact p.Prime] (X : TopCat.{0}) (k : ℕ) (x : OddWTensor p k X) :
    oddDiagApp p X k (grGen p • x) = tupT (ZMod p) X p k (oddDiagApp p X k x) := by
  rw [oddDiagApp_smul]
  have h : galAlgHomP (tupT (ZMod p) X p k ^ 1) (tupT_pow_pow p X p k 1 (dvd_mul_left p 1))
      (grGen p) (oddDiagApp p X k x) = (tupT (ZMod p) X p k ^ 1) (oddDiagApp p X k x) :=
    moduleOfOrderP_smul (Fact.out : p.Prime).one_lt _ _ _
  rw [h, pow_one]

/-- The index of a degree-`0` generator on a point is the constant tuple of that point. -/
@[simp] theorem diagPtIdx_zero (X : TopCat.{0}) (r : ℕ) (x : stdSimplexTop 0 ⟶ X) :
    diagPtIdx X r (⟨0, x⟩ : WSIndex 0 X) = diagPt X r x :=
  rfl

/-- **In degree `0` the diagonal is the constant tuple.**  The component is rewritten to
`diagF0` by `acyclicModelsMap_zero` after unfolding `oddDiagApp` and `oddDiagonal`, so the
unifier never reduces the recursive component `((acyclicModelsMap …).app X).f 0` (that
reduction exhausted the heartbeats at `whnf`, probe 0912-120717-49104).  `diagF0` is then read
as `diagF0Lin` by `show`, as in `diagF0_natural`: `unfold diagF0` leaves `ModuleCat.ofHom` at
the `ModuleCat.of` objects, which is not type-correct at `instances` transparency, so
`ModuleCat.hom_ofHom` cannot be rewritten there (probe 0912-121845-91999). -/
theorem oddDiagApp_zero [Fact p.Prime] (X : TopCat.{0}) (x : stdSimplexTop 0 ⟶ X) :
    oddDiagApp p X 0 (Finsupp.single (⟨0, x⟩ : WSIndex 0 X) (1 : GroupRingZMod p))
      = Finsupp.single (diagPt X p x) (1 : ZMod p) := by
  have h := acyclicModelsMap_zero (oddSrcFree p (oddSingularBoundary p))
    (oddTgt_acyclicOnModels p p 1 (dvd_mul_left p 1)) (srcAug p)
    (tgtAug p p 1 (dvd_mul_left p 1)) (oddTgt_acyclicZeroOnModels p p 1 (dvd_mul_left p 1))
    (diagF0 p p 1 (dvd_mul_left p 1)) (diagF0_natural p p 1 (dvd_mul_left p 1))
    (diagF0_aug p p 1 (dvd_mul_left p 1)) X
  unfold oddDiagApp oddDiagonal
  rw [h, ← diagPtIdx_zero X p x]
  letI := tupModule p X p 0 1 (dvd_mul_left p 1)
  show diagF0Lin p X p 1 (dvd_mul_left p 1)
      (Finsupp.single (⟨0, x⟩ : WSIndex 0 X) (1 : GroupRingZMod p)) = _
  exact diagF0Lin_single p X p 1 (dvd_mul_left p 1) ⟨0, x⟩

end

end GroupApproximation.CharClass
