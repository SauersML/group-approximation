import GroupApproximation.CharClass.CartanFreeCxTensorAug
import GroupApproximation.CharClass.CartanSimplexExact
import GroupApproximation.CharClass.AcyclicModelsSplitting
import Mathlib.Algebra.Field.ZMod

/-!
# The singular complex as a `FreeCx`, and acyclicity of the pair complex

This file connects the general machinery to the objects of the comparison.

The mod-2 singular chain complex of a space, with the per-factor boundary `bdU`,
is a complex of free `F₂`-modules presented by its degreewise basis, so it is a
`FreeCx`.  Its tensor square is then `cc-steenrod`'s pair index *on the nose*,
and the general tensor differential is their `dTgt`: the two halves match
through their own `dLeft_eq_bdU` and `dRight_eq_bdU`.

Over a standard simplex the complex is acyclic in positive degrees, proved in
`CartanSimplexExact.lean`, so the field-splitting machinery of
`AcyclicModelsSplitting.lean` produces an augmented contraction, and the tensor
theorem then contracts the pair complex.

## Main results

* `singFreeCx` — the singular complex, as a `FreeCx`.
* `tensorD_eq_dTgt` — the general tensor differential is `cc-steenrod`'s.
* `dTgt_dTgt` — **their differential squares to zero.**
* `singAug` — an augmented contraction of the singular complex of a model.
* `dTgt_exists_preimage_stdSimplexTop` — **the pair complex is acyclic on the
  models.**
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

/-! ## 1. The singular complex as a `FreeCx` -/

/-- The mod-2 singular chain complex, presented by its degreewise basis. -/
noncomputable abbrev singFreeCx (X : TopCat.{0}) : FreeCx where
  ι := singularSimplices X
  d := bdU (ZMod 2) X
  d_d k u := bdU_bdU (ZMod 2) X k u

/-- The tensor square of the singular complex is indexed by `cc-steenrod`'s
pair index, definitionally. -/
theorem tensorIdx_eq_pairIdx (X : TopCat.{0}) (k : ℕ) :
    TensorIdx (singFreeCx X) (singFreeCx X) k = Steenrod.PairIdx X k := rfl

/-! ## 2. The general differential is `cc-steenrod`'s -/

theorem tenElt_single_right {A B : FreeCx} {k : ℕ} (p : Steenrod.PairDeg k)
    (u : A.ι p.val.1 →₀ ZMod 2) (y : B.ι p.val.2) :
    tenElt A B p u (Finsupp.single y 1)
      = Finsupp.lmapDomain (ZMod 2) (ZMod 2)
          (fun x => (⟨p, (x, y)⟩ : TensorIdx A B k)) u := by
  induction u using Finsupp.induction_linear with
  | zero => rw [tenElt_zero_left, map_zero]
  | add f g hf hg => rw [tenElt_add_left, map_add, hf, hg]
  | single x c =>
      rw [tenElt_single_left, incR_single, Finsupp.smul_single, smul_eq_mul, mul_one,
        Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem tensorDGen_eq_dGen (X : TopCat.{0}) (k : ℕ) (q : Steenrod.PairIdx X (k + 1)) :
    tensorDGen (singFreeCx X) (singFreeCx X) k q = Steenrod.dGen X (ZMod 2) k q := by
  obtain ⟨⟨⟨a, b⟩, hab⟩, σ, τ⟩ := q
  have hL : tdL (singFreeCx X) (singFreeCx X) k a b hab
        (Finsupp.single σ 1) (Finsupp.single τ 1)
      = Steenrod.dLeft X (ZMod 2) k a b hab σ τ := by
    cases a with
    | zero =>
        rw [tdL_zero, Steenrod.dLeft_zero]
    | succ a' =>
        rw [tdL_succ, tenElt_single_right, Steenrod.dLeft_eq_bdU]
  have hR : tdR (singFreeCx X) (singFreeCx X) k a b hab
        (Finsupp.single σ 1) (Finsupp.single τ 1)
      = Steenrod.dRight X (ZMod 2) k a b hab σ τ := by
    cases b with
    | zero =>
        rw [tdR_zero, Steenrod.dRight_zero]
    | succ b' =>
        rw [tdR_succ, tenElt_single_left, one_smul, Steenrod.dRight_eq_bdU]
        rfl
  show tdL (singFreeCx X) (singFreeCx X) k a b hab
        (Finsupp.single σ 1) (Finsupp.single τ 1)
      + tdR (singFreeCx X) (singFreeCx X) k a b hab
        (Finsupp.single σ 1) (Finsupp.single τ 1)
      = Steenrod.dLeft X (ZMod 2) k a b hab σ τ + Steenrod.dRight X (ZMod 2) k a b hab σ τ
  rw [hL, hR]

/-- **The general tensor differential is `cc-steenrod`'s pair differential.** -/
theorem tensorD_eq_dTgt (X : TopCat.{0}) (k : ℕ)
    (y : Steenrod.PairIdx X (k + 1) →₀ ZMod 2) :
    tensorD (singFreeCx X) (singFreeCx X) k y = Steenrod.dTgt X (ZMod 2) k y := by
  induction y using Finsupp.induction_linear with
  | zero =>
      calc tensorD (singFreeCx X) (singFreeCx X) k
            (0 : Steenrod.PairIdx X (k + 1) →₀ ZMod 2)
          = 0 := map_zero _
        _ = Steenrod.dTgt X (ZMod 2) k 0 := (map_zero _).symm
  | add f g hf hg =>
      calc tensorD (singFreeCx X) (singFreeCx X) k (f + g)
          = tensorD (singFreeCx X) (singFreeCx X) k f
            + tensorD (singFreeCx X) (singFreeCx X) k g := map_add _ f g
        _ = Steenrod.dTgt X (ZMod 2) k f + Steenrod.dTgt X (ZMod 2) k g := by
              rw [hf, hg]
        _ = Steenrod.dTgt X (ZMod 2) k (f + g) := (map_add _ f g).symm
  | single q c =>
      calc tensorD (singFreeCx X) (singFreeCx X) k (Finsupp.single q c)
          = c • tensorDGen (singFreeCx X) (singFreeCx X) k q :=
            tensorD_single (singFreeCx X) (singFreeCx X) k q c
        _ = c • Steenrod.dGen X (ZMod 2) k q :=
            congrArg (fun w => c • w) (tensorDGen_eq_dGen X k q)
        _ = Steenrod.dTgt X (ZMod 2) k (Finsupp.single q c) :=
            (Steenrod.dTgt_single X (ZMod 2) k q c).symm

/-- **The pair differential squares to zero.** -/
theorem dTgt_dTgt (X : TopCat.{0}) (k : ℕ)
    (y : Steenrod.PairIdx X (k + 2) →₀ ZMod 2) :
    Steenrod.dTgt X (ZMod 2) k (Steenrod.dTgt X (ZMod 2) (k + 1) y) = 0 := by
  rw [← tensorD_eq_dTgt, ← tensorD_eq_dTgt]
  exact tensorD_tensorD (singFreeCx X) (singFreeCx X) k y

/-! ## 3. The singular complex of a model, as a chain complex -/

/-- The mod-2 singular chain complex, as a `ChainComplex` over `ModuleCat`. -/
noncomputable def bdCx (X : TopCat.{0}) : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ :=
  ChainComplex.of (fun k => ModuleCat.of (ZMod 2) (singularSimplices X k →₀ ZMod 2))
    (fun k => ModuleCat.ofHom (bdU (ZMod 2) X k))
    (fun k => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro u
      exact bdU_bdU (ZMod 2) X k u)

theorem bdCx_d (X : TopCat.{0}) (k : ℕ) :
    (bdCx X).d (k + 1) k = ModuleCat.ofHom (bdU (ZMod 2) X k) := by
  simp [bdCx]

theorem bdCx_ker_le_range (n : ℕ) (k : ℕ) :
    LinearMap.ker ((bdCx (stdSimplexTop n)).d (k + 1) k).hom
      ≤ LinearMap.range ((bdCx (stdSimplexTop n)).d (k + 2) (k + 1)).hom := by
  intro y hy
  have hy' : bdU (ZMod 2) (stdSimplexTop n) k y = 0 := by
    rw [LinearMap.mem_ker, bdCx_d] at hy
    exact hy
  obtain ⟨z, hz⟩ := bdU_exists_preimage_stdSimplexTop n k y hy'
  refine ⟨z, ?_⟩
  rw [bdCx_d]
  exact hz

/-! ## 4. The augmented contraction of a model -/

/-- The contracting operator of a model. -/
noncomputable def singS (n k : ℕ) :
    (singularSimplices (stdSimplexTop n) k →₀ ZMod 2) →ₗ[ZMod 2]
      (singularSimplices (stdSimplexTop n) (k + 1) →₀ ZMod 2) :=
  splitHom (bdCx (stdSimplexTop n)) k

/-- The degree-zero residue of a model. -/
noncomputable def singPi (n : ℕ) :
    (singularSimplices (stdSimplexTop n) 0 →₀ ZMod 2) →ₗ[ZMod 2]
      (singularSimplices (stdSimplexTop n) 0 →₀ ZMod 2) :=
  complProj (bdCx (stdSimplexTop n)) 0

theorem singS_succ (n k : ℕ)
    (u : singularSimplices (stdSimplexTop n) (k + 1) →₀ ZMod 2) :
    bdU (ZMod 2) (stdSimplexTop n) (k + 1) (singS n (k + 1) u)
      + singS n k (bdU (ZMod 2) (stdSimplexTop n) k u) = u := by
  have h := splitHom_comm (bdCx (stdSimplexTop n)) (bdCx_ker_le_range n) k u
  rw [bdCx_d, bdCx_d] at h
  exact h

theorem singS_zero (n : ℕ) (u : singularSimplices (stdSimplexTop n) 0 →₀ ZMod 2) :
    bdU (ZMod 2) (stdSimplexTop n) 0 (singS n 0 u) = u + singPi n u := by
  have h := d_splitHom (bdCx (stdSimplexTop n)) (bdCx_ker_le_range n) 0 u
  rw [bdCx_d] at h
  have h2 := eq_add_of_add_eq_zmod2 (bdryProj_add_complProj (bdCx (stdSimplexTop n)) 0 u)
  exact h.trans h2

theorem singPi_bdU (n : ℕ) (u : singularSimplices (stdSimplexTop n) 1 →₀ ZMod 2) :
    singPi n (bdU (ZMod 2) (stdSimplexTop n) 0 u) = 0 := by
  refine complProj_of_mem_range (bdCx (stdSimplexTop n)) 0 ⟨u, ?_⟩
  rw [bdCx_d]
  rfl

/-- **An augmented contraction of the singular complex of a standard simplex.** -/
noncomputable def singAug (n : ℕ) : AugContraction (singFreeCx (stdSimplexTop n)) where
  s k := singS n k
  π := singPi n
  succ k u := singS_succ n k u
  zero u := singS_zero n u
  pi_d u := singPi_bdU n u

/-! ## 5. Acyclicity of the pair complex on the models -/

/-- **The pair complex is acyclic on the models**: over a standard simplex every
positive-degree cycle for `cc-steenrod`'s differential is a boundary. -/
theorem dTgt_exists_preimage_stdSimplexTop (n k : ℕ)
    (y : Steenrod.PairIdx (stdSimplexTop n) (k + 1) →₀ ZMod 2)
    (hy : Steenrod.dTgt (stdSimplexTop n) (ZMod 2) k y = 0) :
    ∃ z : Steenrod.PairIdx (stdSimplexTop n) (k + 2) →₀ ZMod 2,
      Steenrod.dTgt (stdSimplexTop n) (ZMod 2) (k + 1) z = y := by
  have hy' : tensorD (singFreeCx (stdSimplexTop n)) (singFreeCx (stdSimplexTop n)) k y = 0 := by
    rw [tensorD_eq_dTgt]
    exact hy
  obtain ⟨z, hz⟩ := tensorD_exists_preimage (singAug n) (singAug n) k y hy'
  refine ⟨z, ?_⟩
  rw [← tensorD_eq_dTgt]
  exact hz

end

end GroupApproximation.CharClass
