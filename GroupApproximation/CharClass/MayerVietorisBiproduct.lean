import GroupApproximation.CharClass.MayerVietorisDual
import GroupApproximation.CharClass.ThomEulerNaturality

/-!
# The middle term of cohomological Mayer–Vietoris, as a sum of two pieces

`cc-cohom-api`'s `CharClass/CohomologyMayerVietoris.lean` dualizes the vendored
degreewise-split chain-level Mayer–Vietoris sequence and produces the short exact
sequence of cochain complexes

```text
0 → C^*_{U,V}(X) → C^*(U) ⊕ C^*(V) → C^*(U ∩ V) → 0
```

as `mvCoSC`, with the two outer terms identified (`mvAmbientIso`, `mvInterIso`), the
connecting map `mvDelta`, and exactness at all three spots.  What it does *not* do is
say that the middle term is a sum of the two pieces, and that is exactly what the
element-level long exact sequence needs: the statement "an element of the middle term
is zero iff both of its components are", and the two component maps.

This file supplies that, without ever constructing an isomorphism onto a biproduct.
All that is used is the four biproduct identities of `C_*(U) ⊞ C_*(V)`, carried
through the additive dualizing functor and then through `homologyMap`:

```text
jU ≫ qU = 𝟙,   jV ≫ qV = 𝟙,   jU ≫ qV = 0,   jV ≫ qU = 0,
qU ≫ jU + qV ≫ jV = 𝟙.
```

Note the reversal: `coMap` is contravariant, so the chain-level *inclusion*
`biprod.inl` dualizes to the *projection* `qU`, and `biprod.fst` to the inclusion `jU`.

The file also collects the two facts about `F₂`-modules that make signs invisible
(`neg_eq_self_two`, `eq_of_add_eq_zero_two`); the chain-level Mayer–Vietoris map
`biprod.lift ι (-ι')` carries a minus sign which must be absorbed before the
restrictions can be called restrictions.

## Main results

* `mvHProjU`, `mvHProjV`, `mvHInclU`, `mvHInclV` — the four maps on the homology of
  the middle term.
* `mvH_total` — `jU ≫ qU + jV ≫ qV = 𝟙` on homology, in element form
  (`mvH_decompose`), which is where "zero iff both components are zero" comes from.
-/

namespace GroupApproximation.CharClass

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.CharClass.MV

noncomputable section

variable {X : TopCat.{0}}

/-! ## 1. Signs are invisible over `F₂` -/

/-- In a module over `ZMod 2` every element is its own additive inverse. -/
theorem add_self_eq_zero_two {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (x : M) :
    x + x = 0 := by
  have h : ((1 : ZMod 2) + 1) • x = (1 : ZMod 2) • x + (1 : ZMod 2) • x := add_smul _ _ _
  simpa using h.symm

theorem neg_eq_self_two {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (x : M) : -x = x := by
  have h := add_self_eq_zero_two x
  have h2 : -x + (x + x) = -x + 0 := by rw [h]
  rw [← add_assoc, neg_add_cancel, zero_add, add_zero] at h2
  exact h2.symm

/-- Over `F₂`, `x + y = 0` says `x = y`. -/
theorem eq_of_add_eq_zero_two {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {x y : M}
    (h : x + y = 0) : x = y := by
  have h2 : x + y + y = 0 + y := by rw [h]
  rw [add_assoc, add_self_eq_zero_two, add_zero, zero_add] at h2
  exact h2

/-- Over `F₂`, `x = y` says `x + y = 0`. -/
theorem add_eq_zero_two {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {x y : M}
    (h : x = y) : x + y = 0 := by
  rw [h]; exact add_self_eq_zero_two y

/-! ## 3. The two pieces of the cover, and the four maps -/

/-- The subordinate-chain complex of an open of the cover. -/
abbrev mvCx (U : Opens X) : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ :=
  subChainComplex (ZMod 2) X (U : Set X)

/-- The `U`-component of the dual of `C_*(U) ⊞ C_*(V)` (the dual of `biprod.inl`). -/
def mvCxProjU (U V : Opens X) : coCx (mvCx U ⊞ mvCx V) ⟶ coCx (mvCx U) :=
  coMap (biprod.inl (X := mvCx U) (Y := mvCx V))

/-- The `V`-component of the dual of `C_*(U) ⊞ C_*(V)`. -/
def mvCxProjV (U V : Opens X) : coCx (mvCx U ⊞ mvCx V) ⟶ coCx (mvCx V) :=
  coMap (biprod.inr (X := mvCx U) (Y := mvCx V))

/-- The `U`-inclusion into the dual of `C_*(U) ⊞ C_*(V)` (the dual of `biprod.fst`). -/
def mvCxInclU (U V : Opens X) : coCx (mvCx U) ⟶ coCx (mvCx U ⊞ mvCx V) :=
  coMap (biprod.fst (X := mvCx U) (Y := mvCx V))

/-- The `V`-inclusion into the dual of `C_*(U) ⊞ C_*(V)`. -/
def mvCxInclV (U V : Opens X) : coCx (mvCx V) ⟶ coCx (mvCx U ⊞ mvCx V) :=
  coMap (biprod.snd (X := mvCx U) (Y := mvCx V))

theorem mvCxInclU_projU (U V : Opens X) :
    mvCxInclU U V ≫ mvCxProjU U V = 𝟙 (coCx (mvCx U)) := by
  rw [mvCxInclU, mvCxProjU, coMap_comp, biprod.inl_fst, coMap_id]

theorem mvCxInclV_projV (U V : Opens X) :
    mvCxInclV U V ≫ mvCxProjV U V = 𝟙 (coCx (mvCx V)) := by
  rw [mvCxInclV, mvCxProjV, coMap_comp, biprod.inr_snd, coMap_id]

theorem mvCxInclU_projV (U V : Opens X) : mvCxInclU U V ≫ mvCxProjV U V = 0 := by
  rw [mvCxInclU, mvCxProjV, coMap_comp, biprod.inr_fst, coMap_zero]

theorem mvCxInclV_projU (U V : Opens X) : mvCxInclV U V ≫ mvCxProjU U V = 0 := by
  rw [mvCxInclV, mvCxProjU, coMap_comp, biprod.inl_snd, coMap_zero]

/-- **The middle term is the sum of its two pieces**, at the level of cochain
complexes: `biprod.total` carried through the additive dualizing functor. -/
theorem mvCx_total (U V : Opens X) :
    mvCxProjU U V ≫ mvCxInclU U V + mvCxProjV U V ≫ mvCxInclV U V
      = 𝟙 (coCx (mvCx U ⊞ mvCx V)) := by
  rw [mvCxProjU, mvCxInclU, mvCxProjV, mvCxInclV, coMap_comp, coMap_comp,
    ← coMap_add, biprod.total, coMap_id]

/-! ## 4. The same four maps on homology -/

/-- The `U`-component on the homology of the middle term. -/
def mvHProjU (U V : Opens X) (n : ℕ) :
    (coCx (mvCx U ⊞ mvCx V)).homology n ⟶ (coCx (mvCx U)).homology n :=
  HomologicalComplex.homologyMap (mvCxProjU U V) n

/-- The `V`-component on the homology of the middle term. -/
def mvHProjV (U V : Opens X) (n : ℕ) :
    (coCx (mvCx U ⊞ mvCx V)).homology n ⟶ (coCx (mvCx V)).homology n :=
  HomologicalComplex.homologyMap (mvCxProjV U V) n

/-- The `U`-inclusion on the homology of the middle term. -/
def mvHInclU (U V : Opens X) (n : ℕ) :
    (coCx (mvCx U)).homology n ⟶ (coCx (mvCx U ⊞ mvCx V)).homology n :=
  HomologicalComplex.homologyMap (mvCxInclU U V) n

/-- The `V`-inclusion on the homology of the middle term. -/
def mvHInclV (U V : Opens X) (n : ℕ) :
    (coCx (mvCx V)).homology n ⟶ (coCx (mvCx U ⊞ mvCx V)).homology n :=
  HomologicalComplex.homologyMap (mvCxInclV U V) n

theorem mvH_inclU_projU (U V : Opens X) (n : ℕ) (x : (coCx (mvCx U)).homology n) :
    (mvHProjU U V n).hom ((mvHInclU U V n).hom x) = x := by
  refine hom_apply_of_comp_eq_id ?_ x
  rw [mvHInclU, mvHProjU, ← HomologicalComplex.homologyMap_comp, mvCxInclU_projU,
    HomologicalComplex.homologyMap_id]

theorem mvH_inclV_projV (U V : Opens X) (n : ℕ) (x : (coCx (mvCx V)).homology n) :
    (mvHProjV U V n).hom ((mvHInclV U V n).hom x) = x := by
  refine hom_apply_of_comp_eq_id ?_ x
  rw [mvHInclV, mvHProjV, ← HomologicalComplex.homologyMap_comp, mvCxInclV_projV,
    HomologicalComplex.homologyMap_id]

theorem mvH_inclU_projV (U V : Opens X) (n : ℕ) (x : (coCx (mvCx U)).homology n) :
    (mvHProjV U V n).hom ((mvHInclU U V n).hom x) = 0 := by
  have h : mvHInclU U V n ≫ mvHProjV U V n = 0 := by
    rw [mvHInclU, mvHProjV, ← HomologicalComplex.homologyMap_comp, mvCxInclU_projV,
      HomologicalComplex.homologyMap_zero]
  have := hom_apply_of_comp_eq h x
  rw [this]; rfl

theorem mvH_inclV_projU (U V : Opens X) (n : ℕ) (x : (coCx (mvCx V)).homology n) :
    (mvHProjU U V n).hom ((mvHInclV U V n).hom x) = 0 := by
  have h : mvHInclV U V n ≫ mvHProjU U V n = 0 := by
    rw [mvHInclV, mvHProjU, ← HomologicalComplex.homologyMap_comp, mvCxInclV_projU,
      HomologicalComplex.homologyMap_zero]
  have := hom_apply_of_comp_eq h x
  rw [this]; rfl

/-- **Every class in the middle term is the sum of its two components.** -/
theorem mvH_decompose (U V : Opens X) (n : ℕ) (m : (coCx (mvCx U ⊞ mvCx V)).homology n) :
    (mvHInclU U V n).hom ((mvHProjU U V n).hom m)
      + (mvHInclV U V n).hom ((mvHProjV U V n).hom m) = m := by
  have h : mvHProjU U V n ≫ mvHInclU U V n + mvHProjV U V n ≫ mvHInclV U V n
      = 𝟙 ((coCx (mvCx U ⊞ mvCx V)).homology n) := by
    rw [mvHProjU, mvHInclU, mvHProjV, mvHInclV, ← HomologicalComplex.homologyMap_comp,
      ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_add,
      mvCx_total, HomologicalComplex.homologyMap_id]
  have h2 := congrArg (fun f : (coCx (mvCx U ⊞ mvCx V)).homology n
      ⟶ (coCx (mvCx U ⊞ mvCx V)).homology n => f.hom m) h
  simpa using h2

/-- **A class in the middle term vanishes iff both of its components do.**  This is the
only consequence of the biproduct structure that the long exact sequence needs. -/
theorem mvH_eq_zero_iff (U V : Opens X) (n : ℕ)
    (m : (coCx (mvCx U ⊞ mvCx V)).homology n) :
    m = 0 ↔ (mvHProjU U V n).hom m = 0 ∧ (mvHProjV U V n).hom m = 0 := by
  constructor
  · rintro rfl
    exact ⟨map_zero _, map_zero _⟩
  · rintro ⟨hU, hV⟩
    rw [← mvH_decompose U V n m, hU, hV, map_zero, map_zero, add_zero]

end

end GroupApproximation.CharClass
