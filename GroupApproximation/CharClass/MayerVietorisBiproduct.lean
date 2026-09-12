import GroupApproximation.CharClass.CohomologyMayerVietoris
import GroupApproximation.CharClass.ThomEulerNaturality

/-!
# The middle term of cohomological Mayer–Vietoris, as a sum of two pieces

`CharClass/CohomologyMayerVietoris.lean` dualizes the vendored degreewise-split
chain-level Mayer–Vietoris sequence and produces the short exact sequence of
cochain complexes

```text
0 → C^*_{U,V}(X) → C^*(U) ⊕ C^*(V) → C^*(U ∩ V) → 0
```

as `mvCoSCOf`, with the two outer terms identified, the connecting map, and
exactness at all three spots.  What it does *not* do is say that the middle term
is a sum of the two pieces, and that is exactly what the element-level long exact
sequence needs: the statement "an element of the middle term is zero iff both of
its components are", and the two component maps.

This file supplies that, without ever constructing an isomorphism onto a
biproduct.  All that is used is the four biproduct identities of
`C_*(U) ⊞ C_*(V)`, carried through the additive dualizing functor and then
through `homologyMap`:

```text
jU ≫ qU = 𝟙,   jV ≫ qV = 𝟙,   jU ≫ qV = 0,   jV ≫ qU = 0,
qU ≫ jU + qV ≫ jV = 𝟙.
```

Note the reversal: `dualMapOf` is contravariant, so the chain-level *inclusion*
`biprod.inl` dualizes to the *projection* `qU`, and `biprod.fst` to the inclusion
`jU`.

## The coefficient parameter

**Nothing in §2–§4 below uses characteristic two.**  The whole development is
`biprod.total` carried through an additive functor and then through
`homologyMap`, so it is a plain substitution: the generic declarations carry an
`Of` suffix and take the coefficient explicitly (their other arguments are opens
and degrees, which determine nothing), and the `F₂` names are `abbrev`s and
restatements at `K = ZMod 2`.

§1 is different.  It collects the facts about `F₂`-modules that make signs
invisible, because the chain-level Mayer–Vietoris map `biprod.lift ι (-ι')`
carries a minus sign which the mod-2 tree absorbs rather than carries.  Those
four lemmas are **used only by each other and by consumers of this file**, never
by the biproduct argument, so they stay exactly as they are.  Over a general
coefficient field the consumers do not need generic analogues of them: the
replacements are Mathlib's `sub_self` and `sub_eq_zero`, and the sign moves into
the definition of the middle-term class (`inclU a - inclV b` rather than
`inclU a + inclV b`).  Adding `sub`-flavoured twins here would be an unused
abstraction, so this file does not.

## Main results

* `mvHProjUOf`, `mvHProjVOf`, `mvHInclUOf`, `mvHInclVOf` — the four maps on the
  homology of the middle term, over any coefficient field.
* `mvH_decomposeOf` — `jU ≫ qU + jV ≫ qV = 𝟙` on homology, in element form,
  which is where "zero iff both components are zero" (`mvH_eq_zero_iffOf`) comes
  from.
* `mvHProjU`, `mvH_decompose`, … — the `F₂` instances, with the names the rest of
  the tree already uses.
-/

namespace GroupApproximation.CharClass

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

variable {X : TopCat.{0}}

/-! ## 1. Signs are invisible over `F₂`

These four are a service for the consumers of this file, not part of the
biproduct argument below.  Over a general field their role is played by
`sub_self` and `sub_eq_zero`. -/

/-- In a module over `ZMod 2` every element is its own additive inverse. -/
theorem add_self_eq_zero_two {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (x : M) :
    x + x = 0 := by
  have hs : ((1 : ZMod 2) + 1) = 0 := by decide
  have h : ((1 : ZMod 2) + 1) • x = (1 : ZMod 2) • x + (1 : ZMod 2) • x := add_smul _ _ _
  rw [hs, zero_smul, one_smul] at h
  exact h.symm

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

/-! ## 2. Contravariant functoriality of the dualization

`Functor.map_id` and friends must be written out: with `open CategoryTheory` in scope
the bare names can still resolve to the *monadic* `Functor` class, whose `map_id` is
`(Functor.map id) = id` and whose rewrite pattern is `fun x => id <$> x`.

The coefficient here is **implicit**: every one of these has a complex or a chain
map among its arguments, which determines it. -/

theorem mvDualMapOf_comp {K : Type} [CommRing K] {C D E : ChainComplex (ModuleCat.{0} K) ℕ}
    (f : C ⟶ D) (g : D ⟶ E) : dualMapOf K g ≫ dualMapOf K f = dualMapOf K (f ≫ g) := by
  show (dualCxFunctorOf K).map g.op ≫ (dualCxFunctorOf K).map f.op
      = (dualCxFunctorOf K).map (f ≫ g).op
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.op_comp]

theorem mvDualMapOf_id {K : Type} [CommRing K] (C : ChainComplex (ModuleCat.{0} K) ℕ) :
    dualMapOf K (𝟙 C) = 𝟙 (dualCxOf K C) := by
  show (dualCxFunctorOf K).map (𝟙 C).op = 𝟙 _
  rw [CategoryTheory.op_id, CategoryTheory.Functor.map_id]

theorem mvDualMapOf_add {K : Type} [CommRing K] {C D : ChainComplex (ModuleCat.{0} K) ℕ}
    (f g : C ⟶ D) : dualMapOf K (f + g) = dualMapOf K f + dualMapOf K g := by
  show (dualCxFunctorOf K).map (f + g).op = _
  rw [CategoryTheory.op_add, CategoryTheory.Functor.map_add]

theorem mvDualMapOf_zero {K : Type} [CommRing K] {C D : ChainComplex (ModuleCat.{0} K) ℕ} :
    dualMapOf K (0 : C ⟶ D) = 0 := by
  have h := mvDualMapOf_add (0 : C ⟶ D) 0
  rw [add_zero] at h
  have h3 : (0 : dualCxOf K D ⟶ dualCxOf K C) + dualMapOf K (0 : C ⟶ D)
      = dualMapOf K (0 : C ⟶ D) + dualMapOf K (0 : C ⟶ D) := by rw [zero_add, ← h]
  exact ((add_left_inj (dualMapOf K (0 : C ⟶ D))).mp h3).symm

/-- The `F₂` restatement, in the vocabulary the four consumers use.  Stated
separately rather than left to reducibility: `rw` matching a lemma about
`dualMapOf K` against a goal about `dualMap2` would rely on the `abbrev`
unfolding during keyed matching, and that is not worth risking in four files. -/
theorem mvDualMap_comp {C D E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : C ⟶ D) (g : D ⟶ E) : dualMap2 g ≫ dualMap2 f = dualMap2 (f ≫ g) :=
  mvDualMapOf_comp f g

/-! ## 3. The two pieces of the cover, and the four maps -/

/-- The subordinate-chain complex of an open of the cover. -/
abbrev mvCxOf (K : Type) [CommRing K] (U : Opens X) : ChainComplex (ModuleCat.{0} K) ℕ :=
  subChainComplex K X (U : Set X)

/-- The `U`-component of the dual of `C_*(U) ⊞ C_*(V)` (the dual of `biprod.inl`). -/
def mvCxProjUOf (K : Type) [CommRing K] (U V : Opens X) :
    dualCxOf K (mvCxOf K U ⊞ mvCxOf K V) ⟶ dualCxOf K (mvCxOf K U) :=
  dualMapOf K (biprod.inl (X := mvCxOf K U) (Y := mvCxOf K V))

/-- The `V`-component of the dual of `C_*(U) ⊞ C_*(V)`. -/
def mvCxProjVOf (K : Type) [CommRing K] (U V : Opens X) :
    dualCxOf K (mvCxOf K U ⊞ mvCxOf K V) ⟶ dualCxOf K (mvCxOf K V) :=
  dualMapOf K (biprod.inr (X := mvCxOf K U) (Y := mvCxOf K V))

/-- The `U`-inclusion into the dual of `C_*(U) ⊞ C_*(V)` (the dual of `biprod.fst`). -/
def mvCxInclUOf (K : Type) [CommRing K] (U V : Opens X) :
    dualCxOf K (mvCxOf K U) ⟶ dualCxOf K (mvCxOf K U ⊞ mvCxOf K V) :=
  dualMapOf K (biprod.fst (X := mvCxOf K U) (Y := mvCxOf K V))

/-- The `V`-inclusion into the dual of `C_*(U) ⊞ C_*(V)`. -/
def mvCxInclVOf (K : Type) [CommRing K] (U V : Opens X) :
    dualCxOf K (mvCxOf K V) ⟶ dualCxOf K (mvCxOf K U ⊞ mvCxOf K V) :=
  dualMapOf K (biprod.snd (X := mvCxOf K U) (Y := mvCxOf K V))

theorem mvCxInclUOf_projU (K : Type) [CommRing K] (U V : Opens X) :
    mvCxInclUOf K U V ≫ mvCxProjUOf K U V = 𝟙 (dualCxOf K (mvCxOf K U)) := by
  rw [mvCxInclUOf, mvCxProjUOf, mvDualMapOf_comp, biprod.inl_fst, mvDualMapOf_id]

theorem mvCxInclVOf_projV (K : Type) [CommRing K] (U V : Opens X) :
    mvCxInclVOf K U V ≫ mvCxProjVOf K U V = 𝟙 (dualCxOf K (mvCxOf K V)) := by
  rw [mvCxInclVOf, mvCxProjVOf, mvDualMapOf_comp, biprod.inr_snd, mvDualMapOf_id]

theorem mvCxInclUOf_projV (K : Type) [CommRing K] (U V : Opens X) :
    mvCxInclUOf K U V ≫ mvCxProjVOf K U V = 0 := by
  rw [mvCxInclUOf, mvCxProjVOf, mvDualMapOf_comp, biprod.inr_fst, mvDualMapOf_zero]

theorem mvCxInclVOf_projU (K : Type) [CommRing K] (U V : Opens X) :
    mvCxInclVOf K U V ≫ mvCxProjUOf K U V = 0 := by
  rw [mvCxInclVOf, mvCxProjUOf, mvDualMapOf_comp, biprod.inl_snd, mvDualMapOf_zero]

/-- **The middle term is the sum of its two pieces**, at the level of cochain
complexes: `biprod.total` carried through the additive dualizing functor. -/
theorem mvCxOf_total (K : Type) [CommRing K] (U V : Opens X) :
    mvCxProjUOf K U V ≫ mvCxInclUOf K U V + mvCxProjVOf K U V ≫ mvCxInclVOf K U V
      = 𝟙 (dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)) := by
  rw [mvCxProjUOf, mvCxInclUOf, mvCxProjVOf, mvCxInclVOf, mvDualMapOf_comp, mvDualMapOf_comp,
    ← mvDualMapOf_add, biprod.total, mvDualMapOf_id]

/-! ## 4. The same four maps on homology -/

/-- The `U`-component on the homology of the middle term. -/
def mvHProjUOf (K : Type) [CommRing K] (U V : Opens X) (n : ℕ) :
    (dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).homology n ⟶ (dualCxOf K (mvCxOf K U)).homology n :=
  HomologicalComplex.homologyMap (mvCxProjUOf K U V) n

/-- The `V`-component on the homology of the middle term. -/
def mvHProjVOf (K : Type) [CommRing K] (U V : Opens X) (n : ℕ) :
    (dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).homology n ⟶ (dualCxOf K (mvCxOf K V)).homology n :=
  HomologicalComplex.homologyMap (mvCxProjVOf K U V) n

/-- The `U`-inclusion on the homology of the middle term. -/
def mvHInclUOf (K : Type) [CommRing K] (U V : Opens X) (n : ℕ) :
    (dualCxOf K (mvCxOf K U)).homology n ⟶ (dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).homology n :=
  HomologicalComplex.homologyMap (mvCxInclUOf K U V) n

/-- The `V`-inclusion on the homology of the middle term. -/
def mvHInclVOf (K : Type) [CommRing K] (U V : Opens X) (n : ℕ) :
    (dualCxOf K (mvCxOf K V)).homology n ⟶ (dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).homology n :=
  HomologicalComplex.homologyMap (mvCxInclVOf K U V) n

theorem mvH_inclU_projUOf (K : Type) [CommRing K] (U V : Opens X) (n : ℕ)
    (x : (dualCxOf K (mvCxOf K U)).homology n) :
    (mvHProjUOf K U V n).hom ((mvHInclUOf K U V n).hom x) = x := by
  refine hom_apply_of_comp_eq_id ?_ x
  rw [mvHInclUOf, mvHProjUOf, ← HomologicalComplex.homologyMap_comp, mvCxInclUOf_projU,
    HomologicalComplex.homologyMap_id]

theorem mvH_inclV_projVOf (K : Type) [CommRing K] (U V : Opens X) (n : ℕ)
    (x : (dualCxOf K (mvCxOf K V)).homology n) :
    (mvHProjVOf K U V n).hom ((mvHInclVOf K U V n).hom x) = x := by
  refine hom_apply_of_comp_eq_id ?_ x
  rw [mvHInclVOf, mvHProjVOf, ← HomologicalComplex.homologyMap_comp, mvCxInclVOf_projV,
    HomologicalComplex.homologyMap_id]

theorem mvH_inclU_projVOf (K : Type) [CommRing K] (U V : Opens X) (n : ℕ)
    (x : (dualCxOf K (mvCxOf K U)).homology n) :
    (mvHProjVOf K U V n).hom ((mvHInclUOf K U V n).hom x) = 0 := by
  have h : mvHInclUOf K U V n ≫ mvHProjVOf K U V n = 0 := by
    rw [mvHInclUOf, mvHProjVOf, ← HomologicalComplex.homologyMap_comp, mvCxInclUOf_projV,
      HomologicalComplex.homologyMap_zero]
  have := hom_apply_of_comp_eq h x
  rw [this]; rfl

theorem mvH_inclV_projUOf (K : Type) [CommRing K] (U V : Opens X) (n : ℕ)
    (x : (dualCxOf K (mvCxOf K V)).homology n) :
    (mvHProjUOf K U V n).hom ((mvHInclVOf K U V n).hom x) = 0 := by
  have h : mvHInclVOf K U V n ≫ mvHProjUOf K U V n = 0 := by
    rw [mvHInclVOf, mvHProjUOf, ← HomologicalComplex.homologyMap_comp, mvCxInclVOf_projU,
      HomologicalComplex.homologyMap_zero]
  have := hom_apply_of_comp_eq h x
  rw [this]; rfl

/-- **Every class in the middle term is the sum of its two components.** -/
theorem mvH_decomposeOf (K : Type) [CommRing K] (U V : Opens X) (n : ℕ)
    (m : (dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).homology n) :
    (mvHInclUOf K U V n).hom ((mvHProjUOf K U V n).hom m)
      + (mvHInclVOf K U V n).hom ((mvHProjVOf K U V n).hom m) = m := by
  have h : mvHProjUOf K U V n ≫ mvHInclUOf K U V n + mvHProjVOf K U V n ≫ mvHInclVOf K U V n
      = 𝟙 ((dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).homology n) := by
    rw [mvHProjUOf, mvHInclUOf, mvHProjVOf, mvHInclVOf, ← HomologicalComplex.homologyMap_comp,
      ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_add,
      mvCxOf_total, HomologicalComplex.homologyMap_id]
  have h2 := congrArg (fun f : (dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).homology n
      ⟶ (dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).homology n => f.hom m) h
  simpa using h2

/-- **A class in the middle term vanishes iff both of its components do.**  This is the
only consequence of the biproduct structure that the long exact sequence needs. -/
theorem mvH_eq_zero_iffOf (K : Type) [CommRing K] (U V : Opens X) (n : ℕ)
    (m : (dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).homology n) :
    m = 0 ↔ (mvHProjUOf K U V n).hom m = 0 ∧ (mvHProjVOf K U V n).hom m = 0 := by
  constructor
  · rintro rfl
    exact ⟨map_zero _, map_zero _⟩
  · rintro ⟨hU, hV⟩
    rw [← mvH_decomposeOf K U V n m, hU, hV, map_zero, map_zero, add_zero]

/-! ## 5. The `F₂` instance -/

/-- The subordinate-chain complex of an open of the cover, over `F₂`. -/
abbrev mvCx (U : Opens X) : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ := mvCxOf (ZMod 2) U

abbrev mvCxProjU (U V : Opens X) : dualCx2 (mvCx U ⊞ mvCx V) ⟶ dualCx2 (mvCx U) :=
  mvCxProjUOf (ZMod 2) U V

abbrev mvCxProjV (U V : Opens X) : dualCx2 (mvCx U ⊞ mvCx V) ⟶ dualCx2 (mvCx V) :=
  mvCxProjVOf (ZMod 2) U V

abbrev mvCxInclU (U V : Opens X) : dualCx2 (mvCx U) ⟶ dualCx2 (mvCx U ⊞ mvCx V) :=
  mvCxInclUOf (ZMod 2) U V

abbrev mvCxInclV (U V : Opens X) : dualCx2 (mvCx V) ⟶ dualCx2 (mvCx U ⊞ mvCx V) :=
  mvCxInclVOf (ZMod 2) U V

theorem mvCxInclU_projU (U V : Opens X) :
    mvCxInclU U V ≫ mvCxProjU U V = 𝟙 (dualCx2 (mvCx U)) :=
  mvCxInclUOf_projU (ZMod 2) U V

theorem mvCxInclV_projV (U V : Opens X) :
    mvCxInclV U V ≫ mvCxProjV U V = 𝟙 (dualCx2 (mvCx V)) :=
  mvCxInclVOf_projV (ZMod 2) U V

theorem mvCxInclU_projV (U V : Opens X) : mvCxInclU U V ≫ mvCxProjV U V = 0 :=
  mvCxInclUOf_projV (ZMod 2) U V

theorem mvCxInclV_projU (U V : Opens X) : mvCxInclV U V ≫ mvCxProjU U V = 0 :=
  mvCxInclVOf_projU (ZMod 2) U V

theorem mvCx_total (U V : Opens X) :
    mvCxProjU U V ≫ mvCxInclU U V + mvCxProjV U V ≫ mvCxInclV U V
      = 𝟙 (dualCx2 (mvCx U ⊞ mvCx V)) :=
  mvCxOf_total (ZMod 2) U V

abbrev mvHProjU (U V : Opens X) (n : ℕ) :
    (dualCx2 (mvCx U ⊞ mvCx V)).homology n ⟶ (dualCx2 (mvCx U)).homology n :=
  mvHProjUOf (ZMod 2) U V n

abbrev mvHProjV (U V : Opens X) (n : ℕ) :
    (dualCx2 (mvCx U ⊞ mvCx V)).homology n ⟶ (dualCx2 (mvCx V)).homology n :=
  mvHProjVOf (ZMod 2) U V n

abbrev mvHInclU (U V : Opens X) (n : ℕ) :
    (dualCx2 (mvCx U)).homology n ⟶ (dualCx2 (mvCx U ⊞ mvCx V)).homology n :=
  mvHInclUOf (ZMod 2) U V n

abbrev mvHInclV (U V : Opens X) (n : ℕ) :
    (dualCx2 (mvCx V)).homology n ⟶ (dualCx2 (mvCx U ⊞ mvCx V)).homology n :=
  mvHInclVOf (ZMod 2) U V n

theorem mvH_inclU_projU (U V : Opens X) (n : ℕ) (x : (dualCx2 (mvCx U)).homology n) :
    (mvHProjU U V n).hom ((mvHInclU U V n).hom x) = x :=
  mvH_inclU_projUOf (ZMod 2) U V n x

theorem mvH_inclV_projV (U V : Opens X) (n : ℕ) (x : (dualCx2 (mvCx V)).homology n) :
    (mvHProjV U V n).hom ((mvHInclV U V n).hom x) = x :=
  mvH_inclV_projVOf (ZMod 2) U V n x

theorem mvH_inclU_projV (U V : Opens X) (n : ℕ) (x : (dualCx2 (mvCx U)).homology n) :
    (mvHProjV U V n).hom ((mvHInclU U V n).hom x) = 0 :=
  mvH_inclU_projVOf (ZMod 2) U V n x

theorem mvH_inclV_projU (U V : Opens X) (n : ℕ) (x : (dualCx2 (mvCx V)).homology n) :
    (mvHProjU U V n).hom ((mvHInclV U V n).hom x) = 0 :=
  mvH_inclV_projUOf (ZMod 2) U V n x

/-- **Every class in the middle term is the sum of its two components** (`F₂`). -/
theorem mvH_decompose (U V : Opens X) (n : ℕ) (m : (dualCx2 (mvCx U ⊞ mvCx V)).homology n) :
    (mvHInclU U V n).hom ((mvHProjU U V n).hom m)
      + (mvHInclV U V n).hom ((mvHProjV U V n).hom m) = m :=
  mvH_decomposeOf (ZMod 2) U V n m

/-- **A class in the middle term vanishes iff both of its components do** (`F₂`). -/
theorem mvH_eq_zero_iff (U V : Opens X) (n : ℕ)
    (m : (dualCx2 (mvCx U ⊞ mvCx V)).homology n) :
    m = 0 ↔ (mvHProjU U V n).hom m = 0 ∧ (mvHProjV U V n).hom m = 0 :=
  mvH_eq_zero_iffOf (ZMod 2) U V n m

end

end GroupApproximation.CharClass
