import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CoveringSimplexLift
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SingularCohomology

/-!
# The mod-2 transfer of the double cover `Sⁿ → RPⁿ` on singular chains

This file defines the **chain-level mod-2 transfer** for the double cover
`proj n : Sphere n → RP n` with `ZMod 2` coefficients, degreewise on singular
chains. It is the genuine (Route A) construction: a singular `k`-simplex of
`RP n` is sent to the formal sum of its **two** lifts to `Sphere n`.

This is the next ingredient after the simplex-lifting API of
`CoveringSimplexLift.lean`. It defines the transfer on the chain groups and
records its additivity / linearity. **Boundary compatibility is not addressed
here** (that is the next step); nothing in this file claims the transfer commutes
with the differential.

## The singular chain groups

For `X : TopCat` and `k : ℕ`, Mathlib's degree-`k` singular chain group with
coefficients in `M : ModuleCat (ZMod 2)` is, by construction
(`singularChainComplexFunctor`, `sigmaConst`),
**definitionally** the coproduct
```text
(((singularChainComplexFunctor (ModuleCat (ZMod 2))).obj M).obj X).X k
  = ∐ fun _ : (TopCat.toSSet.obj X).obj (op ⦋k⦌) => M
```
of one copy of `M` per singular `k`-simplex of `X`, where the singular
`k`-simplices `(TopCat.toSSet.obj X).obj (op ⦋k⦌)` identify with
`C(TopologicalSimplex k, X)` via `TopCat.toSSetObjEquiv`. We use this coproduct
structure directly: maps **out of** the chain group are built with
`Limits.Sigma.desc`, and the basis simplices are the coproduct injections
`Limits.Sigma.ι`. This is the actual chain-group type supplied by Mathlib, not a
re-modelled free module.

## Main declarations

* `singularChainZMod2 X k` — abbreviation for the degree-`k` mod-2 singular chain
  group of `X` (a `ModuleCat (ZMod 2)` object).
* `projTransferOnSimplex n k σ` — the transfer of a single singular `k`-simplex
  `σ` of `RP n`: the morphism `M ⟶ C_k(Sⁿ; F₂)` sending the generator to the sum
  of the coproduct injections of the two lifts `projLiftSimplex σ … e` and
  `projLiftSimplex σ … (-e)` (over the two fiber points `e`, `-e`).
* `projTransferChainDegree n k : C_k(RPⁿ; F₂) ⟶ C_k(Sⁿ; F₂)` — the degreewise
  transfer, the linear extension `Limits.Sigma.desc (projTransferOnSimplex n k)`.
* `projTransferChainDegree_ι` — the defining property: precomposing with the
  coproduct injection of a simplex `σ` recovers `projTransferOnSimplex n k σ`.
* `projTransferChainDegree_add`, `projTransferChainDegree_smul` — additivity and
  `ZMod 2`-linearity (immediate, since the transfer is a `ModuleCat` morphism,
  i.e. a bundled linear map).

## Choice of fiber point

For each simplex `σ` we must pick a fiber point `e` over the value of `σ` at a
chosen vertex `v₀`. The fiber over any point is the two-element set `{e, -e}`
(`proj_fiber_eq`, `proj_fiber_ncard_eq_two`); picking either one and summing both
lifts gives the same chain, because over the second fiber point `-e` the lift is
the antipode of the lift over `e` (`projLiftSimplex_antipodal`), so the two
summands merely swap. We make the (immaterial) choice with
`proj_surjective n`; the resulting transfer is therefore well defined as written.
-/

noncomputable section

open CategoryTheory AlgebraicTopology Limits

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- The mod-2 coefficient module `ZMod 2` as a `ModuleCat (ZMod 2)` object. -/
abbrev transferCoeff : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ZMod 2)

/-- The degree-`k` mod-2 singular chain group of a space `X`, as a
`ModuleCat (ZMod 2)` object. By construction this is definitionally the coproduct
`∐ fun _ : (TopCat.toSSet.obj X).obj (op ⦋k⦌) => ZMod 2` of one copy of the
coefficients per singular `k`-simplex of `X`. -/
abbrev singularChainZMod2 (X : TopCat.{0}) (k : ℕ) : ModuleCat.{0} (ZMod 2) :=
  (((singularChainComplexFunctor (ModuleCat.{0} (ZMod 2))).obj transferCoeff).obj X).X k

/-- The type of singular `k`-simplices of `X` (the index set of the coproduct
defining `singularChainZMod2 X k`). It identifies with `C(TopologicalSimplex k, X)`
via `TopCat.toSSetObjEquiv`. -/
abbrev singularSimplexIndex (X : TopCat.{0}) (k : ℕ) : Type :=
  (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk k))

/-- **The mod-2 transfer of a single singular simplex.** Given a singular
`k`-simplex `σ` of `RP n`, view it as a continuous map
`σc : C(TopologicalSimplex k, RP n)`, choose a vertex `v₀` and a fiber point `e`
over `σc v₀`, and form the **two** lifts `τ₁ = projLiftSimplex σc v₀ e` and
`τ₂ = projLiftSimplex σc v₀ (-e)` of `σ` to `Sphere n`. The transfer of `σ` is the
morphism `ZMod 2 ⟶ C_k(Sⁿ; F₂)` sending the generator to the sum of the coproduct
injections of `τ₁` and `τ₂`.

This is the degreewise generator-level part of the transfer; the linear extension
to all chains is `projTransferChainDegree`. -/
def projTransferOnSimplex (n k : ℕ) (σ : singularSimplexIndex (TopCat.of (RP n)) k) :
    transferCoeff ⟶ singularChainZMod2 (TopCat.of (Sphere n)) k :=
  let σc : C(TopologicalSimplex k, RP n) := TopCat.toSSetObjEquiv _ _ σ
  let v₀ : TopologicalSimplex k := Classical.arbitrary _
  let e : Sphere n := (proj_surjective n (σc v₀)).choose
  let he : proj n e = σc v₀ := (proj_surjective n (σc v₀)).choose_spec
  let τ₁ : C(TopologicalSimplex k, Sphere n) := projLiftSimplex σc v₀ e he
  let τ₂ : C(TopologicalSimplex k, Sphere n) :=
    projLiftSimplex σc v₀ (-e) ((proj_neg e).trans he)
  Sigma.ι (fun _ : singularSimplexIndex (TopCat.of (Sphere n)) k => transferCoeff)
      ((TopCat.toSSetObjEquiv _ _).symm τ₁)
    + Sigma.ι (fun _ : singularSimplexIndex (TopCat.of (Sphere n)) k => transferCoeff)
      ((TopCat.toSSetObjEquiv _ _).symm τ₂)

/-- **The degreewise mod-2 transfer on singular chains.** The linear extension of
`projTransferOnSimplex` to the whole chain group, obtained from the universal
property of the coproduct (`Limits.Sigma.desc`). It is a genuine `ModuleCat
(ZMod 2)` morphism
```text
projTransferChainDegree n k : C_k(RPⁿ; F₂) ⟶ C_k(Sⁿ; F₂),
```
hence automatically additive and `ZMod 2`-linear. -/
def projTransferChainDegree (n k : ℕ) :
    singularChainZMod2 (TopCat.of (RP n)) k ⟶ singularChainZMod2 (TopCat.of (Sphere n)) k :=
  Sigma.desc (projTransferOnSimplex n k)

/-- **Defining property of the transfer.** Precomposing the transfer with the
coproduct injection of a singular simplex `σ` recovers the per-simplex transfer
`projTransferOnSimplex n k σ`. This is the basis-level characterisation that the
boundary-compatibility step will read on each simplex. -/
@[simp] theorem projTransferChainDegree_ι (n k : ℕ)
    (σ : singularSimplexIndex (TopCat.of (RP n)) k) :
    Sigma.ι (fun _ : singularSimplexIndex (TopCat.of (RP n)) k => transferCoeff) σ
        ≫ projTransferChainDegree n k
      = projTransferOnSimplex n k σ :=
  Sigma.ι_desc _ _

/-- Additivity of the degreewise transfer (it is a linear map). -/
@[simp] theorem projTransferChainDegree_add (n k : ℕ)
    (x y : singularChainZMod2 (TopCat.of (RP n)) k) :
    (projTransferChainDegree n k).hom (x + y)
      = (projTransferChainDegree n k).hom x + (projTransferChainDegree n k).hom y :=
  map_add _ _ _

/-- `ZMod 2`-linearity (homogeneity) of the degreewise transfer. -/
@[simp] theorem projTransferChainDegree_smul (n k : ℕ) (c : ZMod 2)
    (x : singularChainZMod2 (TopCat.of (RP n)) k) :
    (projTransferChainDegree n k).hom (c • x) = c • (projTransferChainDegree n k).hom x :=
  map_smul _ _ _

/-- The transfer sends `0` to `0` (it is a linear map). -/
@[simp] theorem projTransferChainDegree_zero (n k : ℕ) :
    (projTransferChainDegree n k).hom 0 = 0 :=
  map_zero _

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
