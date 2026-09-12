import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.Covering
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.Monodromy
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SingularHomologyFunctorAPI
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Lifting singular simplices through the double cover `Sⁿ → RPⁿ`

This file builds the first genuine ingredient of the mod-2 transfer for the double
cover `proj n : Sphere n → RP n`: a reusable API saying that a **singular simplex**
in `RP n` lifts to `Sphere n` once a lift of one chosen vertex is selected, and
that this lift is unique.

## The simplex domain

Mathlib's singular simplicial set `TopCat.toSSet.obj X` has, in degree `k`,
`(toSSet.obj X).obj (op ⦋k⦌) ≃ C(stdSimplex ℝ (Fin (k+1)), X)`
(`TopCat.toSSetObjEquiv`). The relevant geometric simplex domain is therefore the
standard simplex `stdSimplex ℝ (Fin (k+1))`, which we name `TopologicalSimplex k`.
It is a nonempty **convex** subset of `Fin (k+1) → ℝ`, hence contractible (so
simply connected) and locally path connected — exactly the hypotheses of the
covering-space lifting theorem.

## Main declarations

* `TopologicalSimplex k` — the standard topological `k`-simplex, with the derived
  `LocPathConnectedSpace`, `ContractibleSpace`, `SimplyConnectedSpace` instances.
* `projLiftSimplex σ v₀ e he` — the canonical lift of a singular simplex
  `σ : C(TopologicalSimplex k, RP n)` through `proj n`, pinned by the choice of a
  fiber point `e : Sphere n` over the chosen vertex value `σ v₀`.
* `projLiftSimplex_lifts` — `proj n ∘ liftSimplex = σ`.
* `projLiftSimplex_vertex` — `liftSimplex v₀ = e`.
* `projLiftSimplex_unique` — any two lifts of the same simplex agreeing at `v₀`
  coincide.
* `projLiftSimplex_comp` — naturality under precomposition by a continuous map of
  simplices (the face/degeneracy compatibility, in its general precomposition
  form): the lift of `σ ∘ g` is the lift of `σ` precomposed with `g`.
* `projLiftSimplex_antipodal` — the *other* lift (over the second fiber point
  `-e`) is the antipode of the first; this records that the two sheets of the
  double cover give the two lifts, the input the mod-2 chain transfer of Prompt 03
  will sum over.

The whole construction rests on Mathlib's
`IsCoveringMap.existsUnique_continuousMap_lifts` together with the project's
`proj_isCoveringMap`. No transfer map is defined here.
-/

noncomputable section

open CategoryTheory Simplicial

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-! ## 1. The topological simplex and its connectivity instances -/

/-- The standard topological `k`-simplex, the domain of singular `k`-simplices:
the nonempty convex set `stdSimplex ℝ (Fin (k+1)) ⊆ (Fin (k+1) → ℝ)`. Mathlib's
singular simplices `(TopCat.toSSet.obj X).obj (op ⦋k⦌)` identify with
`C(TopologicalSimplex k, X)` via `TopCat.toSSetObjEquiv`. -/
abbrev TopologicalSimplex (k : ℕ) : Type := stdSimplex ℝ (Fin (k + 1))

/-- The topological simplex is locally path connected (it is convex in a locally
convex space). -/
instance topologicalSimplex_locPathConnected (k : ℕ) :
    LocallyPathConnectedSpace (TopologicalSimplex k) :=
  Convex.locallyPathConnectedSpace _ (convex_stdSimplex ℝ (Fin (k + 1)))

/-- The topological simplex is contractible (it is nonempty and convex). -/
instance topologicalSimplex_contractible (k : ℕ) :
    ContractibleSpace (TopologicalSimplex k) :=
  Convex.contractibleSpace (convex_stdSimplex ℝ (Fin (k + 1))) Set.Nonempty.of_subtype

/-- The topological simplex is simply connected (being contractible). -/
instance topologicalSimplex_simplyConnected (k : ℕ) :
    SimplyConnectedSpace (TopologicalSimplex k) :=
  SimplyConnectedSpace.ofContractible _

/-! ## 2. The canonical lift of a singular simplex -/

/-- **The canonical lift of a singular simplex through the double cover.** Given a
singular simplex `σ : C(TopologicalSimplex k, RP n)`, a chosen vertex
`v₀ : TopologicalSimplex k`, and a fiber point `e : Sphere n` over the vertex
value (`proj n e = σ v₀`), this is the unique continuous lift
`TopologicalSimplex k → Sphere n` of `σ` sending `v₀` to `e`.

It exists and is unique because the topological simplex is simply connected and
locally path connected (`IsCoveringMap.existsUnique_continuousMap_lifts` applied
to the covering map `proj_isCoveringMap n`). -/
def projLiftSimplex {n k : ℕ} (σ : C(TopologicalSimplex k, RP n))
    (v₀ : TopologicalSimplex k) (e : Sphere n) (he : proj n e = σ v₀) :
    C(TopologicalSimplex k, Sphere n) :=
  ((proj_isCoveringMap n).existsUnique_continuousMap_lifts σ v₀ e he).choose

/-- `projLiftSimplex` is a lift of `σ`: composing with `proj n` recovers `σ`. -/
theorem projLiftSimplex_lifts {n k : ℕ} (σ : C(TopologicalSimplex k, RP n))
    (v₀ : TopologicalSimplex k) (e : Sphere n) (he : proj n e = σ v₀) :
    proj n ∘ (projLiftSimplex σ v₀ e he) = σ :=
  ((proj_isCoveringMap n).existsUnique_continuousMap_lifts σ v₀ e he).choose_spec.1.2

/-- `projLiftSimplex` sends the chosen vertex `v₀` to the chosen fiber point `e`. -/
theorem projLiftSimplex_vertex {n k : ℕ} (σ : C(TopologicalSimplex k, RP n))
    (v₀ : TopologicalSimplex k) (e : Sphere n) (he : proj n e = σ v₀) :
    projLiftSimplex σ v₀ e he v₀ = e :=
  ((proj_isCoveringMap n).existsUnique_continuousMap_lifts σ v₀ e he).choose_spec.1.1

/-- Pointwise form of `projLiftSimplex_lifts`: `proj n (lift x) = σ x`. -/
@[simp] theorem projLiftSimplex_lifts_apply {n k : ℕ} (σ : C(TopologicalSimplex k, RP n))
    (v₀ : TopologicalSimplex k) (e : Sphere n) (he : proj n e = σ v₀)
    (x : TopologicalSimplex k) :
    proj n (projLiftSimplex σ v₀ e he x) = σ x :=
  congrFun (projLiftSimplex_lifts σ v₀ e he) x

/-- **Uniqueness of the lift.** Any two continuous lifts of the same singular
simplex `σ` that agree at the chosen vertex `v₀` are equal. -/
theorem projLiftSimplex_unique {n k : ℕ} (σ : C(TopologicalSimplex k, RP n))
    (v₀ : TopologicalSimplex k) (e : Sphere n) (he : proj n e = σ v₀)
    {τ₁ τ₂ : C(TopologicalSimplex k, Sphere n)}
    (h1 : proj n ∘ τ₁ = σ) (h2 : proj n ∘ τ₂ = σ)
    (h10 : τ₁ v₀ = e) (h20 : τ₂ v₀ = e) : τ₁ = τ₂ :=
  ((proj_isCoveringMap n).existsUnique_continuousMap_lifts σ v₀ e he).unique
    ⟨h10, h1⟩ ⟨h20, h2⟩

/-- A continuous lift of `σ` agreeing with the canonical lift at `v₀` *is* the
canonical lift. -/
theorem eq_projLiftSimplex {n k : ℕ} (σ : C(TopologicalSimplex k, RP n))
    (v₀ : TopologicalSimplex k) (e : Sphere n) (he : proj n e = σ v₀)
    {τ : C(TopologicalSimplex k, Sphere n)}
    (hτ : proj n ∘ τ = σ) (hτ0 : τ v₀ = e) : τ = projLiftSimplex σ v₀ e he :=
  projLiftSimplex_unique σ v₀ e he hτ (projLiftSimplex_lifts σ v₀ e he) hτ0
    (projLiftSimplex_vertex σ v₀ e he)

/-! ## 3. Naturality under precomposition (face/degeneracy compatibility) -/

/-- **Precomposition compatibility of the lift.** For a continuous map of simplices
`g : C(TopologicalSimplex j, TopologicalSimplex k)` carrying a chosen vertex `w₀`
to `v₀`, the canonical lift of the precomposed simplex `σ ∘ g` (pinned at `w₀` by
the same fiber point `e`) is the canonical lift of `σ` precomposed with `g`:

```text
liftSimplex (σ ∘ g) w₀ e  =  (liftSimplex σ v₀ e) ∘ g.
```

Specialized to a face map `g` this is the face compatibility of the lift; it is
the form Prompt 03 needs to check that the chain-level transfer commutes with the
simplicial face maps. -/
theorem projLiftSimplex_comp {n k j : ℕ} (σ : C(TopologicalSimplex k, RP n))
    (v₀ : TopologicalSimplex k) (e : Sphere n) (he : proj n e = σ v₀)
    (g : C(TopologicalSimplex j, TopologicalSimplex k)) (w₀ : TopologicalSimplex j)
    (hg : g w₀ = v₀) :
    projLiftSimplex (σ.comp g) w₀ e (by rw [ContinuousMap.comp_apply, hg]; exact he)
      = (projLiftSimplex σ v₀ e he).comp g := by
  refine projLiftSimplex_unique (σ.comp g) w₀ e
    (by rw [ContinuousMap.comp_apply, hg]; exact he)
    (projLiftSimplex_lifts _ _ _ _) ?_ (projLiftSimplex_vertex _ _ _ _) ?_
  · ext x
    have hx := congrFun (projLiftSimplex_lifts σ v₀ e he) (g x)
    simpa [Function.comp] using hx
  · rw [ContinuousMap.comp_apply, hg, projLiftSimplex_vertex]

/-! ## 4. The two sheets: the other lift is the antipode -/

/-- **The second lift is the antipode of the first.** The fiber of the double
cover over `σ v₀` is `{e, -e}`. Lifting `σ` over the second fiber point `-e`
yields the antipode of the lift over `e`:

```text
liftSimplex σ v₀ (-e)  =  antipodal n ∘ (liftSimplex σ v₀ e).
```

This records that the two sheets of the cover give exactly the two lifts of a
singular simplex; the mod-2 chain transfer of Prompt 03 sums over them. -/
theorem projLiftSimplex_antipodal {n k : ℕ} (σ : C(TopologicalSimplex k, RP n))
    (v₀ : TopologicalSimplex k) (e : Sphere n) (he : proj n e = σ v₀) :
    projLiftSimplex σ v₀ (-e) ((proj_neg e).trans he)
      = (antipodal n).comp (projLiftSimplex σ v₀ e he) := by
  refine (eq_projLiftSimplex σ v₀ (-e) ((proj_neg e).trans he) ?_ ?_).symm
  · ext x
    rw [Function.comp_apply, ContinuousMap.comp_apply, proj_antipodal]
    exact congrFun (projLiftSimplex_lifts σ v₀ e he) x
  · rw [ContinuousMap.comp_apply, projLiftSimplex_vertex, antipodal_apply]

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
