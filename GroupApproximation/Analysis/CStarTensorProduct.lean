import GroupApproximation.Analysis.CStarTensorProductConcrete
import GroupApproximation.Analysis.CStarTensorProductAlgebra

/-!
# The minimal (spatial) tensor product of C⋆-algebras: entry point and roadmap

## The gap this addresses

`non_mf_groups_exist.tex` makes two operator-algebraic assertions that are not
merely unproved in this development but **unstatable** at the pinned Mathlib
revision:

* the reduced group C⋆-algebra of the witness group is **exact** --- located by
  `The algebra is also exact, by the block normal form of` beneath
  `\ref{thm:reduced}`, and again by `The same decomposition also proves that
  $E$ is exact` inside `\ref{sec:algebras-sofic}` --- and
* a certain algebra is **not nuclear**, located by `whence` … `is not nuclear
  \cite{Lance}` (Lance's theorem).

Both notions are defined through the minimal tensor product `⊗_min`, and
Mathlib has no C⋆-tensor product of any kind.  The string `nuclear` does not
occur anywhere in Mathlib at the pinned revision `905b9581`
(`git grep -i nuclear` returns nothing), and neither does any C⋆-norm on a
tensor product.

This module is the entry point for the missing foundation.  It imports the
layers that are complete and records what remains.

## What Mathlib *does* have (verified against the pinned revision)

An earlier survey in this directory understated this substantially, so the
facts are recorded with file references:

* `Mathlib/Algebra/Star/TensorProduct.lean` --- `Star (A ⊗[R] B)` with
  `@[simp] star_tmul : star (x ⊗ₜ y) = star x ⊗ₜ star y := rfl`, plus
  `InvolutiveStar`, `StarAddMonoid`, `StarModule R (A ⊗[R] B)`.
* `Mathlib/RingTheory/TensorProduct/Basic.lean` --- `Semiring`, `Ring`,
  `Algebra R (A ⊗[R] B)`, and --- in the `Algebra.TensorProduct` namespace of
  that file, found by `git grep -n 'StarRing (A ⊗' ` --- the `StarMul` and
  `StarRing (A ⊗[R] B)` instances.
  **The ⋆-algebra `A ⊙ B` therefore costs nothing.**
* `Mathlib/RingTheory/TensorProduct/Maps.lean` --- `Algebra.TensorProduct.lift`,
  the universal property for a pair of algebra maps with commuting ranges.
* `Mathlib/Analysis/InnerProductSpace/TensorProduct.lean` --- the inner product
  space structure on the *algebraic* `E ⊗[𝕜] F`, with `inner_tmul`,
  `norm_tmul : ‖x ⊗ₜ y‖ = ‖x‖ * ‖y‖`, `ContinuousLinearMap.rTensor`/`lTensor`
  (with `rTensor_mul`, `lTensor_mul`), `TensorProduct.mapL` and
  `norm_mapL_le : ‖mapL f g‖ ≤ ‖f‖ * ‖g‖`, and the isometry API.  No
  finite-dimensionality is assumed.
* `Mathlib/Analysis/InnerProductSpace/Completion.lean` --- `InnerProductSpace 𝕜
  (Completion E)`, so a genuine Hilbert-space tensor product `H ⊗̂ K` *is*
  assemblable as `Completion (H ⊗[ℂ] K)`.
* `Mathlib/Analysis/Normed/Module/Completion.lean` --- `NormedRing
  (Completion A)` for a seminormed ring `A`.
* `Mathlib/Analysis/CStarAlgebra/Hom.lean` --- `NonUnitalStarAlgHom.norm_map`:
  an injective ⋆-homomorphism of C⋆-algebras is isometric.

## What this development adds

* `CStarTensorProductAdjointable.lean` --- the adjointable bounded operators on
  a complex inner product space, and the **C⋆-identity** `‖T⋆T‖ = ‖T‖²` proved
  with **no completeness assumption**, together with closure of adjointability
  under `0, 1, +, -, •, ∘`.
* `CStarTensorProductSeminorm.lean` --- `IsCStarSeminorm` / `IsCStarNorm`
  (star-invariance derived, not assumed), `StarRep`, and the theorem that the
  operator seminorm of a ⋆-representation by adjointable operators is a
  C⋆-seminorm --- a C⋆-norm when the representation is faithful.
* `CStarTensorProductSpatial.lean` --- `isAdjoint_mapL` (the adjoint of
  `S ⊗ T` is `S⋆ ⊗ T⋆`), **`norm_mapL : ‖mapL S T‖ = ‖S‖ * ‖T‖`** (Mathlib
  has only `≤`), the product representation `π ⊗ ρ` of `A ⊗[ℂ] B` on
  `H ⊗[ℂ] K` built from `Algebra.TensorProduct.lift`, and hence the **spatial
  norm relative to a fixed pair of representations, fully proved to be a
  C⋆-seminorm** and a C⋆-norm when faithful.
* `CStarTensorProductConcrete.lean` --- `StarRep.ofStarAlgHom` (every
  ⋆-homomorphism into `B(H)` for Hilbert `H` is a `StarRep`, so the theory is
  not vacuous and covers the concretely represented algebras of this
  repository), and the **cross-norm property** `‖a ⊗ₜ b‖ = ‖a‖ * ‖b‖`.

### The design decision that made this reachable

The textbook construction completes `H ⊗ K` to a Hilbert space first.  **That
completion is not needed to define the norm.**  The C⋆-identity
`‖T‖² = ‖T⋆T‖` follows from Cauchy--Schwarz and the definition of the operator
norm alone; completeness, the Riesz representation theorem, and the existence
of adjoints play no part.  So the entire spatial construction is carried out on
the *algebraic* tensor product `H ⊗[ℂ] K`, which Mathlib already makes an inner
product space.  Completion re-enters only at the very last step, to turn the
C⋆-normed ⋆-algebra `A ⊙ B` into a C⋆-algebra.

Mathlib's `InnerProductSpace 𝕜 (Completion E)` means the completed route is
*also* available; it was not taken because it is strictly more work for the
same norm --- one would have to transport every operator through the
completion --- and because the pre-Hilbert statement is the more general one.

## Roadmap: what is left, in dependency order

Estimates are for a from-scratch Mathlib-quality build, revised against what
the pinned revision actually contains.

### Stage A --- faithfulness of `π ⊗ ρ` on all of `A ⊙ B`  --- **DONE**

`CStarTensorProductSpatial.spatialHom_injective`, with the unconditional
corollary `spatialNorm_isCStarNorm`.

**This stage was mis-costed here, and the mis-costing is instructive.**  The
estimate above read: "one needs the **slice maps**: for a state `ψ` on `B`, the
map `R_ψ : A ⊙ B → A` with `R_ψ (a ⊗ b) = ψ(b) • a`, and its *continuity* for
the spatial norm.  Requires states on a C⋆-algebra and the fact that they
separate points ... *~800 lines*."

Continuity of slice maps, and hence states and GNS, is what **Takesaki's
theorem** needs --- Stage C.  Mere injectivity of `π ⊗ ρ` on the *algebraic*
tensor product needs none of it.  The vector functionals `a ↦ ⟪ξ', π a ξ⟫`
already separate the points of `A` as soon as `π.hom` is injective (take
`ξ' = π a ξ`; the pairing is `‖π a ξ‖²`), and separation plus a Hamel basis on
one factor suffices.  The whole thing is algebra: no states, no GNS, no
continuity, no completeness.  It came to roughly a third of the estimate.

The lesson generalises: an estimate inherited from the textbook route can cost
the wrong thing entirely.  Before budgeting a stage here, check what the step
actually needs rather than what the standard proof of the *neighbouring* step
needs.

### Stage B --- completion of a C⋆-normed ⋆-algebra  --- **DONE**

Every item that stood here is built and in the root import closure:
`Analysis/CStarCompletion.lean` supplies `Star`, `StarRing`,
`NormedStarGroup`, the C⋆-identity, the noncommutative `Algebra ℂ` and
`NormedAlgebra ℂ`, `StarModule`, and the assembled
`CStarAlgebra (Completion A)`; `Analysis/CStarNormBundled.lean` retags an
algebra along a C⋆-norm (`WithCStarNorm`) and packages the chain as
`completionCStarAlgebraOfIsCStarNorm`; `Analysis/CStarCompletionCoe.lean` and
`Analysis/CStarCompletionHom.lean` give the canonical arrow into the
completion and the extension of ⋆-homomorphisms across it.

`Analysis/CStarTensorProductAlgebra.lean` (imported above) joins Stages A and
B: `SpatialTensorProduct π ρ hπ hρ` is `A ⊗_{π,ρ} B` as an honest
C⋆-algebra, with the algebraic tensor product isometrically and densely
embedded by `spatialTensorIn`, and the cross-seminorm value
`‖a ⊗ₜ b‖ = ‖π.hom a‖ * ‖ρ.hom b‖` on elementary tensors.

### Stage C --- independence of the representations (Takesaki)  (research scale)

This is the theorem that makes `⊗_min` canonical, and the only reason the
construction above is still indexed by `(π, ρ)`.  Route: states and GNS
(C.1); the universal representation as a Hilbert direct sum of GNS
representations, and its faithfulness (C.2); slice maps from Stage A (C.3);
the independence theorem itself (C.4).  *~3000--5000 lines.*

Note an alternative that yields a canonical norm without C.4: define the
minimal norm as a supremum over a *set* of representations manufactured from
states.  The pointwise supremum of a bounded family of C⋆-seminorms is a
C⋆-seminorm --- squaring is monotone on `[0, ∞)`, so the C⋆-identity survives
the supremum --- so this is cheap.  It does not remove the theorem: identifying
that supremum with the norm computed from *one* faithful pair is still C.4.

### Stage D --- what the manuscript actually cites  (out of reach)

Quotients of C⋆-algebras by closed two-sided ideals (needed even to *state*
exactness; Mathlib's `Ideal.Quotient.normedCommRing` is commutative-only and
the quotient C⋆-identity needs an approximate unit, for which Mathlib does
have `CStarAlgebra/ApproximateUnit.lean`); the definition of exactness;
nuclearity and the completely positive approximation property; Lance's
theorem; Kirchberg's `exact ↔ nuclearly embeddable`; Ozawa's
`property A → Cred(G) exact`; Guentner--Higson--Weinberger for linear groups.
The last four are research-scale formalizations that no proof assistant
library has approached.  See `CStarExactness.lean` and
`ExactnessPermanence.lean` for the accounting of those rows.

## Honest verdict

Stages A and B are done and joined: `A ⊗_{π,ρ} B` is an honest C⋆-algebra
with a faithful cross-norm (`CStarTensorProductAlgebra.lean`).  Stage C is a
research-scale project on its own,
and until it is done the minimal tensor product cannot be written `⊗_min`
without lying about canonicity.  Stage D is out of reach.

Therefore **C⋆-exactness remains out of reach for this development**, and the
correct form of the manuscript's exactness row is the one it already uses: an
explicit statement that the formal library has no definition of exact
C⋆-algebras.  What has changed is the size of the hole: the vocabulary needed
to *state* a C⋆-tensor norm now exists and needs no literature input.

**Do not read "exists" as "checked."**  An earlier version of this paragraph
claimed the vocabulary "is machine-checked".  That was false when written:
`CStarTensorProductSeminorm`, `Spatial`, `Concrete` and this module were not in
the import closure of `GroupApproximation.lean`, so `lake build` had never
elaborated them and no audit had ever seen them.  Only
`CStarTensorProductAdjointable.lean` --- the base layer, carrying `IsAdjoint`
and the C⋆-identity --- was root-imported and hence genuinely verified.  A
declaration written in an orphan module is a claim, not a theorem.  Whether the
rest of this lane is checked is decided by one thing only: whether these module
names appear in `GroupApproximation.lean`.  Check there before relying on
anything below.

## Manuscript status

`EXACT`: none --- no manuscript step is certified by this lane.
`MISSING`: the exactness assertion and the nuclearity assertion, for the
reasons above.  Both are located by the strings quoted at the top of this
docstring.  (Two earlier versions of this block located them by line number and
both had drifted by the time anyone read them; the paragraph they cited has
since been retitled as well.  Cite manuscript passages by a `\label` or by
their own words, never by line number.)
-/

namespace GroupApproximation
namespace CStarTensor

/-! This module is an entry point: it re-exports the completed layers and
carries the roadmap above.  No declarations are made here. -/

end CStarTensor
end GroupApproximation
