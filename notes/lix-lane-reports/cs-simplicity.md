# cs-simplicity

Owns `Analysis/CStarSimple.lean`, `Analysis/LIXSimplicity.lean`,
`Analysis/LIXSimplicityInstance*.lean`.

## 1. GREEN

*(nothing recorded yet; probe round 1 in flight)*

## 2. AUTHORED, UNVERIFIED

* `Analysis/CStarSimple.lean` — **new**.  `IsSimpleCStar (A : Type u) [CStarAlgebra A]`,
  `IsSimpleCStar.eq_bot_or_eq_top`, `IsSimpleCStar.eq_top_of_mem`,
  `IsSimpleCStar.of_starAlgEquiv`, `isSimpleCStar_iff_isSimpleRing`, plus the instance
  `GroupApproximation.isTwoSided_closure` (the closure of a two-sided ideal of a topological
  ring is two-sided).  Not yet wired into the root — **the lead must add
  `import GroupApproximation.Analysis.CStarSimple`**; nothing imports it yet except
  `LIXSimplicity`.
* `Analysis/LIXSimplicity.lean` — rewritten (see TRAPS 1).  `posCut`, `sqrtPosCut`, `resCut`,
  `invCut`; `cfc_mem_of_isClosed`; `IsFull`, `IsFullIn`, `IsFullIn.isFull`,
  `isFullIn_of_sum_eq_one`, `isFull_of_sum_eq_one`, `one_mem_of_isFull`;
  `mem_of_mul_self_le` (closed two-sided ideals are hereditary); `exists_ge_nonneg_mem_approx`;
  `exists_ge_mem_ideal_of_nonneg`; `eq_top_of_stagewise_full`;
  `isSimpleCStar_of_stagewise_full`.

## 3. NEEDS

### For `cs-endpoint`: the definition, exactly as asked

```lean
-- GroupApproximation/Analysis/CStarSimple.lean
namespace GroupApproximation
def IsSimpleCStar (A : Type u) [CStarAlgebra A] : Prop :=
  ∀ I : Ideal A, I.IsTwoSided → IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤
```

Instance arguments are `[CStarAlgebra A]` and nothing else — no order, no `Nontrivial`.
Universe-polymorphic.  `I.IsTwoSided` is an explicit hypothesis rather than an instance binder so
that `intro I hI hclosed` needs no `haveI` gymnastics at the use site; supply it with
`inferInstance` when the instance is around, and `IsSimpleCStar.eq_bot_or_eq_top` /
`IsSimpleCStar.eq_top_of_mem` take it as an instance for convenience.

### From `cs-limit` — the limit algebra as an increasing union

```lean
def LIXLimit : Type
instance : CStarAlgebra LIXLimit
instance : Nontrivial LIXLimit
def lixStage : ℕ → StarSubalgebra ℂ LIXLimit          -- image of ι_i, i.e. `(ι i).range`
theorem lixStage_isClosed : ∀ i, IsClosed (lixStage i : Set LIXLimit)
theorem lixStage_mono : Monotone lixStage
theorem lixStage_dense : Dense (⋃ i, (lixStage i : Set LIXLimit))
```

`StarSubalgebra ℂ LIXLimit`, **not** a bare `Set`, and closed: `cfc_mem_of_isClosed` needs the
subalgebra to be a C⋆-algebra in its own right (`StarSubalgebra.cstarAlgebra`, which fires off an
`IsClosed` instance).  `Monotone` for `ℕ` with its `SemilatticeSup`; any `SemilatticeSup` index
works.

### From `cs-stages` — fullness, in either of two shapes

```lean
theorem lixStage_full (k : ℕ) (a : LIXLimit) (ha : a ∈ lixStage k) (h0 : 0 ≤ a) (hne : a ≠ 0) :
    ∃ j, k ≤ j ∧ GroupApproximation.LIX.IsFullIn (lixStage j) a
```

`IsFullIn T a` is the concrete statement "for every `ε > 0` there are finitely many `xᵢ, yᵢ ∈ T`
with `‖1 - ∑ xᵢ a yᵢ‖ < ε`"; `isFullIn_of_sum_eq_one` builds it from an exact identity
`∑ xᵢ a yᵢ = 1`, which is what "a section nonzero in every fibre of a matrix bundle generates the
whole corner" actually produces (partition of unity + local inverses, no limit needed).  If it is
easier to produce fullness in the *ambient* limit, `IsFull a` alone feeds
`eq_top_of_stagewise_full` directly.

**Order instances.**  `0 ≤ a` needs `[PartialOrder LIXLimit] [StarOrderedRing LIXLimit]`.  I take
them as instance hypotheses; the instantiation file will install
`CStarAlgebra.spectralOrder` / `CStarAlgebra.spectralOrderedRing` as local instances, exactly as
`Analysis/LIXEndpointStatement.lean` does.  **`cs-limit` must not register a competing
`PartialOrder` instance on the limit algebra**, or the two orders diamond.

## 4. TRAPS

1. **The manuscript's quotient route is unavailable in this repo, and `LIXSimplicity` as
   inherited was written against it.**  The inherited file called `quotientStarMk`,
   `continuous_quotientStarMk`, `cfc` on `B ⧸ I` and `spectrum ℝ (quotientStarMk I a)`.  But
   `Analysis/CStarIdealQuotient` says in its own module docstring that the **C⋆-identity for the
   quotient norm is not proved** — the quotient is a complete normed ⋆-algebra and nothing more —
   so there is no `ContinuousFunctionalCalculus` on `B ⧸ I` and none of those lines can
   elaborate.  It also carried `[IsStarStable I]`, which `IsSimpleCStar` does not, so even a
   green version would not have instantiated the endpoint.  Replaced by an argument that never
   leaves `B`: `d (a - ε) d = c c` with `d = cfc (√ ∘ (·-ε)₊) a`, then `c c ≤ d b d ∈ I`, then
   heredity of closed two-sided ideals (`mem_of_mul_self_le`).  This also drops the manuscript's
   `1/8` slack: cutting at exactly the approximation error works.
2. **Heredity without an approximate unit.**  `0 ≤ s`, `s s ≤ v ∈ I ⟹ s ∈ I` is proved with the
   resolvent `r_δ = δ (v + δ)⁻¹` *written as a functional calculus of `v`*
   (`resCut δ t = δ / (max t 0 + δ)`), never as an inverse: then `1 - r_δ = v · invCut δ (v)` is
   visibly in the left ideal, and `‖s r_δ‖² = ‖r_δ (s s) r_δ‖ ≤ ‖r_δ v r_δ‖ ≤ δ` by the C⋆-identity
   plus the scalar bound `δ² t/(t+δ)² ≤ δ`.  The `max t 0` in the denominator is what makes the
   function continuous on all of `ℝ`, so no `ContinuousOn`-side-condition bookkeeping is needed;
   on the spectrum of a positive element it is the honest `δ/(t+δ)`.
3. **`Ideal.closure` is only a left ideal in Mathlib.**  `Ideal.closure` (Topology/Algebra/Ring/
   Ideal.lean) proves `smul_mem'` and nothing else, so `I.closure.IsTwoSided` has to be supplied;
   it is one line with `mulRight_continuous` in place of Mathlib's `mulLeft_continuous`.  Without
   it `isSimpleCStar_iff_isSimpleRing` cannot even be stated on the closure.
