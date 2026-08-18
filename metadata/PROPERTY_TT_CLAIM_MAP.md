# Property `(TT)/T` paper claim map

This file is the publication gate for the property `(TT)/T` paper. A result may
appear as a numbered theorem in the manuscript only when it has one exact
paper-facing Lean declaration below. The mathematical statement in the
manuscript must have exactly the declaration's hypotheses and conclusion. The
written proof may use a shorter independently valid argument from the
literature, with the source credited explicitly. Formalization itself is not
claimed as mathematical novelty.

## Analytic input: strong relative root control

Let `X` be finite and let `G = E₄((Z/2Z)⟨X⟩)`. Every Hilbert-space
quasi-cocycle on `G`, for every unitary representation, is bounded on the
elementary root subgroup `X₀₃`. No assumption excluding invariant vectors is
imposed.

Exact Lean declaration:

```text
GroupApproximation.PropertyTTPaper.freeCharacteristicTwo_root_hasRelativeTT
```

Proof declaration:

```text
GroupApproximation.PropertyTT.RankFourRelativeTT.hasRelativeTT_X03
```

The localized Fourier estimate used by that proof is exposed as:

```text
GroupApproximation.PropertyTTPaper.freeCharacteristicTwo_localizedPlaneEstimate
GroupApproximation.PropertyTTPaper.freeCharacteristicTwo_planeEnergyEstimate
GroupApproximation.PropertyTTPaper.freeCharacteristicTwo_rowEmbedding_controlRoot
GroupApproximation.PropertyTTPaper.freeCharacteristicTwo_inverseTranspose_root
GroupApproximation.PropertyTTPaper.freeCharacteristicTwo_rowEmbedding_elementaryRoot
```

Credit boundary: relative `(TT)/T` for noncommutative universal lattices is
already present in Mimura's work. In characteristic two, the displayed full
relative `(TT)` statement is also a short consequence at theorem level:
Mimura controls the no-invariant-vector summand on a coordinate block, while
the globally invariant summand is bounded on the root because every root
element has order two. The paper may present the internal quantitative
rank-four argument as an independent proof and explicit estimate, but must
not claim novelty for the bare relative theorem.

## Theorem A: coordinate-block factorization

Let `R` be a nontrivial ring such that every nonzero `a` admits `x, y` with
`x * a * y = 1`. If `2 ≤ n`, every element of `GLₙ(R)` is a product of at most
`2n + 2` factors, each either an elementary transvection or an element of the
fixed coordinate copy of `GLₙ₋₁(R)`.

Exact Lean declaration:

```text
GroupApproximation.PropertyTTPaper.coordinateBlock_factorization
```

The three-move diagonal pivot used in its proof is exposed separately as:

```text
GroupApproximation.PropertyTTPaper.threeMove_diagonalPivot
```

Credit boundary: Ara--Goodearl--Pardo, Theorem 1.6, identifies the sandwich
condition with pure infiniteness for nondivision simple unital rings.
Bounded-generation
globalization belongs to the Shalom--Mimura rigidity tradition. The candidate
contribution is only the explicit coordinate-block elimination theorem and its
width. The manuscript must not call this bounded elementary generation.

## Theorem B: four-hypothesis synthesis

Let `R` be a nontrivial ring equipped with:

1. a finite surjective presentation from a free associative `Z/2Z`-algebra;
2. a binary Leavitt family;
3. strong sandwich division `a ≠ 0 -> ∃ x y, x*a*y = 1`;
4. elementary triviality of every diagonal unit, `diag(u,1) ∈ E₂(R)`.

Then `Eₙ(R)` has property `(TT)/T` for each `n ≥ 2` covered by the Lean
statement.

Exact Lean declaration:

```text
GroupApproximation.PropertyTTPaper.finiteFreeQuotient_elementaryGroup_hasTTmodT
```

Equivalent finite-type wrapper used for the paper's prose statement:

```text
GroupApproximation.PropertyTTPaper.finiteType_elementaryGroup_hasTTmodT
```

The manuscript's intermediate rank-four and globalization steps correspond to
the following exact declarations:

```text
GroupApproximation.PropertyTTPaper.elementaryGroup_eq_generalLinear
GroupApproximation.PropertyTTPaper.leavitt_elementaryRankEquivalence
GroupApproximation.PropertyTTPaper.elementaryBlockFlattening
GroupApproximation.PropertyTTPaper.kazhdan_normalizedSet_globalization
GroupApproximation.PropertyTTPaper.finiteFreeQuotient_rankFour_hasTTmodT
GroupApproximation.PropertyTTPaper.quasiCocycle_list_product_bound
```

The last inequality is the empty-list-safe estimate actually proved in Lean:
for a list of length `m` whose entries satisfy `‖b(g)‖ ≤ C`, it gives
`‖b(prod)‖ ≤ m*C + (m+1)*D`.

The wrapper uses `Algebra.FiniteType (ZMod 2) R` only to construct the finite
free-algebra surjection. It does not infer or suppress the Leavitt-family,
sandwich-division, or unstable-diagonal hypotheses.

Credit boundary: the definition and rigidity role of `(TT)/T` are due to
Mimura. Property `(T)` for elementary groups over finitely generated
associative rings is due to Ershov--Jaikin-Zapirain. Matrix self-similarity and
the relevant Leavitt-ring structure are classical. Only the synthesis from the
exact hypotheses, using the analytic input and Theorem A, is a candidate
contribution.

## Proposition: unstable rank-two elimination

For every field `k`, every invertible `2 × 2` matrix over the binary Leavitt
algebra is elementary. Equivalently,

```text
E₂(L_k(1,2)) = GL₂(L_k(1,2)).
```

Exact Lean declarations:

```text
GroupApproximation.KOnePaper.diagUnit_mem_elementary
GroupApproximation.KOnePaper.elementaryGroup_two_eq_top
```

Credit boundary: this equality also receives no theorem-novelty credit.
Menal--Moncasi supply the GE theorem used for purely infinite simple unital
rings; Ara--Goodearl--Pardo apply it and identify stable `K₁` with the
abelianization of the unit group. Ara--Brustenga--Cortiñas give
`K₁(L_k(1,2)) = 0`. Hence every unit is
a product of commutators; the classical rank-two Whitehead identity makes
`diag(u,1)` elementary; and GE reduction gives `GL₂ = E₂`. The manuscript
uses this established structural route and makes no novelty claim for the
unstable equality.

## Theorem C: the binary Leavitt algebra

For every `n ≥ 2`, the elementary group over the binary Leavitt algebra has
property `(TT)/T`.

Exact Lean declaration:

```text
GroupApproximation.PropertyTTPaper.binaryLeavitt_elementaryGroup_hasTTmodT
```

Credit boundary: the binary Leavitt algebra's structural and `K`-theoretic
facts are not claimed as new. The only possible novelty here is the resulting
`(TT)/T` conclusion.

## Corollary: nonsofic and `(TT)/T`

For every `n ≥ 2`, the elementary group over the binary Leavitt algebra has
property `(TT)/T` and is nonsofic.

Exact Lean declaration:

```text
GroupApproximation.PropertyTTPaper.binaryLeavitt_elementaryGroup_hasTTmodT_and_not_isSofic
```

Credit boundary: the nonsoficity theorem and its proof mechanism belong to
OpenAI, *Ten Advances in Mathematics and Theoretical Computer Science*
(2026), Chapter 3, Theorem 1.1. The conjunction is only a corollary; neither
the abstract nor the introduction may imply that this paper constructs or
proves the nonsofic group independently.

## Release gates

- All declarations above compile from a cold build.
- `Endpoint/Audit.lean` reports no unapproved axioms for every paper-facing
  declaration.
- Every manuscript theorem has exactly the hypotheses and conclusion of its
  Lean declaration; no prose strengthening is permitted.
- Every imported mathematical ingredient receives primary-source credit at
  its first point of use.
- No title, abstract, or introduction uses `first`, `new`, or equivalent
  priority language without a completed final literature audit.
- Formal verification, proof repair, and code engineering are not described as
  mathematical novelty.
