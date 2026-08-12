# Property `(TT)/T` paper claim map

This file is the publication gate for the property `(TT)/T` paper. A result may
appear as a numbered theorem in the manuscript only when it has one exact
paper-facing Lean declaration below. The manuscript proof must follow that
declaration's dependency path. Formalization itself is not claimed as
mathematical novelty.

## Theorem A: strong relative root control

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

Credit boundary: relative `(TT)/T` for noncommutative universal lattices is
already present in Mimura's work. The paper must not advertise noncommutative
relative rigidity itself as new. The candidate increment is the stronger root
statement without the `/T` hypothesis and its quantitative rank-four proof.
Priority language is forbidden until the final literature and specialist
checks are complete.

## Theorem B: coordinate-block factorization

Let `R` be a nontrivial ring such that every nonzero `a` admits `x, y` with
`x * a * y = 1`. If `2 ≤ n`, every element of `GLₙ(R)` is a product of at most
`2n + 6` factors, each either an elementary transvection or an element of the
fixed coordinate copy of `GLₙ₋₁(R)`.

Exact Lean declaration:

```text
GroupApproximation.PropertyTTPaper.coordinateBlock_factorization
```

Credit boundary: the sandwich condition and its connection to purely infinite
simple rings belong to the established ring literature. Bounded-generation
globalization belongs to the Shalom--Mimura rigidity tradition. The candidate
contribution is only the explicit coordinate-block elimination theorem and its
width. The manuscript must not call this bounded elementary generation.

## Theorem C: four-hypothesis synthesis

Let `R` be a nontrivial ring equipped with:

1. a finite surjective presentation from a free associative `Z/2Z`-algebra;
2. a binary Leavitt family;
3. strong sandwich division `a ≠ 0 -> ∃ x y, x*a*y = 1`;
4. elementary triviality of every diagonal unit, `diag(u,1) ∈ E₂(R)`.

Then `Eₙ(R)` has property `(TT)/T` for each `n ≥ 3` covered by the Lean
statement.

Exact Lean declaration:

```text
GroupApproximation.PropertyTTPaper.finitePresentation_elementaryGroup_hasTTmodT
```

Credit boundary: the definition and rigidity role of `(TT)/T` are due to
Mimura. Property `(T)` for elementary groups over finitely generated
associative rings is due to Ershov--Jaikin-Zapirain. Matrix self-similarity and
the relevant Leavitt-ring structure are classical. Only the synthesis from the
exact hypotheses, using Theorems A and B, is a candidate contribution.

## Corollary D: the binary Leavitt algebra

For every `n ≥ 3`, the elementary group over the binary Leavitt algebra has
property `(TT)/T`.

Exact Lean declaration:

```text
GroupApproximation.PropertyTTPaper.binaryLeavitt_elementaryGroup_hasTTmodT
```

Credit boundary: the binary Leavitt algebra's structural and `K`-theoretic
facts are not claimed as new. The only possible novelty here is the resulting
`(TT)/T` conclusion.

## Corollary E: nonsofic and `(TT)/T`

For every `n ≥ 3`, the elementary group over the binary Leavitt algebra has
property `(TT)/T` and is nonsofic.

Exact Lean declaration:

```text
GroupApproximation.PropertyTTPaper.binaryLeavitt_elementaryGroup_hasTTmodT_and_not_isSofic
```

Credit boundary: the nonsoficity theorem and its proof mechanism belong to the
prior OpenAI work. The conjunction is only a corollary; neither the abstract
nor the introduction may imply that this paper constructs or proves the
nonsofic group independently.

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
