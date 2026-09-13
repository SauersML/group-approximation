---
rg: 2
id: belyaev-associative-higman-theorem
kind: claim
title: Every associative K-algebra with a recursively enumerable presentation embeds in a finitely presented associative K-algebra
distinct_from:
  decidable-algebras-embed-in-decidable-fp-algebras: that adds the decidability clause, embedding an algebra with SOLVABLE word problem in one with solvable word problem; this is the plain recursively-enumerable Higman analogue, with no control on the word problem of the envelope.
  birget-semigroup-embedding-preserves-word-problem: that is the semigroup Higman-with-word-problem theorem; this is the associative-algebra Higman theorem without any word-problem clause.
  clapham-fp-embedding-preserves-word-problem: that is Clapham's group theorem, with a group envelope and a preserved word problem; this is the associative-algebra analogue of Higman's theorem, without the word-problem clause.
artifacts:
  - research/artifacts/belyaev-1978-decidability-analysis-2026-09-13.md
---

**ESTABLISHED** as a citation import, through
`belyaev-associative-higman-citation`. Read from the Springer scan at source
(2026-09-13); statements quoted verbatim in the artifact.

Let `K` be a commutative associative ring with unity, or a field, that is
finitely generated over its prime subring. Every associative `K`-algebra `A`
with a recursively enumerable set of defining relations embeds, as a
subalgebra, in a finitely presented associative `K`-algebra. The unity of an
algebra, if present, is not fixed in the signature. By the paper's Corollary,
the envelope can be taken 2-generated.

This is the associative form of Higman's embedding theorem. It contains **no**
statement about the word problem: the envelope is finitely presented, but its
word problem is not controlled. Making the envelope's word problem solvable
when `A`'s is solvable is a separate question, recorded at
`decidable-algebras-embed-in-decidable-fp-algebras` and reduced to two concrete
lemmas by `decidable-clapham-via-effective-belyaev`.

## Proof structure (Belyaev 1978)

- **Lemma 1** (the additive homomorphism, due to Taitslin in the ring case):
  given a `K`-module endomorphism `φ` of `A` that restricts to an algebra
  homomorphism on a finitely generated subalgebra, an overalgebra adjoins a
  solution of the system `Hom_n(ā, b̄, θ̄)` (`x a_i z y = b_i`, `a_i z = z β_i`,
  `x z β_i β_j = b_i x z β_j`).
- **Lemma 2**: an algebra with the special enumerable presentation
  `{x y^i z + x y^j z = x y^{f(i,j)} z : i ≠ j} ∪ {x y^i z = x y^j z : ⟨i,j⟩ ∈ Y}`
  embeds, as a `K`-module direct summand, in an algebra with finitely many
  generators and a presentation whose relations are word equalities except for
  one relation `α + β = γ`. The construction uses the injective pairing
  functions `n_i(j)`, `s(i,j)` drawn from the line-intersection diagram.
- **Lemma 3** (modification of Mal'tsev): a countable algebra
  `A = {a_1, a_2, …}` embeds in an algebra with elements `a, b, c` such that
  `a_i = a b^i c`.
- **Theorem**: enumerate `A`, apply Lemma 3, form the special algebra `S`,
  apply Lemma 2 to reach `S_1`, then apply **Murskii's semigroup embedding
  theorem twice** (to a semigroup `G` carrying the word equalities of `S_1`,
  and to a semigroup `H` carrying a counting function `g`) and Lemma 1 three
  times. The final finite relation set is the union of the systems (1)–(7).
