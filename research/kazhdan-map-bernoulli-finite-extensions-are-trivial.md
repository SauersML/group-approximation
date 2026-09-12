---
rg: 2
id: kazhdan-map-bernoulli-finite-extensions-are-trivial
kind: claim
title: Over a Kazhdan group without finite quotients every ergodic finite-to-one extension of a Bernoulli action is an isomorphism
distinct_from:
  kazhdan-bernoulli-rigidity-forces-surjective-embeddings: that is the refuted claim that continuous equivariant injections of Bernoulli coset shifts over simple Kazhdan groups are surjective; this is a measurable theorem about finite-to-one extensions over the regular Bernoulli base, and it does not assert surjectivity of any embedding.
  finite-rank-superrigid-cocycles-cannot-cancel-fixed-points: that uses superrigid unitary cocycles on non-free actions to exclude regular decorated normalizers; this uses finite permutation cocycles over a free Bernoulli base to untwist finite extensions.
  strict-pair-flip-lifts-are-relatively-weakly-mixing: that shows the extensions every strict pair carries are relatively weakly mixing; this shows finite-to-one extensions of the Bernoulli base collapse.
artifacts:
  - research/artifacts/kazhdan-superrigidity-bernoulli-extensions-2026-09-12.md
---

ESTABLISHED. Let `G` be an infinite countable group with property (T) and no nontrivial homomorphism
to a finite group, and `(X, mu)` a Bernoulli action of `G` with nontrivial standard base (atomic or
not). Let `pi: (Z, m) -> (X, mu)` be an extension with `(Z, m)` ergodic, whose conditional measures
`m_x` are finitely supported for almost every `x`. Then `pi` is an isomorphism mod null sets.

Proof: Section 4 of the artifact, Theorem 4.1.
0. *Base reduction.* Multiplying by an independent Bernoulli factor `Y = ([0,1], Leb)^G` makes
   `Z x Y` an ergodic finite extension of `X x Y ~= ([0,1], Leb)^G` with the same multiplicity. So the
   import is used only in its s-malleable, diffuse-base form.
1. The multiplicity is almost everywhere constant.
2. A Borel enumeration of the fibres writes `Z` as `X x {1..n}` with a cocycle into `Sym(n)`.
3. Popa's cocycle superrigidity makes the cocycle cohomologous to a homomorphism, and the
   homomorphism is trivial because `G` has no finite quotient.
4. Untwisting makes each sheet invariant, and ergodicity forces `n = 1`.

Scope:
* It applies to every finitely generated infinite simple Kazhdan group, including `R^x` and every
  host of `countable-group-embeds-in-fg-simple-kazhdan-group`, and in particular to the uniform
  Bernoulli shift `A^G`.
* **Design filter.** Over such hosts, an ergodic invariant lift of the Bernoulli measure on which a
  decoder is finite-to-one is an isomorphism. Every useful lift of a strict pair is infinite-to-one.
  The flip lifts are, with positive relative entropy.
* With compact targets and Zimmer's structure theorem the same argument trivializes compact
  extensions (artifact Remark 4.3). That version is not claimed here.

**Scope correction (2026-09-12).** gk-vf-positive passed the first version but flagged that it
consumed the import for atomic bases, whose coverage by Popa's theorem was unverified. Step 0 was
added so that only the s-malleable diffuse-base case of the import is needed. Step 0 has not yet been
re-verified.
