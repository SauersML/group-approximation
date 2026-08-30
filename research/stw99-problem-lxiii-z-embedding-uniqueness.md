---
rg: 2
id: stw99-problem-lxiii-z-embedding-uniqueness
kind: claim
title: Any two unital embeddings of the Jiang--Su algebra into a unital C-star algebra are approximately unitarily equivalent (STW LXIII)
root: true
refuted_by:
  - stw63-distinct-cu-maps-counterexample
artifacts:
  - research/artifacts/stw63-z-embedding-audit-2026-08-30.md
---

For every unital C-star algebra `B` and unital embeddings

```text
phi, psi : Z -> B,
```

there are unitaries `u_n in B` such that

```text
||u_n phi(z) u_n^* - psi(z)|| -> 0                  (z in Z).
```

This is **STW Problem LXIII and remains open at the audit boundary
2026-08-30**.  The stronger asymptotic form is
`stw63-all-z-embeddings-asymptotically-unitary`.

## Attempts

- **Ordinary invariant separation is dead.**
  `z-embedding-invariants-collapse-before-cu` proves that the two embeddings
  always have the same `KK` class, unit-preserving K-theory, bounded tracial
  data, and ideal map.  Any negative example must use finer nonstable data.
- **Cuntz-semigroup lane.**  The open refuter
  `stw63-distinct-cu-maps-counterexample` asks for two actual embeddings with
  different `Cu` maps.  Approximate unitary equivalence would force equality,
  so this would be a genuine counterexample rather than merely two abstract
  semigroup maps.
- **Pairwise absorption lane.**
  `joint-central-z-bridge-forces-approximate-uniqueness` proves uniqueness
  whenever the two ranges have a common unital `Z` in their joint relative
  commutant in `B_infinity`.  This hypothesis is pairwise and can hold without
  asserting `B tensor Z = B`; what is missing in general is construction of
  the bridge.
- **Free-product stress test.**  The two canonical copies in a full or reduced
  free product are tempting candidates because an implementing unitary would
  have to remain in the C-star algebra, not merely its von Neumann closure.
  No norm obstruction is presently proved.  Tracial von Neumann completion
  cannot supply one: the 2026 finite-factor uniqueness theorem gives norm
  approximate conjugacy by unitaries in the factor.
- **Every separably acting von Neumann shadow is eliminated.**
  `stw63-all-separably-acting-von-neumann-codomains-have-uniqueness` combines
  the finite/semifinite theorem with Hua--White type-III-factor uniqueness
  and a measurable central-integration argument.  Thus a counterexample
  cannot be detected in any separably acting von Neumann representation of
  its pair-generated algebra, regardless of type.  The obstruction must be
  failure to return von Neumann implementing unitaries to the original
  C-star algebra, or must require a genuinely non-separably-acting shadow.
  Arbitrary finite von Neumann targets remain covered without countability
  restrictions by the earlier theorem.
- **Sigma-finite type-III factors need not have separable predual.**
  `stw63-sigmafinite-type3-factor-asymptotic-uniqueness` observes that a
  sigma-finite type-III factor is simple purely infinite as a C-star algebra
  and applies Kirchberg's nuclear KK uniqueness theorem.  This gives the
  stronger asymptotic conclusion without a separable-predual assumption, and
  product closure covers arbitrary products of such factors.  Genuinely
  non-sigma-finite type-III factors are not covered: their nonzero projection
  classes need not all equal the unit, so the simplicity step fails.
- **Arbitrary-cardinal type-I factors are eliminated.**
  `stw63-arbitrary-type1-factor-uniqueness` combines the finite-copy fullness
  inequality with infinite-cardinal arithmetic and Hadwin's nonseparable
  rank theorem.  Thus every `B(H)`, without a separability assumption on
  `H`, has uniqueness.  Product closure gives the same result for every
  atomic type-I von Neumann algebra.
- **Asymptotic upgrade.**  Even after approximate uniqueness, coherent paths
  are a separate issue.  `approximate-to-asymptotic-via-central-paths`
  isolates a sufficient quantitative contraction property for the transition
  unitaries and proves the path concatenation rigorously.
