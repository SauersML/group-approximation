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
- **Every type-III von Neumann codomain is eliminated.**
  `stw63-arbitrary-type3-vn-asymptotic-uniqueness` removes factoriality,
  sigma-finiteness, separable-predual and separable-action assumptions.  A
  type-III von Neumann algebra is strongly purely infinite as a C-star
  algebra.  Jiang--Su embeddings are full even when the target has proper
  cardinal-rank ideals, so Gabe's full-map classification gives asymptotic
  uniqueness.  This route never claims that arbitrary nonzero projections
  are equivalent or that the target is C-star simple.
- **Arbitrary-cardinal type-I factors are eliminated.**
  `stw63-arbitrary-type1-factor-uniqueness` combines the finite-copy fullness
  inequality with infinite-cardinal arithmetic and Hadwin's nonseparable
  rank theorem.  Thus every `B(H)`, without a separability assumption on
  `H`, has uniqueness.  Product closure gives the same result for every
  atomic type-I von Neumann algebra.
- **Every von Neumann codomain is eliminated.**
  `stw63-all-von-neumann-codomains-have-uniqueness` places the two ranges in
  their countably generated W-star envelope.  Elliott--Zsido decompose that
  envelope as a direct product of separable-predual W-star algebras;
  separably acting uniqueness and product closure then give norm approximate
  unitary equivalence in the original von Neumann algebra.  Hence
  `stw63-counterexamples-invisible-in-all-vn-shadows` rules out every von
  Neumann shadow, with no type, center, predual, or cardinality restriction.
- **Exact bidual-return obstruction.**
  `stw63-aue-is-relative-corner-equivalence` identifies approximate unitary
  equivalence with Murray--von Neumann equivalence of the two coordinate
  projections in a pair-dependent relative sequence algebra `D`.  Universal
  von Neumann uniqueness makes the same projections equivalent after the
  canonical inclusion `D->E` obtained from `B->B**`.  Thus
  `stw63-relative-v-obstruction` shows that every counterexample is exactly a
  failure of this inclusion to reflect one distinguished projection
  equivalence.  This does not assume that bidual unitaries lift.
- **A conditional return theorem.**
  `stw63-relative-k0-return-criterion` proves uniqueness for a pair whenever
  `K_0(D)->K_0(E)` is injective and `D` has projection cancellation (stable
  rank one of `D` suffices).  Stable rank one of the original codomain is not
  claimed to pass to this relative commutant.
- **Strict comparison needs no unique quasitrace for uniqueness.**
  `stw63-strict-comparison-sr1-uniqueness` proves that a unital simple
  stable-rank-one codomain with nonempty normalized 2-quasitrace space and
  strict comparison has at most one Jiang--Su embedding up to approximate
  unitary equivalence.  All quasitraces restrict to the unique trace of `Z`;
  strict comparison first compares a smaller soft class `r_k<r`, and a
  supremum then proves equality at `r`.  Robert's map theorem returns the
  resulting equality of `Cu` maps.  No unique-quasitrace hypothesis is used.
- **Unconditional convex norm return.**
  `stw63-convex-unitary-return` combines the all-von-Neumann theorem with
  unitary Kaplansky density and Hahn--Banach: each embedding is in the
  point-norm closed convex hull of the other's `B`-unitary orbit.  The missing
  universal step is deconvexification from a finite random-unitary average to
  one inner conjugate; strong density alone cannot perform it.
- **Generic descent shortcuts fail even for AF targets.**
  `stw63-generic-bidual-return-fails-for-af` gives two maps `C^2->B` for a
  simple stationary AF algebra which are exactly unitarily conjugate in
  `B**` but not approximately unitarily equivalent in `B`.  Thus nuclearity,
  exactness, local reflexivity, real rank zero, stable rank one and fullness
  do not by themselves return bidual conjugacies.  This is a boundary test,
  not a Jiang--Su counterexample.
- **All von Neumann rank and norm-ideal invariants collapse.**
  `stw63-all-vn-rank-and-ideal-data-collapse` proves, without any countability
  or type assumption, that the two embeddings have equal elementwise
  von Neumann rank and that every nonzero image element is norm-full.  Hence
  this independently explains why projection cardinality and proper norm
  ideals cannot obstruct the universal von Neumann theorem.
- **Sigma-finite type-II-infinity factors need not have separable predual.**
  `stw63-sigmafinite-type2inf-factor-uniqueness` combines the global rank
  collapse with Li--Hadwin--Liu's factor-specific Corollary 1, whose target
  hypothesis is sigma-finiteness rather than separable action.  It therefore
  closes every countably decomposable type-II-infinity factor, and product
  closure handles arbitrary products of such factors.  The countably
  generated-envelope theorem above then removes the remaining factor and
  diffuse-center restrictions by a different argument.
- **Asymptotic upgrade.**  Even after approximate uniqueness, coherent paths
  are a separate issue.  `approximate-to-asymptotic-via-central-paths`
  isolates a sufficient quantitative contraction property for the transition
  unitaries and proves the path concatenation rigorously.
