# STW LXXII: topological-dimension-zero literature import (2026-08-30)

## Verdict

Two primary sources establish the same unconditional positive slice of the
weakly-purely-infinite problem.  For every C-star algebra `A` of topological
dimension zero,

```text
A is weakly purely infinite
  <=> A is purely infinite
  <=> A is strongly purely infinite.
```

The unrestricted implication in STW Problem LXXII is **not** claimed here.
No separability, nuclearity, unitality, exactness, real-rank, stable-rank, or
Hausdorff-spectrum assumption occurs in the imported theorem.

## Primary-source status check

The sources and theorem statements were checked on 2026-08-30.

1. G. A. Elliott and M. Rouzbehani, [*Weakly Purely Infinite C-star
   algebras with Topological Dimension Zero are Purely
   Infinite*](https://mathreports.ca/article/weakly-purely-infinite-c-algebras-with-topological-dimension-zero-are-purely-infinite/),
   C. R. Math. Rep. Acad. Sci. Canada 45(4) (2023), 87--91.  Theorem 2.1 is
   the weak-to-plain equivalence and Corollary 2.2 adds strong pure
   infiniteness.  The separability and nuclearity assumptions in the latter
   attach only to its additional `O_infinity`-absorption equivalence.
2. P. W. Ng, H. Thiel, and E. Vilalta, [*The Global Glimm Property for
   C-star algebras of topological dimension
   zero*](https://doi.org/10.1112/blms.70343), Bull. Lond. Math. Soc. 58(4)
   (2026), article e70343; [arXiv:2507.16261,
   v2](https://arxiv.org/abs/2507.16261).  Theorem 2.3 proves that, for every
   topological-dimension-zero C-star algebra, nowhere scatteredness is
   equivalent to the Global Glimm Property.  Corollary 2.5 recovers the
   Elliott--Rouzbehani weak-to-plain collapse.  The journal version was first
   published on 2026-04-01.

The Schafhauser--Tikuisis--White problem list was also checked in its current
form, [arXiv:2506.10902](https://arxiv.org/abs/2506.10902).  It still records
the unrestricted equivalence as Problem LXXII; the special case above must
therefore be represented as an established child claim, not as a resolution
of the root.

## Dependency audit

The 2026 proof gives a short independently checkable implication chain.

1. A weakly purely infinite C-star algebra is nowhere scattered
   (Thiel--Vilalta, Example 3.3, cited in the proof of Ng--Thiel--Vilalta,
   Corollary 2.5).
2. Topological dimension zero plus nowhere scatteredness gives the Global
   Glimm Property (Ng--Thiel--Vilalta, Theorem 2.3).
3. Weak pure infiniteness plus the Global Glimm Property gives pure
   infiniteness (Kirchberg--Rordam, Proposition 4.15).
4. Pure infiniteness implies weak pure infiniteness in general.
5. Elliott--Rouzbehani, Corollary 2.2, identifies these two equivalent
   conditions with strong pure infiniteness in topological dimension zero.

Every hypothesis used by the chain is visible.  In particular, Theorem 2.3
explicitly removes the separability assumption in its preliminary Cuntz-
semigroup characterization, so no countability hypothesis has been imported
silently.

## Why this enlarges the existing Cairn frontier

Topological dimension zero means that `Prim(A)` has a basis of compact open
sets.  It is transverse to the previously recorded chain, finite-lattice,
and scattered-spectrum mechanisms.  For instance,

```text
C(Cantor space) tensor_min O_infinity
```

has topological dimension zero, an infinite non-chain ideal lattice, and a
primitive ideal space with no isolated point.  Every nonempty open subset of
the Cantor space contains two disjoint nonempty open subsets, so no nonzero
ideal in this example has a chain ideal lattice; in particular it is not a
chain-ideal-cover instance.  The topological-dimension-zero theorem therefore
adds a genuinely different positive region rather than relabeling an existing
special case.

## Multiplier consequence

Ng--Thiel--Vilalta, Theorem 2.6 and Corollary 2.8, also import a second exact
result.  If `A` is sigma-unital, purely infinite, and has real rank zero, then
`M(A)` is purely infinite.  The proof has three transparent inputs:

1. Zhang's theorem makes `M(A)` topological dimension zero.
2. Kirchberg--Rordam, Proposition 4.11, makes `M(A)` weakly purely infinite.
3. The preceding topological-dimension-zero collapse makes `M(A)` purely
   infinite.

This closes the real-rank-zero case of Kirchberg--Rordam's multiplier question
without pretending that the multiplier algebra itself has real rank zero.
Ng--Thiel--Vilalta, Remark 2.9, explicitly records examples where its real
rank is one.
