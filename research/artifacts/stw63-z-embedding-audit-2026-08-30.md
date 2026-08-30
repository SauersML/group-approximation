# STW LXIII: literature and proof-boundary audit (2026-08-30)

## Question

Problem LXIII of Schafhauser--Tikuisis--White asks whether, for every unital
C-star algebra `B`, every two unital embeddings `Z -> B` are approximately
unitarily equivalent, or even asymptotically unitarily equivalent.  The cached
v2 text at `tmp/pdfs/stw99.txt`, lines 3079--3109, still states the problem and
records the known `Z`-stable and stable-rank-one/Cuntz-semigroup cases.

## Time-sensitive audit

The following primary sources were checked by exact-title and exact-phrase
searches, followed by inspection of the theorem statements.

1. T. Amrutam, D. Gao, S. Kunnawalkam Elayavalli and G. Patchell,
   *Strict comparison in reduced group C-star algebras*, arXiv:2412.06031,
   published in Inventiones in 2025,
   <https://arxiv.org/abs/2412.06031>.  Its introduction explicitly says that
   it remains open whether a unital C-star algebra can have two inequivalent
   unital embeddings of `Z`.  Its Theorem C proves uniqueness for a large new
   family of reduced group C-star algebras.
2. I. Vigdorovich, *Structural properties of reduced C-star algebras
   associated with higher-rank lattices*, arXiv:2503.12737,
   <https://arxiv.org/abs/2503.12737>.  This adds higher-rank reduced group
   C-star algebras to the positive stable-rank-one/strict-comparison family;
   it does not treat arbitrary codomains.
3. S. Hua and S. White, *Uniqueness for embeddings of nuclear C-star
   algebras into type II_1 factors*, arXiv:2601.08779,
   <https://arxiv.org/abs/2601.08779>.  Theorem 5.2 proves norm approximate
   unitary equivalence for faithful unital nuclear maps from a separable
   unital nuclear UCT algebra into a II_1 factor when the traces agree.
   Applied to `Z`, this closes every II_1-factor codomain.  The paper also
   records Kirchberg's asymptotic uniqueness theorem for simple purely
   infinite codomains (Appendix A, Theorem A.2).
4. Targeted arXiv searches through 2026-08-30 for the exact combinations
   "Jiang--Su", "embedding", "approximately unitarily equivalent", and
   "Problem LXIII" found no later claim resolving the arbitrary unital
   codomain question.  The May 2026 paper arXiv:2605.22585 concerns unitary
   orbits and Wasserstein geometry in regular targets, not LXIII.

## Trust boundary

This is a targeted, not bibliometrically exhaustive, audit.  Non-discovery is
not a proof of openness.  The strongest direct status evidence is the explicit
open-problem statement in the published 2025 paper, combined with inspection
of the scopes of the relevant 2026 results.  No literature assertion is used
as a premise in any graph route added with this artifact.

## New internal deductions recorded in the graph

The graph additions isolate three facts which do not depend on the literature
audit.

1. Every possible counterexample is invisible to `KK`, unit-preserving
   K-theory, bounded traces, and ideal maps.  Cuntz-semigroup data is the first
   standard invariant in which the two maps can still separate.
2. A common unital copy of `Z` in the joint relative commutant inside the
   sequence algebra is enough for approximate uniqueness.  This is strictly a
   pairwise condition; it does not assume that `B` is `Z`-stable.
3. Approximate equivalence upgrades to asymptotic equivalence whenever
   sufficiently central transition unitaries can be contracted through
   controlled approximately central paths.  The proof gives the exact
   concatenation mechanism and exposes the remaining obstruction as topology
   of approximate relative commutants, rather than K-theory or traces of the
   embeddings.
