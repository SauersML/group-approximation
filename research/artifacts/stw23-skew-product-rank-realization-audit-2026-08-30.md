# STW Problem XXIII: skew-product rank-realization audit

## Result

For a minimal homeomorphism `h:X->X`, an arbitrary automorphism `beta` of a
simple exact unique-trace fibre `B`, and

```text
D=(C(X) tensor B) rtimes_(h tensor beta) Z,
```

all ranks occur provided `B` contains one positive contraction with Lebesgue
spectral distribution for its unique trace.  The realizing operator is built
inside the stabilized coefficient algebra.

This is a genuine many-trace statement: `QT(D)` is the full invariant-measure
simplex `M_h(X)`, which need not have finitely many extreme points or
finite-dimensional extreme boundary.  The proof does not invoke stable rank
one, strict comparison, finite-dimensional trace boundary, or
Jiang--Su absorption.

## Audit of the four possible failure points

1. **Extra crossed-product traces.**  There are none.  Freeness of every
   nonzero power of `h` supplies central cutoffs with disjoint translates,
   killing every nonzero Fourier coefficient of a trace.  Unique trace on
   `B` then identifies coefficient traces with measures on `X`.
2. **A positive representative on `X`.**  Continuous functions on `X` map
   onto `Aff(M_h(X))`: affine approximation gives dense range, while Jordan
   decomposition of invariant signed measures identifies the quotient norm
   with the uniform norm on `Aff(M_h(X))`, making the range closed.  Strict
   positivity on all invariant measures then makes one finite orbit average
   pointwise positive: failure would produce an invariant empirical limit
   with nonpositive integral.
3. **Exact, rather than approximate, ranks.**  Scaling an increasing affine
   approximation produces strictly positive increments whose sum is exactly
   the prescribed lower semicontinuous affine function.  Each increment is
   represented exactly by a positive orbit average.
4. **One operator rather than a formal Cu-supremum.**  Spectral cuts of the
   Lebesgue-distributed fibre element give the exact pointwise rank.  Putting
   the cuts in orthogonal compact-operator blocks and multiplying the `n`th
   block by `2^(-n)` gives a norm-convergent positive element; support ranks
   add by normal monotone convergence.

## Literature boundary and novelty check

The general rank problem remains open.  The existing positive theorems found
in the source and the current primary catalogue cover stable-rank-one
algebras (Antoine--Perera--Robert--Thiel and Thiel), finitely many extremal
quasitraces (Tikuisis--Toms), Jiang--Su-stable algebras
(Elliott--Robert--Santiago), and strict comparison with controlled extremal
boundary (Dadarlat--Toms).  Searches for rank realization in minimal crossed
products and skew products did not locate the orbit-average/spectral-cut
theorem recorded here.

Primary background used in the audit:

* U. Haagerup, *Quasitraces on exact C*-algebras are traces*.
* R. Antoine, F. Perera, L. Robert, H. Thiel,
  *C*-algebras of stable rank one and their Cuntz semigroups*,
  arXiv:1809.03984.
* A. Tikuisis, A. Toms,
  *On the structure of the Cuntz semigroup in (possibly) nonunital
  C*-algebras*, arXiv:1210.2235.

## Limitation

The theorem is a subclass result, not a solution of Problem XXIII.  Its
decisive extra datum is a single fibre element with exactly Lebesgue spectral
distribution.  The argument also uses a free central minimal dynamical
coordinate; it does not show how to manufacture such a coordinate inside an
arbitrary simple algebra.
