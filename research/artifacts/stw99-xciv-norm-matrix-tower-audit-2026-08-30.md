# STW Problem XCIV: norm finite-dimensional-tower audit (2026-08-30)

## Source definition and open root

Schafhauser--Tikuisis--White define separable `D`-stability to mean that every
norm-separable subset of the ambient algebra is contained in a norm-separable
`D`-stable subalgebra; see footnote 21 of
[Nuclear C\*-algebras: 99 problems](https://arxiv.org/html/2506.10902v2).
At Problem XCIV they ask this for `D=Z` and the hyperfinite II1 factor `R`, and
state that a suitably large-relative-ultrapower version of property (SI) would
give a positive answer.  The unrestricted question remains open here.

## Audit of the existing XCIV routes

All local XCIV claims and proof routes were checked before adding the matrix
tower theorem.  The existing positive subclass requires a unital CAR algebra
in the exact relative commutant of the whole seed.  The local-central
equivalence instead asks for actual operator-norm-central `Z` embeddings for
every finite subset of `R`.  The property-(SI) route remains conditional, and
the recorded orthogonal-corner example correctly shows why tracial
centrality alone cannot choose norm-central representatives.

The new class is not an instance of the exact-commutant theorem.  It starts
with an increasing finite-dimensional tower and assumes that, arbitrarily
far out, every nonzero Bratteli multiplicity from a fixed stage is uniformly
large.  For each `k`, multiplicity at least `k^2+k+1` supplies a unital
faithful `M_k direct_sum M_(k+1)` in the finite-stage relative commutant.
This makes the AF norm core and all its finite-stage tail commutants
approximately divisible and hence `Z`-stable.  In a dyadic model
`R=(union_n M_(2^n))''`, the CAR core is a special case even though it is
weakly dense and consequently has scalar relative commutant in `R`.

The integer threshold is internal: for `t>=k^2+k+1`, write
`t-(2k+1)=ell k+r` with `0<=r<k`.  Then `ell>=k-1>=r` and

```text
t=k(ell-r+1)+(k+1)(r+1),
```

so both irreducible summands occur.  Haar averaging proves
`F_n' intersect A=closure(union_(m>=n)(F_n' intersect F_m))`.  Applying the
same multiplicity argument after a later stage proves approximate
divisibility of the tail commutant itself, not just of the ambient AF core.
Here approximate divisibility is used in the standard equivalent form of
approximately central unital copies of arbitrarily large coprime matrix
sums; the constructed `M_k direct_sum M_(k+1)` copies meet it.  The imported
absorption boundary is Toms--Winter, *Z-stable ASH algebras*, Theorem 2.3:
every separable approximately divisible C*-algebra is `Z`-stable.  This
theorem does not require nuclearity or simplicity.

## Exact boundary

The hypothesis is one coherent finite-dimensional tower with uniform growth
of every positive tail multiplicity, together with operator-norm distance
tending to zero.  It strictly includes the previous unbounded full-matrix
tower criterion.  Replacing operator-norm distance by tracial `2`-norm
distance would make approximation available throughout `R` but would
invalidate the commutator estimate: the bound used in the proof is

```text
||[x,phi(z)]|| <= 2 ||x-b|| ||z||.
```

Thus the theorem proves separable `Z`-stability for subsets lying in these
approximately divisible AF norm cores of `R`, including weakly dense UHF
cores, but makes no assertion for an arbitrary norm-separable subset of `R`.
