---
rg: 2
id: three-site-pauli-refutes-unpeeled-fourth-moment
kind: claim
title: A three-site Pauli block refutes an unpeeled sparse fourth-moment gain
distinct_from:
  sparse-clifford-cycles-refute-average-commutator-rounding: that uses an extensive sparse Clifford graph to stay globally far from commuting tuples; this is a localized, cheaply repairable three-site block which refutes only the proposed little-o fourth-moment inequality.
  operator-tail-contraction-misses-uniform-diffuse-matching: that exhibits a diffuse scalar profile invisible to small-tail expansion; this is a genuinely sparse high-tail example and explains why tail peeling must precede the random-anchor estimate.
  balanced-overlay-sparse-sites-evade-hilbert-outlier-cut: that concerns physical spectral cuts for sparse full-rank errors; this computes the exact random-anchor and balanced-face normalizations.
---

ESTABLISHED.  Let the Tanner family have `M=rho L` original rows, bounded
row width and column degree, and let the balanced face multiset contain
`Theta(M)` repeats of each original row together with all pair-sum faces.
Choose an original row `h` containing two distinct coordinates `i,j`, and
choose a coordinate `k` outside their bounded incidence neighborhood.  On
one qubit set

```text
 Q_i=Q_j=X,       Q_k=Z,       Q_l=1 otherwise.          (STP1)
```

Use the same reflection on every equality copy.  The selected row is exact,
because its two nonidentity factors cancel.  Only `O(1)` original rows meet
`{i,j,k}`.  Their repeated copies and the pair sums involving them account
for `O(M)` out of `Theta(M^2)` balanced faces.  Every residual has operator
norm at most two, so the sum of their positive residual squares has the same
incidence bound.  Consequently both the normalized balanced energy and its
raw positive square-function operator satisfy

```text
 E_bal=O(1/L),       H<=C/L.                             (STP2)
```

Complete-pair commutator energy is even smaller: only the four ordered
pairs `(k,i),(i,k),(k,j),(j,k)` are nonzero.

For the anchor-odd parts `(SAF1)`,

```text
 Y_(k,i)=Y_(k,j)=X,
 Y_(k,i)^2Y_(k,j)^2=1.                                  (STP3)
```

The `Theta(M)` repeated copies of `h` occupy a `Theta(1/L)` fraction of the
balanced faces.  Choosing anchor `k` has probability `1/L`.  Hence the
left side of `(SAF3)` is bounded below by

```text
 c/L^2.                                                  (STP4)
```

On the other hand the anchor energy on the right is exactly

```text
 E_(a,l) tau(Y_(a,l)^2)=4/L^2,                           (STP5)
```

under ordered uniform averaging.  Thus their ratio stays bounded below by
`c/4` while the proposed parameter `b=C/L` tends to zero.  No estimate with
coefficient `o_b(1)` can hold for the unpeeled tuple.

This is not a far balanced microstate: resetting three coordinates costs
only `O(1/L)` in average squared generator distance.  The example therefore
does not obstruct basin capture.  It proves that sparse tail peeling or
cheap coordinate repair is logically prior to the fourth-moment Newton
estimate; a common low **average** square-function cut alone is insufficient.
