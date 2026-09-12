---
rg: 2
id: stw74-uniform-gapless-compression-proof
kind: route
title: Combine minimal matrix level with compactness of the scalar direction space
target: stw74-minimal-projection-has-uniform-gapless-compressions
requires:
  - stw74-counterexamples-have-stationary-matrix-thresholds
  - stw74-projectionless-corner-forces-gapless-compressions
---

Apply the stationary-threshold theorem to `a`, discard its finite initial
segment, and relabel.  It gives `m>=2` and the displayed tower `(H_k)`.
Choose any nonzero projection

```text
p in M_m(H_1).
```

The same projection belongs to `M_m(H_k)` for every `k`, so no choice of
projections varying along the tower is needed.  The stationary-threshold
theorem also makes `p` properly infinite and identifies its stabilized
Cuntz class with `[1_A]`.

We first prove that no scalar compression vanishes.  Suppose that
`||xi||=1` and

```text
b_xi=(xi* tensor 1)p(xi tensor 1)=0.
```

Regarding `xi tensor 1` as a multiplier column and using `p=p*=p^2`,

```text
b_xi=(p(xi tensor 1))^*p(xi tensor 1),
```

so `p(xi tensor 1)=0`.  Choose a scalar unitary `U in M_m(C)` whose last
column is `xi`.  The last column of `U* p U` is zero, and self-adjointness
makes its last row zero.  Hence

```text
U* p U = q direct-sum 0
```

for a nonzero projection `q in M_(m-1)(H_1)`.  This contradicts minimality
of `m`.  Therefore `b_xi!=0` for every unit `xi`.

The map

```text
xi mapsto b_xi
```

is norm continuous on the compact unit sphere of `C^m`.  Its norm is a
strictly positive continuous function there, so it has a positive minimum;
call that minimum `delta`.  Since multiplication of `xi` by a scalar of
modulus one does not change `b_xi`, the map factors continuously through
`CP^(m-1)`.

Finally `b_xi` is a nonzero positive element of `H_1 subset D`.  The
gapless-compression theorem applies because `D` is projectionless and shows
that zero is an accumulation point of its nonzero spectrum.  Explicitly, a
gap after zero would make the support function continuous on the spectrum
and produce a nonzero projection in `C*(b_xi) subset D`.  This proves the
uniform norm floor and simultaneous gaplessness claimed above.

The minimal-level argument supplies only a norm floor, not a uniform lower
spectral gap; projectionlessness proves that every individual compression
has the opposite spectral behaviour.  No comparison, cancellation,
property (QQ), or regularity hypothesis is used.
