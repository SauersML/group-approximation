---
rg: 2
id: separate-packet-calculi-have-no-common-matching
kind: claim
title: Separate finite-packet calculi cannot select a positive-mass common multiplicity matching
distinct_from:
  packet-natural-selectors-cannot-extract-one-bounded-copy: that treats one isotypic packet and rules out a proper natural reducing projection; this also rules out the full-carrier matching between two independently gauged reservoirs and gives a quantitative Haar obstruction.
  canonical-finite-packet-data-stop-at-scalar-overlaps: that computes all scalar overlap information supplied by canonical finite packets; this proves the corresponding selector-and-matching no-go for spectral, Gram, PI, and exterior-power rules.
  atlas-shifted-factorizations-have-independent-right-gauge: that identifies independent gauges on existential factorizations of one common Atlas unitary; this concerns independent external multiplicity reservoirs before a literal mixed block has identified their gauges.
  one-cross-gram-moment-extracts-the-common-polar-gauge: that gives a positive polar construction after a mixed cross-reservoir operator with sufficiently large Gram mass is supplied; this proves such a mixed operator is necessary for the natural selector classes.
---

Let two authenticated irreducible finite-packet carriers be

```text
H_i=V_i tensor M_i,       pi_i(f)=rho_i(f) tensor I_(M_i),   i=0,1. (SPC1)
```

Suppose the available input consists only of represented packet operators
inside each carrier, with no named operator from `H_0` to `H_1`.  A rule
natural under unitary equivalence is asked to return multiplicity cuts
`p_i in B(M_i)` and a matching

```text
J:p_0 M_0 -> p_1 M_1.                                      (SPC2)
```

Then

```text
p_i=0 or I_(M_i),       and       J=0.                      (SPC3)
```

Indeed the represented input is fixed by every independent multiplicity
gauge `(W_0,W_1) in U(M_0) times U(M_1)`.  Naturality therefore gives

```text
W_i p_i W_i^*=p_i,
W_1 J W_0^*=J.                                             (SPC4)
```

The commutant of `U(M_i)` in `B(M_i)` is the scalars, proving the first
assertion.  In the second equation take `W_0=I` and `W_1=-I`; then `J=-J`,
so `J=0`.

There is also a sharp normalized-Hilbert--Schmidt form.  If `p` is a
projection of normalized trace `t`, Haar averaging gives

```text
E_W ||WpW^*-p||_2^2 = 2t(1-t).                            (SPC5)
```

For a rectangular matching `J`, using the same fixed normalization on both
terms,

```text
E_(W_0,W_1) ||W_1 J W_0^*-J||_2^2 = 2||J||_2^2.           (SPC6)
```

For `(SPC5)`, Haar twirling sends `p` to `tI`, and expansion of the square
gives `2t-2t^2`.  For `(SPC6)`, both squared-norm terms equal
`||J||_2^2`, while the mixed inner product has Haar average zero.  Thus an
approximately gauge-natural matching of normalized mass `mu=||J||_2^2`
has some independent gauge with covariance residual at least `sqrt(2mu)`.
In particular no positive fixed mass can have covariance loss tending to
zero with packet defect, because the packet defect is exactly zero along
the whole gauge orbit.

This covers every construction made separately from the two finite regular
packet tables by star-polynomials, central or ordinary polynomial identities,
spectral calculus, within-reservoir Gram matrices, fixed tensor operations,
or exterior powers followed by a natural map back to the original carriers.
All those operations are functorial under `(W_0,W_1)`.  Exterior powers may
detect a dimension or create determinant lines in auxiliary spaces, but a
natural matching returned on the original reservoirs still obeys `(SPC4)`.
Spectator amplification and direct sums preserve the same obstruction.

The conclusion changes only after the input contains an authenticated mixed
block

```text
T:H_0 -> H_1,       T |-> W_1 T W_0^*.                    (SPC7)
```

For Atlas, the legal relative-coordinate compression `P_i U Q_j` is such a
block even though `U` is a coordinate obtained after finite-chart
exactification rather than a group word.  Its polar partial isometry is
covariant rather than invariant and can match
equal-rank spectral cuts of `T^*T` and `TT^*`.  Therefore any Atlas common-cut
acquisition using these natural selector classes must name such a mixed word
block or relative-coordinate compression, prove its source and target types
from the same quotient relation, and prove a fixed lower bound on its selected
Gram mass.  Separate regular
`A8`, `S4`, or `S3` carrier data cannot supply the matching.
