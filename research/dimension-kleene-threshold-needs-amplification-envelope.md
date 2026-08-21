---
rg: 2
id: dimension-kleene-threshold-needs-amplification-envelope
kind: claim
title: A dimension-dependent Kleene threshold needs a positive amplification envelope
distinct_from:
  dimension-matched-kleene-microstate-diagonal: that uses one fixed positive defect threshold and therefore crosses every hyperlinear approximation sequence; this identifies the exact extra rate hypothesis needed if the threshold is allowed to depend on the reported dimension.
  instance-modulated-kleene-microstate-diagonal: that permits dependence on the source code but keeps one fixed threshold after the fixed point is chosen; this rules out arbitrary dependence on data printed only when the search halts.
  adaptive-tensor-amplification: that converts operator separation to normalized-HS separation at a dimension cost; this studies tensor amplification of an already normalized-HS tuple and the soundness threshold at its enlarged dimension.
---

Let `delta:N_(>0)->Q_(>0)` be a computable proposed soundness threshold for a
compiler whose halting machine reports the dimension to which soundness
applies.  For a tuple of dimension `d`, tensor amplification permits the
fixed-point search to output any multiple `kd` without changing either its
normalized-HS relator defect or its marked distance.  Define the amplification
envelope

```text
Delta(d)=sup_(k>=1) delta(kd).                                  (DKE1)
```

The dimension-reported Kleene argument can force its search to halt from a
hyperlinear microstate sequence `(d_n,epsilon_n)` only if

```text
epsilon_n<Delta(d_n)                                            (DKE2)
```

for some `n` whose marked distance is already above the search cutoff.  In
particular, the dimension-free condition

```text
inf_(d>=1) Delta(d)>0                                           (DKE3)
```

is sufficient: search simultaneously over tuples and amplification factors,
and output `kd` when the amplified tuple enters the `delta(kd)` window.

Mere pointwise positivity of `delta(D)` is not sufficient.  Abstract defect
profiles

```text
epsilon_d=1/d,                 delta(D)=exp(-D)                  (DKE4)
```

have `inf_d epsilon_d=0`, as hyperlinearity requires at the level used by the
diagonal proof, but

```text
epsilon_d>=delta(kd)                  for every d,k>=1.          (DKE5)
```

Thus no amplified witness enters its dimension-dependent search window.  This
is a logical obstruction to the proposed weakening, not an assertion that
`(DKE4)` is realized by a particular group presentation.

Consequently the universal-in-`D` defect modulus in the current
dimension-reported Clifford and Pauli compilers is load-bearing.  It may be
replaced by `(DKE2)` for every possible canonical microstate profile, or by a
checkable sufficient condition such as `(DKE3)`, but not by an arbitrary
positive post-halting modulus.

The same obstruction survives the more adaptive proposal in which the
fixed-point program computes the van-Kampen/Higman/Clifford area of the
certificate that would result from halting on the candidate currently under
inspection.  See `halt-now-certificate-area-still-needs-a-crossing-envelope`:
the reciprocal area is merely a candidate- and time-dependent search window,
and hyperlinearity supplies no diagonal rate forcing a candidate into it.
