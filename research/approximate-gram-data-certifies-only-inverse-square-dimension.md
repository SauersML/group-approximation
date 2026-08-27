---
rg: 2
id: approximate-gram-data-certifies-only-inverse-square-dimension
kind: claim
title: Approximate orthogonality at precision epsilon certifies dimension at most of order one over epsilon squared
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  marked-clifford-table-exponential-dimension: that certifies exponential dimension from an all-pairs epsilon-homomorphism by exactification and integrality; this proves that trace data alone, without exactification, can never certify more than inverse-square dimension, which is why the all-pairs hypothesis cannot be weakened to approximate traces.
  dimension-kleene-threshold-needs-amplification-envelope: that is a logical obstruction about thresholds learned after halting; this is a linear-algebra bound on what approximate inner-product data can force, independent of any search.
---

Let `v_1,...,v_N` be unit vectors in an inner-product space with
`|<v_i,v_j>|<=epsilon` for `i!=j`.  Then

```text
dim span{v_i} >= N/(1+(N-1)epsilon^2) >= min(N, 1/epsilon^2)/2,    (GS1)
```

and this is sharp up to a logarithm: for every `epsilon` and `N` there are
such vectors in dimension `O(epsilon^(-2) log N)` (normalized codewords of a
binary code of relative distance `(1-epsilon)/2`, which Gilbert--Varshamov
supplies with `2^(Omega(epsilon^2 n))` words).

*Proof.*  The Gram matrix `Gamma` has rank equal to the span dimension,
trace `N`, and `tr Gamma^2<=N+N(N-1)epsilon^2`; Cauchy--Schwarz on its
nonzero eigenvalues gives `rank>=(tr Gamma)^2/tr Gamma^2`.

**For word data.**  In `M_d(C)` with the normalized Hilbert--Schmidt inner
product the ambient dimension is `d^2`.  Any family of `N` word evaluations
with pairwise normalized traces `|tr(w_i(U)^*w_j(U))|<=epsilon` certifies
only `d>=(min(N,1/epsilon^2)/2)^(1/2)`.  The `4^n` Pauli words, exactly
orthogonal in an exact `J=-1` representation and hence forcing `d>=2^n`,
force only `d>=min(2^n,1/epsilon)` at precision `epsilon`.

**Design consequence.**  Hyperlinear microstates supply defect tending to
zero with no rate against dimension.  Therefore no route can reach
unbounded dimension at fixed precision from traces of words; it must pass
through an exact object with an integrality constraint (an exactified
finite group's irreducible dimension, a rank, a multiplicity), and
exactifying an `n`-fold structure from relator or pairwise data costs
precision growing with `n`.  That cost is where "dimension explosion"
routes pay the area, and it is why the remaining compiler problem is a
uniform stability statement for an infinite structure rather than a
better counting argument.
