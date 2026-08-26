---
rg: 2
id: odd-maslov-homogeneous-coefficients-have-a-uniform-folner-gap
kind: claim
title: Odd Maslov homogeneous coefficients have a dimension-uniform Folner boundary gap
invalidates:
  - odd-maslov-llp-via-vanishing-defect-homogeneous-retract
distinct_from:
  odd-maslov-homogeneous-coefficients-have-a-fixed-size-defect-gap: that uses compactness separately at each coefficient size; this proves one positive constant simultaneously for all matrix sizes by turning the coefficient defect into projective Folner boundary.
  deligne-fixed-projective-representation-folner-compression-no-go: that excludes a vanishing finite-rank boundary sequence inside one fixed exact projective representation; this direct-sums the varying coefficient GNS representations so that theorem applies and yields a uniform coefficient inequality.
  matrix-homogeneous-ucp-retracts-can-hide-defect: that same-twist construction hides positive defect but has a trivial difference multiplier and an invariant scalar summand; this uses the odd Maslov difference multiplier and excludes even asymptotically small hidden defect in unbounded coefficient degree.
  maslov-bounded-block-sector-gap: that treats bounded invariant blocks of approximate unitary tuples; this treats arbitrary contractive homogeneous ucp coefficients in all matrix sizes without any invariant-block hypothesis.
---

Use `Gamma`, `alpha`, `epsilon`, `delta`, and the symmetric generating set
`S` from
`odd-maslov-homogeneous-coefficients-have-a-fixed-size-defect-gap`.  There is
one constant

```text
kappa_hom>0                                               (OUF1)
```

such that for every matrix size `n` and every normalized
`M_n`-valued `delta`-projective positive-definite function `C`,

```text
sum_(s in S) tr_n(2I-C_s^*C_s-C_sC_s^*) >= kappa_hom.   (OUF2)
```

The constant is independent of `n`.  Consequently every homogeneous
odd-to-even ucp map

```text
i(u_g^alpha)=C_g tensor u_g^epsilon                     (OUF3)
```

pays a macroscopic coefficient defect on the canonical generating set.  If
`i` has a ucp left inverse, that left inverse must kill positive generator
defect of total normalized coefficient trace at least `kappa_hom`.

## Scalarization consequence

The unbounded-degree escape left open by the fixed-size compactness argument
does not exist.  In particular, no sequence of homogeneous odd-to-even split
ucp retracts can approach the scalar/projective homogeneous line by making
its coefficient multiplicative defects tend to zero, regardless of how fast
the matrix amplification grows.

This does not by itself rule out a homogeneous split retract.  A nonfaithful
retraction may still kill a positive boundary ideal of fixed macroscopic
coefficient mass, just as abstract ucp countermodels can hide positive
defect.  What `(OUF2)` rules out is precisely the proposed quantitative
Maslov scalarization mechanism after matrix-homogeneous covariance: the
hidden boundary cannot become asymptotically negligible.  Any positive LLP
transfer through such a retract must use that macroscopic nonmultiplicative
boundary rather than perturb it toward a scalar Morita bridge.

