---
rg: 2
id: sl3-arithmetic-inclusion-is-not-re-over-lattice
kind: claim
title: The SL3 lattice factor inclusion is not relatively embeddable over the lattice factor
distinct_from:
  arithmetic-pair-is-not-relatively-embeddable: that bundles rank two and rank three and asks for failure over every Connes-embeddable coefficient factor; this is the single weakest SL3 instance RE over L(SL3(Z)), now exactly equivalent to non-hyperlinearity of the plain arithmetic double.
  sl3-canonical-double-has-a-correctable-vertex: that is a sufficient matrix-coordinate correction theorem for canonical double microstates; this is the exact relative-embeddability obstruction and does not require correcting either vertex.
---

OPEN.  For

```text
L(SL_3(Z)) subset L(SL_3(Z[1/2])),
```

the inclusion is not `RE/L(SL_3(Z))` in Gao's sense.

By `sl3-arithmetic-double-hyperlinear-iff-relative-embeddable`, this is
equivalent to non-hyperlinearity of

```text
SL_3(Z[1/2]) *_(SL_3(Z)) SL_3(Z[1/2]).                        (SNR1)
```

It is therefore the exact operator-algebraic form of the simultaneous
two-vertex-outlier terminal, not merely a sufficient strengthening.  Gao's
definition says a refutation consists of a trace-preserving embedding of
`L(A)` into an ultraproduct `prod(A_k tensor L(C))` with hyperfinite
subalgebras `B_k subset A_k` forming the required commuting square over
`L(C)`.  A proof must exclude all such relative models.

`gao-re-witness-carries-orthogonal-arithmetic-hecke-tower` gives the
sharpest intrinsic reduction presently available: every hypothetical
witness must coordinate-realize all mutually orthogonal bifinite
double-coset correspondences, including the relative-Haar tower generated
by the dyadic diagonal.  `sl3-lattice-inclusion-is-quasiregular-not-mixing`
shows why property `(T)`, mixing, and quasi-normalizer arguments alone do
not exclude it.  The unresolved input must use coordinate hyperfiniteness
of the `B_k` together with the simultaneous Hecke fusion/dimension data.

Because the coefficient `L(C)` is Connes embeddable and hence QWEP, Gao
Proposition 2.2 removes it: see
`sl3-re-over-lattice-iff-re-over-scalars`.  Thus this claim is equivalent
to `sl3-arithmetic-inclusion-is-not-re-over-scalars`, where the target is a
commuting-square embedding into an ultraproduct of QWEP finite algebras
with hyperfinite carrier subalgebras and no auxiliary factor coordinate.
