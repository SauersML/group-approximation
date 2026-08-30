---
rg: 2
id: stw93-residual-hereditary-exhaustion-proof
kind: route
title: Linearize locally, apply three-space permanence, and extend every residual trace
target: stw93-hereditary-exhaustion-reduces-to-traces
requires:
  - stw93-all-z-central-slices-generate-quasitrace-null-ideal
  - stw93-super-mcduff-tracial-central-quotient
  - stw01-extensions-preserve-qt-linearity
artifacts:
  - research/artifacts/stw93-hereditary-exhaustion-audit-2026-08-30.md
---

Put `E=bar(D)` and retain `R triangleleft E`.  First let `q` be a bounded
`2`-quasitrace on `R`.  If `x,y in R` are self-adjoint, the exhaustion
hypothesis places `{x,y}` in one `H_lambda`.  The restriction `q|H_lambda`
is a trace, so

```text
q(x+y)=q(x)+q(y).
```

Thus `q` is additive on all self-adjoint pairs and hence is a trace on `R`.
This argument needs containment of each finite packet, not a common unit for
the hereditary pieces.

For completeness, every finite subset of an arbitrary C*-algebra is
contained in some sigma-unital hereditary subalgebra.  Given
`x_1,...,x_m`, take a positive contraction obtained by rescaling

```text
h=sum_j (x_j*x_j+x_j x_j*).
```

The left and right support projections of every `x_j` are dominated by the
support projection of `h`; hence `x_j in Her(h)`.  The algebra `Her(h)` is
sigma-unital, with `(min(1,nh))` as an approximate unit.  Therefore the
stronger hypothesis concerning all sigma-unital hereditary subalgebras does
indeed supply the required family.

The quotient

```text
E/R = D/I
```

is a II_1 factor and has a unique normalized `2`-quasitrace.  Since both
`R` and `E/R` have bounded-quasitrace linearity,
`stw01-extensions-preserve-qt-linearity` shows that every bounded
`2`-quasitrace on `E` is a trace.  This is where the approximate-unit-net
version of the quasitracial-cut argument is essential: `R` itself need not
be sigma-unital even though it is exhausted by sigma-unital hereditary
pieces.

We now identify the exact remaining obstruction.  If `E` has a normalized
trace `s` different from the canonical limit trace, then `s|R` is nonzero:
otherwise `s` would factor through the unique-trace quotient `E/R` and
would equal the canonical trace.  Hence uniqueness of the trace on `E`
implies that `R` has no nonzero bounded trace.

Conversely, let `theta` be a nonzero bounded trace on `R`.  Its canonical
finite tracial extension `tilde(theta)` to `M(R)` can be composed with the
unital multiplication homomorphism

```text
E -> M(R).
```

The resulting bounded trace on `E` restricts to `theta` and takes the value
`||theta||` at `1_E`.  After normalization it is a trace on `E` which
charges `R`, so it differs from the canonical trace.  This proves `(b)` if
and only if `(c)`.  Because every quasitrace on `E` is already a trace,
`(c)` is equivalent to `(d)`, and `(a)` is equivalent to either one by the
unique-quasitrace quotient.  This proves all four equivalences.

**Sharpness.**  Let `E=C direct_sum C`, `R=0 direct_sum C`, and take the
canonical trace to be evaluation on the first summand.  Then `E/R=C`, while
`R` itself is finite-dimensional, sigma-unital, hereditary, and
quasitrace-rigid.  Nevertheless evaluation on the second summand is a
normalized trace charging `R`.  Thus no hereditary exhaustion hypothesis
which only proves quasitrace linearity can imply annihilation; bounded
residual traces are a genuine separate obstruction.
