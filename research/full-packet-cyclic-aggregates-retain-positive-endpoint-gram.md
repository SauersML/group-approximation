---
rg: 2
id: full-packet-cyclic-aggregates-retain-positive-endpoint-gram
kind: claim
title: Full-packet odd cyclic aggregates retain a uniform signed endpoint Gram
artifacts:
  - research/full-packet-cyclic-aggregate-gram-proof.md
distinct_from:
  endpoint-order-five-actor-has-half-gram: that proves the sharp one-third bound on the unaggregated literal p2 source; this transports that bound to the C- and M-invariant orbit joins, with the unavoidable orbit-size dilution.
  cyclic-endpoint-sheet-aggregation-has-zero-gram-profile: that deletes the literal G1-to-K1 return incidences and proves the odd cyclic relators alone allow zero Gram; this uses the complete native packet, whose returning GL3 subgroup excludes that profile.
---

**ESTABLISHED POSITIVE CYCLIC AGGREGATES.**  In the complete native packet
of `endpoint-order-five-actor-has-half-gram`, put

```text
C=WM,              C^5=1,             M^7=1,
p=p_2,              p*=p(WpW),
tau(p*) >= (1/3)tau(p).                                (FCA1)
```

For `U=C,M`, define the invariant orbit join

```text
E_U=join_(j=0)^(ord(U)-1) U^j p U^-j.                  (FCA2)
```

Then `U E_U U^-1=E_U`, `p<=E_U`, and

```text
tau(E_C)<=5 tau(p),             tau(E_M)<=7 tau(p).    (FCA3)
```

Since `p*<=p<=E_U` and `p*<=WpW<=W E_U W`, the common endpoint overlap
satisfies

```text
E_U meet (W E_U W) >= p*.                              (FCA4)
```

Consequently the literal compressed Whitehead has

```text
||E_C W E_C||_2^2 >= (1/15)tau(E_C),
||E_M W E_M||_2^2 >= (1/21)tau(E_M).                   (FCA5)
```

Thus either exact odd cyclic aggregation retains positive signed-source
mass and a dimension-independent Whitehead cross Gram.  If the original
`p_2` lies on positive marked mass, so does `E_U` because it contains
`p_2`.  Orthogonalizing the finite family of translates does not change
its join or these estimates.

The conclusion is positivity, not the raw half Gram.  More importantly,
the positive meet in `(FCA4)` is not shown to reduce `U`.  Hence the odd
relations `C^5=1` or `M^7=1` cannot yet be restricted to the common overlap
to remove its polar reservoir gauge.  The aggregation closes the mass/Gram
question but does not close the native unequal-selector occurrence typing.

No Property `(T)`, canonical trace, literature theorem, local computation,
or Lean compilation is used.

DERIVATION
full-packet-cyclic-aggregate-gram-proof
