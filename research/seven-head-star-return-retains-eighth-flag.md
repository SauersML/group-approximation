---
rg: 2
id: seven-head-star-return-retains-eighth-flag
kind: claim
title: A seven-head Coxeter reset retains the marked-star eighth flag
artifacts:
  - research/seven-head-star-return-support-proof.md
distinct_from:
  four-cell-marked-star-has-an-eighth-head-flag: that proves the shortest three-head word has an eighth source but a four-cycle optimistic holonomy; this inserts the shortest Coxeter reset found after that word and recovers an involutory optimistic holonomy without losing the eighth source.
  marked-star-asymmetric-heads-have-half-quarter-sources: that gives the first two literal source flags and isolates their cumulative three-cycle; this uses four cells and a six-step rank-two Coxeter loop before the third head.
  binary-leavitt-two-shared-gauge-selector-compiler: that needs actual native quarter/eighth outputs carrying conjugate authenticated gauges; this proves an exact eighth support and cancels the formal Coxeter product, but does not authenticate the compressed head gauges.
---

Retain the four-cell marked-star carrier `E_4` and the three asymmetric
heads `H_1,H_2,H_3` from
`four-cell-marked-star-has-an-eighth-head-flag`.  Put

```text
R_8=H_3(H_2H_1)^3.                                    (SHR1)
```

Then the compression `E_4R_8E_4` is a partial isometry with exact source
and range projections

```text
(E_4R_8E_4)^*(E_4R_8E_4)
  =E_4(1-Z_2)(1+Z_3)(1+Z_4)/8,

(E_4R_8E_4)(E_4R_8E_4)^*
  =E_4(1+Z_2)(1-Z_3)(1+Z_4)/8.                        (SHR2)
```

Thus both supports have relative rank `1/8` on every finite-dimensional
trace profile.  The longer return really retains all three independent
star signs; it does not suffer the half-rank collapse of the shortest
involutive palindrome.

There is also a genuine Coxeter improvement.  If, only for the purpose of
auditing the remaining occurrence typing, the three compressed head polars
are assigned the corresponding adjacent Whitehead reservoir involutions
`V_1,V_2,V_3`, then the reservoir word of `(SHR1)` is

```text
V_3(V_2V_1)^3=V_3.                                    (SHR3)
```

The equality uses only the type-`A_2` Coxeter relations for `V_1,V_2`.
Hence the first six head occurrences form an identity reservoir loop, and
the surviving formal holonomy is the native involution `V_3`, not a
three- or four-cycle.  A finite symbolic search through reduced signed head
words confirms that no shorter word has simultaneously rank-three source,
rank-three range, and transposition Coxeter image; the exact theorem here
uses only the displayed word and does not depend on that minimality search.

This does **not** close the native selector compiler.  The actual
compressions of the `H_i` do not reduce `E_4`, and the existing order-seven
relations `(J_iH_i)^7=1` cannot be restricted to `E_4` without paying the
known compression leakage.  Consequently `(SHR3)` is an exact statement
about the already authenticated Whitehead gauges under the favorable
head/Whitehead identification, not a proof of that identification.  The
remaining seam is now narrower: authenticate the gauge of the seven-head
partial return, or attach the six-head Coxeter reset to the literal
Whitehead packet by an odd identity-outer occurrence.

No Property `(T)`, Kazhdan input, canonical trace, stability theorem, or
literature input is used.

DERIVATION
seven-head-star-return-support-proof
