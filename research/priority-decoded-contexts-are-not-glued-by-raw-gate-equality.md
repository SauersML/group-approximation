---
rg: 2
id: priority-decoded-contexts-are-not-glued-by-raw-gate-equality
kind: claim
title: Raw gate equality and gate aggregation do not glue priority-decoded contexts
distinct_from:
  zpc-context-mismatch-transducer: that asks for a positive context-coupled LCS construction; this rules out two natural candidate couplings without claiming that every transducer is impossible.
  odd-selector-priority-decoding: that proves lossless decoding inside one selector context; this shows that the resulting decoded observable is not functorial under equality of the raw gate variables across different selector contexts.
---

Let two contexts `c,d` each have two commuting selector involutions with exact
odd parity, and let their two raw gate involutions agree branch by branch:

```text
G_(c,a)=G_(d,a),                 a=1,2.
```

Even if every gate commutes with every selector in its own context, the
priority-decoded observables

```text
U_c = sum_a Q_(c,a) G_(c,a),
U_d = sum_a Q_(d,a) G_(d,a)
```

need not agree.  There is an exact model in `M_2(C)` in which all raw gate
equalities and both selector parity equations have zero defect while

```text
||U_c-U_d||_2^2 = 4.
```

Nor can a shared observable be recovered under priority decoding by imposing
the aggregate relation

```text
U = product_a G_a.
```

For three selectors there is a scalar exact odd-parity model with
`product_a G_a=+1` but priority-decoded observable `-1`.

Finally, raw gate equality is not even completeness-preserving for canonical
predication.  If `P,R` are the active projections in two contexts, `U`
commutes with both, and

```text
G_P=1-P+PU,       G_R=1-R+RU,
```

then

```text
G_P-G_R=(P-R)(U-1),
```

which need not vanish.  Consequently a successful
`zpc-context-mismatch-transducer` must couple the selector allocation to the
payload mismatch.  Equality rows on raw gates, or equality of their unweighted
products, cannot supply `(CTX')` while retaining the overlap-tolerant priority
decoder.
