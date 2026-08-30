---
rg: 2
id: stw22-matrix-to-hyperfinite-field-trace-continuity
kind: claim
title: A growing-matrix field with hyperfinite limit fibre has only uniform traces
distinct_from:
  stw22-nuclear-convergent-sequence-has-nonzero-tracefree-gap: that theorem uses the constant hyperfinite fibre over the whole convergent sequence; the present theorem has finite matrix fibres at every isolated point and a type II_1 fibre only at the limit, so the bundle is not locally trivial or a trivial factor field.
  stw22-locally-trivial-finite-dimensional-bundles: every locally trivial R-bundle is globally trivial by Evington--Pennig; the present field is genuinely non-locally-trivial because its fibre type and matrix dimension change at every isolated point.
artifacts:
  - research/artifacts/stw22-matrix-to-hyperfinite-field-audit-2026-08-30.md
---

Let `U` be an infinite-dimensional UHF algebra with unique trace `tau`, and
fix an increasing sequence of unital full matrix subalgebras

```text
F_1 subset F_2 subset ... subset U,       closure(union_n F_n)=U.
```

Represent all these algebras in the tracial GNS representation and write
`R=pi_tau(U)''`.  Define

```text
A={ (a_infinity,a_1,a_2,...):
      a_infinity in U, a_n in F_n, ||a_n-a_infinity|| -> 0 }.
```

Then `A` is a separable unital nuclear C*-algebra.  Its extreme trace
boundary is the convergent sequence

```text
X={infinity,1,2,...},
```

and its uniform tracial completion is canonically

```text
M={ (a_infinity,a_1,a_2,...):
      a_infinity in R, a_n in F_n, sup_n ||a_n||<infinity,
      ||a_n-a_infinity||_2 -> 0 }.
```

Every tracial state on `M` is uniquely

```text
a |-> mu({infinity}) tau(a_infinity)
     + sum_n mu({n}) tr_(F_n)(a_n)
```

for a probability measure `mu` on `X`.  In particular, every trace on `M`
is continuous for the uniform `2`-norm, so STW Problem XXII has a positive
answer for this non-locally-trivial, changing-fibre nuclear class.

The norm/`2`-norm fibre gap at infinity is nonzero:

```text
K_infinity/J_infinity
 ~= { (a_n) in product_n F_n: ||a_n||_(2,tr_(F_n)) -> 0 }
      / { (a_n): ||a_n|| -> 0 }.
```

Nevertheless it has no nonzero bounded positive trace.  Thus the conclusion
does not come from equality of the norm and `2`-norm fibres, and this example
lies outside both the constant-field theorem and the Evington--Pennig
triviality theorem for locally trivial `R`-bundles.
