---
rg: 2
id: corner-localized-non-ce-bcs-energy-gap-proof
kind: route
title: Normalize the bad corners and pass their polar compressions to a tracial matrix ultraproduct
target: corner-localized-non-ce-bcs-energy-gap
requires:
  - mipstar-bcs-tracial-nonru-exists
---

Suppose `(CLG1)` fails.  There are dimensions `d_n`, unitary tuples
`Z_x^(n)`, and nonzero projections `Q_n` such that, with
`q_n=tau_(d_n)(Q_n)`, the left side of `(CLG1)` is `o(q_n)`.  Give
`Q_n M_(d_n) Q_n` its normalized trace.  The ranks of `Q_n` may stay bounded;
this causes no difficulty because a bounded-rank subsequence is already a
sequence of matrix algebras.

Put `A_(x,n)=Q_n Z_x^(n) Q_n`.  The two off-diagonal corners of `Z_x^(n)`
have equal squared Hilbert--Schmidt norm, and

```text
||Q_n-A_(x,n)^* A_(x,n)||_(2;Q_n)^2
+ ||Q_n-A_(x,n) A_(x,n)^*||_(2;Q_n)^2 -> 0.           (CLG2)
```

Indeed their trace defects are bounded by
`||[Q_n,Z_x^(n)]||_(2,d_n)^2/q_n`.  Functional calculus, or the polar
decomposition after filling the kernels by an arbitrary unitary, gives a
unitary `U_(x,n)` on `Q_n C^(d_n)` with

```text
||U_(x,n)-A_(x,n)||_(2;Q_n) -> 0.                     (CLG3)
```

For every fixed noncommutative polynomial `P`, repeated insertion of `Q_n`
and telescoping across its finitely many letters gives

```text
||P(U_n)-Q_n P(Z^(n)) Q_n||_(2;Q_n) -> 0              (CLG4)
```

whenever all the commutators in `(CLG1)` are divided by `sqrt(q_n)` and tend
to zero.  Apply `(CLG4)` to the finite list `R_B`.  The localized defect terms
in `(CLG1)`, again divided by `q_n`, show that

```text
||R(U_n)||_(2;Q_n) -> 0  for every R in R_B.           (CLG5)
```

Pass `(U_(x,n))` to a tracial ultraproduct of the corner matrix algebras.
The square relations make the limiting unitaries self-adjoint involutions;
the contextual commutators vanish; and every ordered forbidden product
vanishes in `L^2`, hence as an operator.  The limit therefore gives a unital
representation of the BCS algebra into a tracial matrix ultraproduct.
Composing with its trace produces a Connes-embeddable tracial state, contrary
to the choice of `B`.  This proves `(CLG1)`.

No quantitative polar-decomposition constant is hidden in the conclusion:
the theorem only asserts existence of the fixed positive
`beta_B^corner`, and the contradiction argument is uniform over dimensions,
corner ranks, and tuples.
