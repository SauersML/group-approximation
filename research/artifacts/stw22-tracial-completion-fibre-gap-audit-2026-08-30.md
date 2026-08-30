# STW Problem XXII: norm-fibre versus 2-norm-fibre audit

## Source status

Problem XXII asks whether every trace on the uniform tracial completion of
`A` is automatically continuous for the uniform `2`-norm.  The v2 source
records the general and nuclear cases as open.  It records positive answers
for finite-dimensional trace simplices, complemented partitions of unity,
and specified low-dimensional Bauer cases.

## The tempting fibrewise argument and its gap

For a compact tracial `C(X)`-bundle, an extreme trace restricts to evaluation
at one point `x`.  It therefore kills the C*-norm ideal

```text
J_x=closure(C_0(X\{x})M)
```

and factors through the norm fibre `M/J_x`.  The canonical tracial fibre,
however, is

```text
M/K_x,             K_x={a:tau_x(a*a)=0},
```

and only `J_x subset K_x` is automatic.  Unique trace on the II_1 factor
`M/K_x` says nothing about traces on `M/J_x` which detect `K_x/J_x`.
Disintegration therefore lands one quotient too early.

## Exact criterion

When a center-valued trace `E:M->C(X)` is available and every `M/K_x` has a
unique trace, all traces on `M` are the canonical measures `mu o E` if and
only if every trace on every norm fibre kills `K_x/J_x`.  Equivalently, each
norm fibre itself must be uniquely traced.

The proof uses only factoriality of extreme tracial GNS representations,
Cauchy--Schwarz, and Krein--Milman.  It gives the positive trivial-field case
`C(X) tensor M_0`, where faithfulness in the finite-factor fibre makes
`J_x=K_x`.  It does not claim that equality for a general uniform tracial
completion.
