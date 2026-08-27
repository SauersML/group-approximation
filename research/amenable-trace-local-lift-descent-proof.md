---
rg: 2
id: amenable-trace-local-lift-descent-proof
kind: route
title: Lift finite operator systems and absorb the kernel in trace two-norm
target: amenable-trace-descends-through-locally-liftable-quotient
requires: []
---

Use the finite-dimensional u.c.p. approximation characterization of amenable
traces. Fix a finite set `F subset B` and include in a finite-dimensional
operator system `E` the elements of `F`, their adjoints, and all products
`xy` with `x,y in F`. Choose a u.c.p. local section

```text
s:E -> A,                 q o s=id_E.                   (ATL1)
```

For `x,y in F` put

```text
d_(x,y)=s(xy)-s(x)s(y).
```

Then `q(d_(x,y))=0`, so trace preservation gives

```text
tau_A(d_(x,y)^*d_(x,y))=0.                              (ATL2)
```

Amenability of `tau_A` supplies u.c.p. maps `Psi:A -> M_n` which, on the
finite set consisting of all `s(x)`, their products, the `d_(x,y)`, and the
positive elements `d_(x,y)^*d_(x,y)`, simultaneously approximate `tau_A`
and multiplication in normalized Hilbert--Schmidt norm. By Schwarz and
`(ATL2)`,

```text
||Psi(d_(x,y))||_2 -> 0.                                (ATL3)
```

Therefore

```text
||Psi(s(xy))-Psi(s(x))Psi(s(y))||_2 -> 0,               (ATL4)
tr(Psi(s(x))) -> tau_A(s(x))=tau_B(x).                  (ATL5)
```

The u.c.p. map `Psi o s:E -> M_n=B(C^n)` extends by Arveson's theorem to a
u.c.p. map `Phi:B -> M_n`. On `F` it satisfies `(ATL4)--(ATL5)`. Directing
these choices over finite sets and tolerances gives the standard u.c.p.
approximation net for `tau_B`, hence `tau_B` is amenable.
