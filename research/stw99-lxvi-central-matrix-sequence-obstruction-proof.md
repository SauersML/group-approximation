---
rg: 2
id: stw99-lxvi-central-matrix-sequence-obstruction-proof
kind: route
title: Fold an infinite doubled unit through central matrix units and lift the resulting isometry
target: stw99-lxvi-central-matrix-sequence-obstruction
requires: []
---

Write `A_infinity=ell_infinity(A)/c_0(A)`, and let `(e_ij)` be matrix
units for a unital copy of `M_2` in `A_infinity cap A'`.  Define

```text
Theta : M_2(A) -> A_infinity,
Theta((a_ij)) = sum_(i,j=1)^2 e_(i1) a_ij e_(1j).
```

Centrality of the `e_ij` gives

```text
Theta(x)Theta(y)=Theta(xy),
Theta(x*)=Theta(x)*,
Theta(1)=e_11+e_22=1.
```

Thus `Theta` is a unital \*-homomorphism.  Since `A` is simple,
`M_2(A)` is simple, so `Theta` is injective.

Suppose that `M_2(A)` has infinite unit.  Choose `v in M_2(A)` with

```text
v* v=1,                 r=1-v v*>0.
```

Then `w=Theta(v)` is an isometry in `A_infinity`, and its defect
`Theta(r)` is a nonzero projection by injectivity.  Choose a bounded
representing sequence `(w_n)` in `A` for `w`.  The quotient identities give

```text
||w_n* w_n-1|| -> 0,
limsup_n ||1-w_n w_n*|| = 1.
```

After passing to a subsequence, the second quantity converges to `1`.

For all sufficiently large `n`, `w_n* w_n` is invertible.  Its polar
correction

```text
s_n=w_n (w_n* w_n)^(-1/2)
```

is an isometry in `A`, and `||s_n-w_n|| -> 0`.  Along the chosen subsequence,
hence
`||1-s_n s_n*|| -> 1`; in particular, `s_n s_n*` is not `1` for all large
`n`.  Thus `A` contains a nonunitary isometry and its unit is infinite.

For the final assertion, if a unital CAR algebra `D` is contained in `A` and
one can choose unital first-factor copies `M_2 -> D` from farther and farther
out in the CAR tensor decomposition whose matrix units asymptotically commute
with every element of `A`, those matrix units define precisely a unital
embedding `M_2 -> A_infinity cap A'`.  The preceding argument rules this out
when `A` is finite and `M_2(A)` is infinite.
