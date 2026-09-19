---
rg: 2
id: cyclic-phase-pauli-shears-have-unbounded-clock-order-proof
kind: route
title: Lift the cyclic Frobenius shears and follow the unique leading monomial
target: cyclic-phase-pauli-shears-have-unbounded-clock-order
requires:
  - phase-inverting-fourth-root-lifts-opposite-pauli-shears
---

The monomial bases `1,x,...,x^(m-1)` and
`1,x^(-1),...,x^(-(m-1))` are dual for `(CPC1)`, proving nondegeneracy.  The
cocycle in `(CPC2)` has alternating commutator form `B`, so the standard
finite-Heisenberg argument gives the asserted spin dimension.

Both maps in `(CPC3)` preserve `(CPC1)` because the two new cross terms are
equal and cancel in characteristic two.  On a Pauli basis vector `v`, its
Weyl normal form squares to `R^(2q(v))`, where
`q(a,b)=ell_m(ab)`.  Multiplication by `R^q(v)` makes it an involution.
Together with `R|->R^-1`, the generator images preserve all commutators and
square relations.  The induced linear map is invertible, hence the resulting
endomorphism is an automorphism.  Applying it twice on the generators makes
the two phase corrections cancel because of the central inversion, proving
involutivity.

For the order bound, write the upper-left and lower-left entries of `M^n` as
`a_n,c_n`.  From left multiplication by `(CPC4)`,

```text
a_(n+1)=(1+x^2)a_n+x c_n,
c_(n+1)=x a_n+c_n.
```

Starting with `deg(a_1)=2` and `deg(c_1)=1`, induction gives monic
`deg(a_n)=2n` and monic `deg(c_n)=2n-1`; the leading term in each recurrence
is unique.  Therefore `M^n!=I`.  For `m>2n` no term at or below degree `2n`
wraps modulo `x^m-1`, so the cyclic quotient also has `M^n!=I`.  The lifted
automorphism maps onto this quotient, and consequently cannot have order at
most `n`.
