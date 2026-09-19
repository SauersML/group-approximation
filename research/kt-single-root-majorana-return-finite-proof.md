---
rg: 2
id: kt-single-root-majorana-return-finite-proof
kind: route
title: Cliffordize the finite root-stabilizer coset quotient
target: kt-single-root-majorana-return-finite-countermodels
requires:
  - kt-single-root-mixed-return-has-exact-finite-countermodels
---

Use the finite actor quotient from
`kt-single-root-mixed-return-finite-countermodel-proof`.  Thus, after taking
a diagonal product with a quotient separating any prescribed actor window,
there is a finite group `K_N` with elements

```text
R=theta_N(r),                 H=theta_N(h),
H notin <R>.
```

Put `X_N=K_N/<R>`.  Let `A_N` be the finite complex Clifford algebra on
self-adjoint generators `(c_x)_(x in X_N)` with

```text
c_x^2=1,                     c_x c_y=-c_y c_x  (x!=y),
```

equipped with its canonical trace (the coefficient of the identity
Clifford monomial).  The permutation action of `K_N` on `X_N` preserves
these relations and therefore acts by trace-preserving automorphisms of
`A_N`.  Form the finite-dimensional crossed product

```text
M_N=A_N crossed_product K_N.
```

Its canonical group unitaries give an exact representation of the finite
actor image.  Set

```text
c=c_(<R>),                    d=u_H c u_H^*=c_(H<R>).
```

Because `R` fixes `<R>`, `[c,u_R]=0`.  Because `H notin <R>`, the two sites
`<R>` and `H<R>` are distinct, so `cd=-dc`.  Both generators have trace
zero, as does their product.  Hence

```text
||[c,u_H]||_2^2=||c-d||_2^2=2.
```

The diagonal finite quotient used in the prerequisite separates every
chosen nonidentity actor word.  The crossed-product trace is zero on its
nontrivial group unitaries, so the actor moments are canonical on the
prescribed window.  Clifford monomials are likewise orthogonal under the
canonical trace.  All assertions in `(KMC2)` are therefore exact.

Only the cyclic subgroup `<R>` stabilizes the distinguished site in this
construction.  It does not centralize `c` under a generating packet of
`Gamma`; accordingly the model does not address, and cannot refute, an
inequality that uses the full Kazhdan stabilizer table.

