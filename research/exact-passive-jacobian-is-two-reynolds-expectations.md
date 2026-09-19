---
rg: 2
id: exact-passive-jacobian-is-two-reynolds-expectations
kind: claim
title: The exact passive Jacobian is output-isometric to a constrained pair of order-three Reynolds expectations
distinct_from:
  iwahori-uniform-infinitesimal-rigidity: that proves a uniform Hilbert-space quotient gap after assembling the two modular vertices; this identifies the concrete operator-space map whose cb inverse is still required.
  full-core-central-relative-tangent-is-zero-near-first-cubic: that eliminates the overcentralized tangent sector; this computes the Jacobian on the genuine fixed-R tangent space.
  right-displacement-reynolds-scalar-cb-complete: that decomposes this exact Jacobian over all right-displacement matrix diagonals and proves its full cb inverse norm equals the scalar diagonal norm.
  passive-iwahori-off-zero-cb-normal-splitting: that asks for a uniform splitting throughout an operator-small neighborhood; this is the exact-zero finite-dimensional reduction only.
---

**ESTABLISHED.**  In the half-parabolic coordinates, fix an exact
`BS(1,4)` core `(R,S)` and an exact extending involution `X`.  Put

```text
A=XS^2,                    B=XRS,
A^3=B^3=I.                                              (EPJ1)
```

The genuine relative tangent space is

```text
E_(R,X)={h:h^*=-h, [h,R]=0, XhX=-h}.                   (EPJ2)
```

For completely bounded norms, use the complexified tangent

```text
E_(R,X)^C={h:[h,R]=0, XhX=-h};                         (EPJ2C)
```

the space in `(EPJ2)` is its skew-adjoint real part, and the derivative
below extends complex-linearly to `(EPJ2C)`.

For the chart `X_h(t)=X exp(th)`, define

```text
k_1=Ad_(S^(-2))(h),             k_2=Ad_(S^(-1))(h).
```

Then

```text
X_h(t)S^2=A exp(tk_1),
X_h(t)RS =B exp(tk_2),                                  (EPJ3)
```

where the second identity uses `[h,R]=0`.  Right-trivializing the two
cubic residuals at `(EPJ1)` gives

```text
DF_X(h)=
 (
   (I+Ad_A+Ad_A^2) k_1,
   (I+Ad_B+Ad_B^2) k_2
 ).                                                     (EPJ4)
```

Since `A` and `B` have order three,

```text
E_A=(I+Ad_A+Ad_A^2)/3,
E_B=(I+Ad_B+Ad_B^2)/3                                  (EPJ5)
```

are trace-preserving conditional expectations onto `{A}'` and `{B}'`.
Thus the exact passive Jacobian is literally the shifted column

```text
h |-> 3(E_A Ad_(S^(-2))h,E_B Ad_(S^(-1))h).            (EPJ6)
```

The two shifts cannot be discarded as separate changes of the one common
domain variable.  There is instead a common-domain normal form.  Applying
the codomain map `Ad_(S^2) direct_sum Ad_S` gives

```text
h |-> 3(E_(S^2 X)h,E_(S X R)h).                        (EPJ6A)
```

Indeed `S^2AS^(-2)=S^2X` and `SBS^(-1)=SXR`; both are
order-three conjugates of `A` and `B`.  On the two-row maximum
operator-space norm the codomain map is a complete isometry, and on the
Hilbert direct sum it is unitary.  Hence `(EPJ6)` and `(EPJ6A)` have the
same kernel and the same normal-inverse norms without moving the constrained
tangent domain.  The cb norm is universally bounded.  The open
operator-space content is exactly whether its gauge-normal inverse on its
range has cb norm bounded uniformly over finite congruence endpoints and
all multiplicity amplifications.

`two-reynolds-l2-gap-does-not-bound-the-cb-normal-inverse` makes the generic
expander obstruction rigorous: even two order-three conditional
expectations can have a uniform `L2` gap and logarithmically divergent cb
normal inverse.  But that theorem alone is not a counterexample here.  The
domain `(EPJ2)` is the fixed-`R`, `X`-odd operator space, not the full scalar
edge-function space, and
`full-core-central-relative-tangent-is-zero-near-first-cubic` shows that
the obvious full-core-central scalar sector is zero.

There is nevertheless an exact commutative test inside the arithmetic
problem.  `constrained-reynolds-column-has-a-diagonal-scalar-shadow`
restricts the left-regular congruence endpoint to its diagonal masa and
obtains an explicit signed-incidence matrix `C_Q` on `Q/<R>`.  Uniform cb
complementability in `(EPJ7)` implies a uniform cb Moore--Penrose inverse
for every `C_Q`.  This is a necessary scalar arithmetic Green estimate,
not a consequence of the Hilbert angle.  Its prime-field domain is the
sign-induced module from `<h(2),w>`.  Because one scalar coordinate is
repeated over the whole growing torus orbit, it is not the bounded-degree
graph in the generic expander counterexample; the surviving scalar issue is
uniformity in the split-torus index and in deeper congruence rings.

At a left-regular endpoint, the apparent remaining matrix-coefficient issue
also collapses.  By
`right-displacement-reynolds-scalar-cb-complete`,
`B(l2(Q))` is the orthogonal sum of right-displacement fibers
`M_f rho(z)`, the original-coordinate column `(EPJ6)` is the identical
scalar column on every fiber, and
its Moore--Penrose inverse is a row of left convolutions.  The full cb norm
of that row equals its ordinary infinity norm on the diagonal fiber.
Accordingly the exact cb question is the scalar arithmetic inequality:

```text
sup_(q,rho)
 || ( C_(q,rho) |_(ker C_(q,rho))^perp )^dagger
       ||_(linfinity^2 -> linfinity)
 < infinity,                                             (EPJ7)
```

where `q` ranges over congruence quotients and `rho` over their left-regular
endpoint packets.  External amplifications cost nothing beyond the same
scalar norm, and arbitrary quotient representations are reducing corners
of an amplified regular representation, so they inherit the same bound.
A no-go must therefore produce a divergent mode in these
specific arithmetic scalar columns; the finite Hecke `L2` angle by itself
neither proves nor refutes `(EPJ7)`.  This exact-zero reduction does not
supply the off-zero continuation required for Newton iteration.
