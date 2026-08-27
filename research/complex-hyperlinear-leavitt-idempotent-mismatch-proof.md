---
rg: 2
id: complex-hyperlinear-leavitt-idempotent-mismatch-proof
kind: route
title: Expand the order-three corner over characteristic zero and compare it with its mod-two reduction
target: complex-hyperlinear-leavitt-idempotent-mismatch
requires:
  - leavitt-corner-idempotent-unital-surjection
  - leavitt-matrix-amplification-in-unit-group-algebra
---

Write `u=u_g`.  Since `g^3=1`, `u^3=1` in every group algebra.  Over the
complex numbers,

```text
(u+u^2)^2 = u^2+2u^3+u^4
            = u^2+2+u,
```

which proves `(CHL1)`.  A unital map into a complex tracial algebra sends the
right side to `2I`, whose normalized Hilbert--Schmidt norm is exactly `2`.

The approximate statement needs no stability theorem.  For unitaries `U_n`
with `||U_n^3-I||_2 -> 0`, put `A_n=U_n+U_n^2`.  Direct expansion gives

```text
A_n^2-A_n = 2U_n^3 + (U_n^4-U_n).
```

Now `||U_n^4-U_n||_2=||U_n(U_n^3-I)||_2 -> 0` and
`||2U_n^3-2I||_2 -> 0`; hence

```text
||A_n^2-A_n||_2 -> ||2I||_2=2.
```

Over `F_2` the middle coefficient vanishes, so the same expansion instead
gives `e_2^2=e_2`; this is exactly the scalar step used by
`leavitt-corner-idempotent-unital-surjection`.  There cannot be a unital ring
map from `F_2[G]` to any nonzero complex algebra, since it would send
`0=1+1` to `2I != 0`.  Thus the characteristic-two evaluation cannot be
composed with a complex hyperlinear representation in either direction.

Finally, functional calculus for the order-three unit gives

```text
q=(1+u+u^2)/3,        p=1-q=(2-u-u^2)/3.
```

These are the trivial and nontrivial `C_3` spectral projections.  For the
regular group trace, `tau(u)=tau(u^2)=0`, so `tau(q)=1/3` and `tau(p)=2/3`.
This is an ordinary finite-dimensional character decomposition, not the
idempotent `e_2`: replacing `e_2` by `p` discards both the mod-two evaluation
`e_2 |-> 1_R` and the corner surjection onto `R`.  Hence it supplies no
partial isometries satisfying the binary Leavitt relations.

For completeness, self-similarity does not restore the lost addition.  The
subgroup calculation in
`leavitt-matrix-amplification-in-unit-group-algebra` gives commuting copies

```text
delta(G) x H <= G,                 H=GL_2(F_2)=S_3.
```

Let `r` be any spectral projection in `C^*(H)` and let a finite tracial model
carry the regular trace on this direct product.  Then `r` commutes with every
`u_(delta(h))`, and, for `h != 1`,

```text
tau(r u_(delta(h)))=0.
```

Indeed, expand `r` in the finite group basis: no product of the nonidentity
`delta(h)` with an element of `H` is the identity.  After normalization by
`tau(r)`, the compressed `delta(G)` trace is again the regular character.
Thus prefix self-similarity creates ordinary trace-scaled copies of the same
group representation, exactly as finite factors permit; it does not identify
a projection with two orthogonal copies of itself.  The missing datum is
coefficient addition, not another multiplicative relation.
