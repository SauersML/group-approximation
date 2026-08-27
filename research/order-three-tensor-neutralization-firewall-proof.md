---
rg: 2
id: order-three-tensor-neutralization-firewall-proof
kind: route
title: Telescope the third tensor power, exhibit the Weyl multiplier, and perturb determinant phase at vanishing HS cost
target: order-three-tensor-neutralization-loses-projective-root
requires: []
---

For normalized Hilbert--Schmidt norm and unitary matrices,

```text
||A_1 tensor A_2 tensor A_3-B_1 tensor B_2 tensor B_3||_2
 <=sum_i ||A_i-B_i||_2.                               (OTNP1)
```

Apply this with all `A_i=U_gU_h` and all
`B_i=alpha(g,h)U_(gh)`.  Since `alpha(g,h)^3=1`, `(OTNP1)` gives `(OTN2)`.

For the exact example, on the standard basis of `C^3` take

```text
X e_j=e_(j+1),        Z e_j=omega^j e_j.
```

Then `ZX=omega XZ`, so direct multiplication proves `(OTN4)`.  Its
commutator bicharacter sends `((0,1),(1,0))` to `omega`, whereas every
coboundary on the abelian group `C_3 x C_3` has trivial commutator
bicharacter.  Thus the multiplier is nontrivial.  Tensoring `(OTN4)` three
times kills the scalar exactly, proving that the third tensor power is an
ordinary representation while retaining no test for triviality of the
original Schur class.

Ordinary HS stability quantifies over the ambient unitary group
`U(d^3)` and has no conclusion constraining its correction to the proper
nonlinear set `(OTN3)`.  Therefore applying it to `(OTN2)` stops before a
projective tensor root; adding such a conclusion is a new stability
hypothesis.  The adjoint statement is the corresponding inner-locus fact in
`sl3-regular-projective-correction-is-inner-adjoint-stability`.

Finally, determinants of an exact projective multiplication law give
`alpha(g,h)^d` as a coboundary, hence only `d[alpha]=0`.  Formula `(OTN5)` is
immediate and shows that determinant phase has no dimension-free normalized-
HS modulus.  These calculations prove every assertion in the target claim.
