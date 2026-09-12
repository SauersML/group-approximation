---
rg: 2
id: sl2-half-explicit-strict-flexible-proof
kind: route
title: Delete the even Weil fixed line and use the TFD intertwiner gap
target: sl2-half-explicit-strict-flexible-separation
requires:
  - even-weil-fixed-line-compression
---

`even-weil-fixed-line-compression` gives `(SFS1)` and the one-dimensional
completion `(SFS3)`.  For `(SFS2)`, suppose exact same-dimensional
representations `sigma_p` approach `phi_p`.  Then `sigma_p (+) 1` approaches
the irreducible exact even Weil representation `pi_p` in the common
dimension `(p+1)/2`.

Property `(T;FD)` of `PSL_2(Z[1/2])` supplies a uniform Kazhdan constant for
finite-dimensional representations.  Applied to

```text
pi_p tensor conjugate(sigma_p (+) 1),
```

the identity matrix is almost invariant, so a nonzero invariant vector
exists.  Equivalently `pi_p` and `sigma_p (+) 1` share an irreducible
constituent.  Since `pi_p` is irreducible and both total dimensions equal
`(p+1)/2`, they must be isomorphic.  This is impossible because
`sigma_p (+) 1` has a trivial invariant line.  Subtracting the
`O(p^(-1/2))` compression error from the fixed `(T;FD)` constant gives the
uniform `c` in `(SFS2)`.
