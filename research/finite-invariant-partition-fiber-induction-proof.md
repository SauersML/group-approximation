---
rg: 2
id: finite-invariant-partition-fiber-induction-proof
kind: route
title: Disintegrate over a finite invariant partition and induce the fiber stabilizer character
target: finite-invariant-partition-only-reduces-irs-to-fiber-irs
requires: []
---

Discard null atoms of `D`.  The action of `Gamma` permutes the remaining
atoms.  Split them into orbits `O_1,...,O_s`, and let `X_j` be the union of
the atoms in `O_j`.  Each `X_j` is invariant, so

```text
phi=sum_j mu(X_j) phi_j,                                (FIP3)
```

where `phi_j` is the fixed-point character of the normalized action on
`X_j`.  Connes-embeddable characters form a convex set.  Therefore some
`phi_j` is non-CE whenever `phi` is non-CE.

Fix such an orbit, write its atoms as

```text
Y_i=r_iY,  1<=i<=m,
```

and put `Delta=Stab_Gamma(Y)`.  Since the atoms are a transitive finite
`Gamma`-set, `m=[Gamma:Delta]` and every atom has normalized measure `1/m`
inside `X_j`.  The restricted action `Delta curvearrowright Y` is pmp for
the normalized measure, and its stabilizer character is `psi` from `(FIP1)`.

The Koopman-orbit representation of `Gamma` on the relation of its action on
`X_j` is the ordinary finite-index induction of the corresponding
representation of `Delta` on the relation of `Delta curvearrowright Y`.
Equivalently, in coset coordinates its matrix is

```text
rho(g)_(k,i)=pi(r_k^(-1) g r_i)
```

when `r_k^(-1) g r_i in Delta`, and zero otherwise.  Taking normalized trace
gives

```text
phi_j(g)
 = (1/m) sum_(i: r_i^(-1) g r_i in Delta)
       psi(r_i^(-1) g r_i).                            (FIP4)
```

Thus `phi_j` is the normalized induced character `Ind_Delta^Gamma(psi)`.
If the GNS algebra `N_psi` were CE, the induced representation would lie in
`M_m(N_psi)`, and its generated von Neumann algebra would be a tracial
subalgebra of that CE algebra.  Hence `phi_j` would be CE, a contradiction.
So `psi` is non-CE.

If `(FIP2)` holds, the GNS representation of `psi` is the left regular
representation of `Delta/K`.  Therefore `L(Delta/K)` is non-CE and
`Delta/K` is non-hyperlinear.

For the final ZPC assertion, decompose a perfect ZPC-IRS strategy into
ergodic components.  The game loss and every forbidden ZPC cylinder have
nonnegative integrands and total integral zero, so they vanish on almost
every component.  Every such component still has game value one.  Since the
fixed game has quantum value below one, its value-one IRS character cannot
be CE.  Choosing one component gives the stated ergodic witness.
