---
rg: 2
id: mf-fd-visible-elements-have-global-trace-gaps-proof
kind: route
title: Adjoin a balanced exact separator to a faithful MF realization
target: mf-fd-visible-elements-have-global-trace-gaps
requires: []
artifacts:
  - notes/mf-invariant-corner-visibility-audit-2026-08-30.md
---

Choose a faithful MF realization represented on exhausting windows by
unitary tables

```text
phi_n : G -> U(d_n).
```

Thus their operator-norm multiplication defects tend to zero, and for each
`a != 1` the induced corona class of `phi_n(a)` stays a positive operator
distance from the identity.  Let `rho : G -> U(m)` be an exact
finite-dimensional representation with `rho(g) != I_m`, and put

```text
gamma = 1-Re tr_m(rho(g)).                                (1)
```

Every eigenvalue of `rho(g)` lies on the unit circle.  Hence its real part
is at most one, with equality only at the eigenvalue one.  Therefore the
average in `(1)` equals zero only if every eigenvalue is one.  The hypothesis
gives

```text
gamma > 0.                                                (2)
```

At coordinate `n`, balance the two summands exactly by defining

```text
v_n(a)=phi_n(a)^(direct sum m) direct sum
       rho(a)^(direct sum d_n) in U(2 m d_n).             (3)
```

The second block is an exact representation, while direct sums take the
maximum of block operator norms.  Consequently the multiplication defect of
`v_n` is precisely at most that of `phi_n` on every tested product and tends
to zero on exhausting windows.  The first block also gives, for every
`a != 1`,

```text
||v_n(a)-I||_op >= ||phi_n(a)-I||_op,                     (4)
```

so the induced homomorphism into the new matrix corona is faithful.

The two blocks in `(3)` have the same dimension `m d_n`.  Normalized trace
therefore gives

```text
Re tr(v_n(g))
 = (Re tr(phi_n(g))+Re tr(rho(g)))/2
 <= (1+(1-gamma))/2
 = 1-gamma/2.                                             (5)
```

This proves `(FDV1)` with the global projection `P=1`.

Finally, failure of the conclusion forces `rho(g)=I` for every
finite-dimensional unitary representation, hence `g in Rad_fd(G)`.  Since
`g !=1` in an MF group and the faithful MF realization itself separates
`g`, one has `g notin Rad_MF(G)`.  This proves `(FDV2)` and the theorem.
