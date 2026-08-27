---
rg: 2
id: parahoric-covariant-congruence-packets-pay-one-over-eighty-four
kind: claim
title: D-covariant congruence packets are central or pay one over eighty-four A2 leakage
distinct_from:
  no-finite-arithmetic-hecke-corner-can-have-shell-atom-trace: That rules out projections inside a fixed finite arithmetic subgroup; this permits moving finite congruence quotients with ranks tending to one over forty-two and proves their covariance-versus-interference obstruction.
  single-denominator-borel-cuts-have-a-rohlin-escape: That builds diffuse one-shift cuts with vanishing covariance; this treats finite Borel/unipotent character packets under the full parahoric section group and computes their A2 Julia leakage.
  native-a2-two-path-average-is-not-an-ordinary-word-compression: That gives a group-basis wordization fence in the infinite arithmetic-lamp group; this proves a centrality and exact rank-leakage dichotomy in every moving congruence quotient.
---

Let `F_n` be the image of

```text
D=SL_3(Z) cap hSL_3(Z)h^(-1)                           (DCQ1)
```

in a finite level-`2^n` congruence quotient.  Let `q_n` be a projection in
the left group algebra `C[F_n]`, obtained from any finite Borel, unipotent,
or character packet and then required to retain all `D`-section covariance:

```text
[q_n,lambda_n(s)]=0                 (s in F_n).         (DCQ2)
```

Then

```text
q_n in Z(C[F_n]).                                      (DCQ3)
```

Indeed `(DCQ2)` says exactly that `q_n` is fixed by conjugation by every
group basis element.  Thus an exact `D`-covariant packet in the finite
Borel/unipotent quotient is central; it cannot simultaneously be the
noncentral Hecke control needed to make two paths interfere.

The same conclusion is robust uniformly in `n`.  The finite-index group
`D<SL_3(Z)` has property `(T)`.  For one fixed Kazhdan pair `(S,kappa)`, the
conjugation representation on `L^2(C[F_n])` gives

```text
dist_2(q_n,Z(C[F_n]))
 <=kappa^(-1) max_(s in S)||[q_n,lambda_n(s)]||_2.      (DCQ4)
```

Thus asymptotically `D`-covariant moving packets are asymptotically central,
independently of their level, dimension, or Borel orbit size.  Spectral
rounding of the central conditional expectation replaces them by central
projections with vanishing additional `L^2` cost.

# Exact two-path leakage scaling

Let

```text
d_n=lambda_n(x_23(2)),                                 (DCQ5)
```

and suppose, even granting the unresolved rank selection, that

```text
tau(q_n)->1/42.                                        (DCQ6)
```

Centrality makes `d_nq_n` a unitary in the `q_n` corner.  After removing one
of the two common A2 path transports, their desired average is

```text
K_n=q_n(1+d_n)/2.                                      (DCQ7)
```

With the normalized corner trace `tau_(q_n)`, direct expansion gives

```text
tau_(q_n)(q_n-K_n^*K_n)
 =(1-Re tau_(q_n)(d_n))/2,                             (DCQ8)
```

and hence the global missing-source/range mass is

```text
tau(q_n-K_n^*K_n)
 =tau(q_n)(1-Re tau_(q_n)(d_n))/2.                     (DCQ9)
```

There are only two asymptotic regimes.

1. If the selected packet retains the canonical trace-zero A2 holonomy,

   ```text
   tau_(q_n)(d_n)->0,
   ```

   then `(DCQ6)--(DCQ9)` give the exact limit

   ```text
   tau(q_n-K_n^*K_n)->1/84.                            (DCQ10)
   ```

   Any unitary dilation or native compression realizing the average must
   route this positive mass into the established first-exit ledger.
2. If the Julia/first-exit mass in `(DCQ9)` tends to zero, then

   ```text
   ||(d_n-1)q_n||_2^2
    =2 tau(q_n)(1-Re tau_(q_n)(d_n))->0,               (DCQ11)
   ```

   so the supposedly trace-separated holonomy is erased on the packet.

Therefore the explicit moving finite Borel/unipotent quotient does not
produce the desired source.  Full `D` covariance centralizes it; retaining
the A2 signal costs asymptotic first-exit mass `1/84`, while suppressing that
mass kills the signal.  A surviving unbounded source must live outside the
left congruence group algebra--for example in a genuinely relative
commutant/matrix-coordinate algebra--and must still couple noncentrally to a
second chart.
