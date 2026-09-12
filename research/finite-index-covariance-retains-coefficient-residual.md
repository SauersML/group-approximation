---
rg: 2
id: finite-index-covariance-retains-coefficient-residual
kind: claim
title: Finite-index covariance retains a fixed bounded-type coefficient residual on high irreducible orbits
distinct_from:
  high-type-irreducibles-retain-finite-packet-mass: that extracts high irreducible packet-bearing representations of the old group; this induces each one across every finite-index overgroup and proves that the actual residual Z(1-a) stays uniformly positive on the identity-coset block.
  finite-normalizer-covariance-density-no-go: that uses regular representations of finite semidirect quotients to dilute old commutant density; this uses a single finite orbit of high irreducibles, has no regular multiplicity, and directly tests the bounded-type coefficient residual.
  regular-trace-forbids-universal-bounded-type-placement: that uses the infinite regular representation to rule out a universal algebraic placement identity; this gives exact finite-dimensional zero-relator-defect countermodels for every finite-index attachment.
---

**ESTABLISHED FINITE-INDEX COEFFICIENT FENCE.**  Let `Lambda` be an
infinite residually finite property-`(T)` group, let `B<Lambda` be finite,
and let

```text
0!=z=z*=z^2 in C[B],             q=tau_B(z)>0.          (FIC1)
```

Assume that `Lambda` has finite quotients of unbounded order which are
injective on `B`.  Fix `K`, let

```text
p=p_<=K in C*_max(Lambda)                               (FIC2)
```

be the central projection selecting the irreducible `Lambda`-types of
dimension at most `K`, and choose `a in C[Lambda]` with

```text
||a-p||_max<=epsilon<1.                                 (FIC3)
```

Let `Lambda<G` have finite index `m`, with no normality assumption.  Then
`G` has exact finite-dimensional representations `rho_j` such that

```text
tr(rho_j(z))>=q/(2m),
||rho_j(z)(1-rho_j(a))||_2
    >=(1-epsilon)sqrt(q/(2m)).                          (FIC4)
```

If `Lambda` is normal in `G`, these representations additionally satisfy
`rho_j(p)=0`.

In particular every defining relator of any finite presentation of `G` has
zero normalized-Hilbert--Schmidt defect in `rho_j`, while the residual in
`(FIC4)` has a fixed positive floor.  Therefore no estimate of the form

```text
||Z(1-a)||_2 <= C sqrt(group-relator energy)            (FIC5)
```

can compile the bounded-type coefficient separator inside any finite-index
ordinary-group attachment.  In particular this includes every crossed
product by a finite automorphism group, every covariance table whose
implementers generate a finite-index overgroup of `Lambda`, and, after
passing to its finite central extension, the corresponding finite-order
projective covariance tables.

## Proof

By `high-type-irreducibles-retain-finite-packet-mass`, there are irreducible
representations

```text
pi_j:Lambda->U(d_j),       d_j->infinity,
tr_(d_j)(pi_j(z))>=q/2.                                 (FIC6)
```

For `d_j>K`, induce `pi_j` to `G`:

```text
rho_j=Ind_Lambda^G(pi_j),       dim(rho_j)=m d_j.        (FIC7)
```

Use the standard induced-representation model on `m` coset fibers and let
`H_j` be the identity-coset fiber.  It is reducing for `rho_j(Lambda)`, and
the restriction there is `pi_j`.  Consequently

```text
rho_j(z)|_(H_j)=pi_j(z),
rho_j(a)|_(H_j)=pi_j(a).                                (FIC8)
```

Since `z` is a projection, `rho_j(z)` is a projection and its trace on the
orthogonal complement of `H_j` is nonnegative.  The identity fiber
contributes at least `q/2`, so normalization by all `m` fibers gives

```text
q_j:=tr_(m d_j)(rho_j(z))>=q/(2m).                      (FIC9)
```

On `H_j`, the high irreducible `pi_j` kills `p`, so `(FIC3)` implies

```text
||pi_j(a)||_op<=epsilon.                                (FIC10)
```

The normalized Hilbert--Schmidt norm on the whole induced space dominates
`1/sqrt(m)` times its norm on `H_j`.  Using `(FIC8)--(FIC10)` therefore gives

```text
||rho_j(z)(1-rho_j(a))||_2
 >=m^(-1/2)||pi_j(z)(1-pi_j(a))||_2
 >=m^(-1/2)(1-epsilon)||pi_j(z)||_2
 >=(1-epsilon)sqrt(q/(2m)).                             (FIC11)
```

This proves `(FIC4)`.  The representations `rho_j` are exact
representations of `G`, so all ordinary group-word relators have zero
defect, proving the fence `(FIC5)`.

If `Lambda` is normal, then the whole restriction `rho_j|_Lambda` is a
direct sum of the `m` conjugates of `pi_j`.  All are irreducible of dimension
`d_j>K`, so every summand kills `p` and `rho_j(p)=0`, proving the optional
normal-case strengthening.

The exact regular marked completion is untouched: because `Lambda` and
`B` embed in `G`, the left regular representation of `G` is exact and the
canonical trace of `z` is still `q`.  Thus finite-index covariance cannot
trade away regular consistency in order to avoid the induced
finite-dimensional countermodels.

## Consequence for the remaining cell

The coefficient residual `Z(1-a)` can only be paid by a group-word-energy
cell which escapes this induction theorem.  It must use at least one of:

1. a genuinely infinite-index attachment;
2. a payload-conditional relation which is vacuous in the exact regular
   marked completion but excludes all induced high-type orbits only in
   finite matrices.

Finite covariance, its finite projective variants, and every other
finite-index attachment are therefore closed branches, not the missing
matrix-only coefficient cell.

DERIVATION
finite-index-induction-coefficient-residual-proof
