---
rg: 2
id: affine-weyl-apartment-has-independent-lamp-models
kind: claim
title: The complete affine-Weyl apartment has finite canonical models with independent commuting lamp overlap
distinct_from:
  commuting-conjugate-involution-transfer-for-sl3-pair: that is the open transfer statement for the full arithmetic actor; this constructs exact finite countermodels for the maximal apartment-normalizer subpacket and locates the relations a proof must use outside it.
  native-hecke-edge-rank-integrality-is-bounded: that bounds the clique pressure of the Hecke orbital graph; this gives coherent canonical finite models for every depth of one entire affine apartment, including all translation and Weyl loops.
  coset-bernoulli-ce-refutes-relative-commutant-collapse: that is an infinite tracial crossed-product firewall for the full coset action; this is a sequence of literal finite groups and exact matrix representations for the apartment subpacket.
---

Put

```text
A = SL_3(Z[1/2]),             C = SL_3(Z),
h = diag(2,1,1/2).
```

Let `T` be the two-dimensional diagonal `2`-power torus

```text
T = {diag(2^a,2^b,2^(-a-b)) : (a,b) in Z^2},
```

and let `K` be the finite group of determinant-one signed monomial matrices
in `C`.  Then `K` normalizes `T`, `h` belongs to `T`, and

```text
N = <T,K> = T rtimes K
```

is the full integral affine-Weyl normalizer packet needed below.  Its action
on the apartment `T` is affine: `T` acts regularly by translation and `K`
fixes the origin and acts through the finite Weyl group on `T`.

Consider the stronger apartment lamp group

```text
G_ap = (direct_sum_(x in T) C_2) rtimes N,              (AWA1)
```

and write `c_x` for its coordinate involutions.  In particular

```text
c_0^2=1,       [c_0,K]=1,       [c_0,h c_0 h^-1]=1.    (AWA2)
```

The last relation is the native commuting-conjugate relation, while `(AWA1)`
imposes the strictly stronger condition that **all** apartment lamps commute.

## Exact finite canonical models

For every integer `m >= 2`, reduce the translation lattice modulo `m`:

```text
T_m = T/mT,
N_m = T_m rtimes K,
G_m = (direct_sum_(x in T_m) C_2) rtimes N_m.           (AWA3)
```

These are finite groups.  The quotient maps `G_ap -> G_m` separate every
fixed nonidentity element for all sufficiently large `m`: a nonzero
translation survives modulo large `m`, a nontrivial Weyl component already
survives in `K`, and the finitely supported lamp function injects after its
support points remain distinct modulo `m`.  Hence `G_ap` is residually finite.

Let `lambda_m` be the left regular representation of `G_m` and define

```text
P_m = (1-lambda_m(c_0))/2,
Q_m = lambda_m(h) P_m lambda_m(h)^*.
```

Whenever the two coordinates `0` and `h.0` are distinct modulo `m`, the
four elements

```text
1, c_0, c_(h.0), c_0 c_(h.0)
```

are distinct.  The regular character therefore gives

```text
tr(P_m)=tr(Q_m)=1/2,
[P_m,Q_m]=0,
tr(P_m Q_m)=1/4,                                      (AWA4)
```

or equivalently

```text
tr(lambda_m(c_0 h c_0 h^-1))=0.                       (AWA5)
```

Moreover `P_m` commutes exactly with `lambda_m(K)`, and every actor or lamp
word in a prescribed finite subset of `G_ap\{1}` has normalized trace zero
for all sufficiently large `m`.  Thus the regular representations of the
finite groups `(AWA3)` are canonical-trace microstates for the complete
apartment lamp group, with zero relation defect and the maximally interior
overlap `a=1/4`.

## Consequence for the native scalar gate

No estimate excluding interior overlap can be derived from any finite or
infinite collection consisting only of

1. the affine-Weyl translation and Weyl relations inside `N`;
2. centrality of the base lamp under the apartment stabilizer `K`;
3. covariance of all apartment lamp coordinates; and
4. any collection of commutation relations among those coordinates.

Indeed the finite regular models above satisfy all of these relations
exactly and satisfy every fixed canonical trace test eventually, while
`a=1/4` identically.  This includes arbitrary-depth translation cycles and
all finite torus/Weyl closures of a single building apartment; passing to a
larger apartment packet cannot create the desired matrix obstruction.

Consequently a proof of
`commuting-conjugate-involution-transfer-for-sl3-pair` must use relations
which glue **different apartments through nonmonomial root subgroups**.  In
matrix terms it must show that the same four joint atom projections from
`P` and `hPh*` cannot be transported consistently across those root-group
gluings.  The diagonal torus, the Weyl interlock, and apartment Hecke loops
alone admit an exact coherent finite counterarchitecture.
