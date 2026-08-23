---
rg: 2
id: restriction-ring-fiber-metric-proof
kind: route
title: Classify aligned extensions by multiplicity and compare them using the Selberg intertwiner gap
target: congruence-endpoint-orbits-are-restriction-ring-fibers
requires:
  - regular-congruence-endpoint-orbit-has-uniform-selberg-retraction
---

An exact endpoint over `beta` is an exact representation `pi` of `Q`
together with a unitary identification `pi|K=beta`.  Its unitary equivalence
class is the multiplicity vector

```text
m_pi in N[Irr(Q)].                                        (RFM1)
```

The existence of the core identification is exactly
`res(m_pi)=[beta]`, proving that `(RFM1)` lands in `(ERF2)` and that every
point of `(ERF2)` occurs.

Suppose two aligned endpoints `pi,eta` have the same multiplicity vector.
Choose a global unitary intertwiner `V`.  Since both restrictions equal
`beta`, `V` commutes with `beta(K)`, and conjugation by `V` carries one
extending involution to the other.  Conversely, a core-commutant conjugacy
between the extending involutions intertwines the core generators and the
extra generator, hence the whole quotient representation.  Its multiplicity
vectors agree.  This proves the orbit bijection.

For the metric statement, let `m,n` be the two multiplicity vectors.  Their
maximal common `Q`-subrepresentation has dimension

```text
c=sum_alpha dim(alpha) min(m_alpha,n_alpha)=ov(m,n).       (RFM2)
```

Align the two representations identically on this common summand.  After
removing it, the complementary restrictions to `K` are still equivalent,
because both full restrictions equal `beta`.  Use any exact `K`-intertwiner
to identify the complements.  The two endpoint involutions now agree on a
`c`-dimensional reducing subspace and are arbitrary unitaries on its
`d-c` dimensional complement.  Therefore

```text
dist_2(O_m,O_n)<=2 sqrt((d-c)/d)=2 sqrt(mu(m,n)).           (RFM3)
```

For the converse, take any unitary `U` intertwining the two common core
actions and put

```text
gamma(q)Z=eta(q)Zpi(q)^*                                  (RFM4)
```

on normalized Hilbert--Schmidt operators.  The `K`-generator displacements
of `U` vanish, while the displacement under the extending generator `x` is

```text
||gamma(x)U-U||_2=||eta(x)-U pi(x)U^*||_2.                (RFM5)
```

The uniform congruence gap gives

```text
||gamma(x)U-U||_2
 >=kappa dist_2(U,Hom_Q(H_pi,H_eta)).                      (RFM6)
```

The orthogonal projection of a unitary onto the global intertwiner space
has squared normalized norm at most `c/d`: in each irreducible isotypic
pair, its diagonal block has Frobenius square at most the smaller carrier
dimension, and all off-isotypic blocks are orthogonal to the intertwiner
space.  Hence

```text
dist_2(U,Hom_Q(H_pi,H_eta))>=sqrt(1-c/d).                  (RFM7)
```

Equations `(RFM5)`--`(RFM7)`, followed by the infimum over all core
identifications, prove the lower half of `(ERF4)`.

Finally, since both vectors have total dimension `d`,

```text
sum_alpha dim(alpha)|m_alpha-n_alpha|
=2(d-c),                                                  (RFM8)
```

which gives the second formula for `mu` in `(ERF3)`.

