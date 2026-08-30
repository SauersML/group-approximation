---
rg: 2
id: central-regular-edge-constituents-are-fell-pure
kind: claim
title: Central-regular Iwahori mass purifies into Fell-regular edge irreducibles
artifacts:
  - notes/TRUE_IWAHORI_CENTRAL_REGULAR_OUTLIER_LOCALIZATION.md
distinct_from:
  edge-pair-mixed-gap-collapse: that still has to exclude a sparse full-rank almost-intertwiner between two high-dimensional edge irreducibles; this proves that the two irreducibles may individually be assumed to converge to the regular character.
  mixed-intertwiner-energy-transport-localization: that localizes overlap mass onto low-mixed-energy block pairs for arbitrary exact representations; this purifies the individual characters and dimensions of the block types on the central-regular face.
  modular-vertex-extension-does-not-force-congruence: that constructs high-dimensional noncongruence edge types; Fell-regular constituent concentration does not turn those types into congruence representations.
---

Let `H` be a countable group and let `tau` be an extreme point of its compact
trace space `Tr(H)`.  Suppose finite-dimensional unitary representations
`rho_n:H->U(d_n)` have normalized characters converging pointwise to `tau`.
Write

```text
rho_n = directSum_j m_(n,j) pi_(n,j),
chi_(n,j)(h)=tr(pi_(n,j)(h))/dim(pi_(n,j)),
mu_n=sum_j (m_(n,j)dim(pi_(n,j))/d_n) delta_(chi_(n,j)).   (CRP1)
```

Then the constituent measures converge weakly to the point mass at `tau`:

```text
mu_n -> delta_tau.                                        (CRP2)
```

Equivalently, for every pointwise neighborhood `U` of `tau`, the total
physical dimension carried by irreducible constituents whose normalized
characters lie outside `U` is `o(d_n)`.  If the GNS representation of `tau`
is infinite-dimensional, then for every fixed `D` the total dimension
carried by constituents of dimension at most `D` is also `o(d_n)`.

Apply this in one matched central-sign sector of the Iwahori problem.  The
established outlier setup, specifically `(ICO6)` in the cited artifact,
says that **each** of the two exact edge restrictions has normalized
character tending pointwise to the same central-regular trace, not merely
that their mixed character is regular.

The required central twist exists concretely.  The modular abelianization is

```text
SL_2(Z)^ab ~= C_12,
```

and `z=-I` maps to its unique element of order two.  Hence there is a
one-dimensional modular character `kappa` with `kappa(z)=-1`; restrict it to
`B`.  Twist by the trivial character in the positive sector and by `kappa`
in the negative sector.  In either case `z` then acts trivially, while
off-center character limits remain zero because twisting only multiplies
them by scalars of modulus one.  The edge representations descend to

```text
B/<z> ~= Z*C_2.                                          (CRP3)
```

This quotient is ICC, so its regular trace has factorial GNS representation
and is extreme.  If the two exact edge restrictions in a central-regular
Iwahori sequence are decomposed into isotypic projections
`(P_(n,i))` and `(Q_(n,j))`, there are pointwise neighborhoods `W_n` shrinking
to the regular trace and numbers `D_n->infinity` such that

```text
sum_(i: chi_(n,i) notin W_n or dim(theta_(n,i))<=D_n) tr(P_(n,i)) ->0,
sum_(j: psi_(n,j) notin W_n or dim(eta_(n,j))<=D_n)   tr(Q_(n,j)) ->0.   (CRP4)
```

For every comparison unitary `V_n`, the overlap plan

```text
m_(n,i,j)=||P_(n,i) V_n Q_(n,j)||_2^2                  (CRP5)
```

has these two trace lists as its marginals.  Therefore the total overlap
mass involving a bad row or bad column in `(CRP4)` is `o(1)`.  Intersecting
with the low-mixed-energy mass from
`mixed-intertwiner-energy-transport-localization` shows that all but `o(1)`
of the surviving low-energy transport lies on edge-irreducible pairs with

```text
dim(theta_n),dim(eta_n)->infinity,
chi_(theta_n)->delta_e,       chi_(eta_n)->delta_e     (CRP6)
```

pointwise after the central twist.

This does not close the outlier.  A one-dimensional low-energy line in
`Hom(eta_n,theta_n)` has normalized operator-space weight tending to zero
and is invisible to `(CRP6)`; its vector may nevertheless be represented by
a full-rank near-unitary matrix.  The remaining gate is thus specifically a
full-rank mixed-gap collapse between two individually Fell-regular,
opposite-extendible edge irreducibles, not cancellation among nonregular
constituent characters.  Any theorem extracting one physical pair from the
surviving transport therefore only has to treat sequences satisfying
`(CRP6)`; that extraction itself is not asserted here.
