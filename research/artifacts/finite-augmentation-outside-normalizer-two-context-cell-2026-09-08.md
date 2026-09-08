# An exact two-context cell outside the augmentation normalizer

2026-09-08. Finite-support sums of compressed group elements can
transport projections through elements which do not normalize the
finite subgroup defining the corner. This artifact constructs one
such cell, with two noncommuting context partitions and one shared
proper projection. It also characterizes the single literal partial
transports used to build it.

The displayed supports leave every finite subgroup. The joint
algebra of this particular two-context cell is nevertheless
`M_2(C) direct-sum C`. Moreover, finite-window models of its
wreath-product host exclude any completed `B_loop` diagram there.
These limits are part of the result.

## 1. Which literal compressions are partial isometries?

Let `K<=G` be finite of order `k>=2`, and put

```text
e_K=(1/k) sum_(h in K) h,
q=1-e_K.
```

For `g in G`, write

```text
L=g K g^(-1),
e_L=g e_K g^(-1),
r=1-e_L,
w=q g q.
```

In the reduced group C-star algebra,

```text
w w^*=q r q.
```

For any two projections `q,r`, the compression `qrq` is a
projection exactly when `q,r` commute. Indeed,

```text
q r q-(q r q)^2=q r(1-q)r q.
```

If the right side vanishes, positivity gives `(1-q)rq=0`.
Taking adjoints then gives `rq=qrq=qr`. The converse is
immediate. Consequently

```text
w is a partial isometry
 iff [e_K,e_L]=0
 iff KL=LK.                                         (1)
```

For the last equivalence, every element of `KL` has exactly
`|K intersect L|` decompositions as a product from `K x L`.
Thus `e_K e_L` has strictly positive constant coefficients
on `KL`, while `e_L e_K` has the same constant coefficients
on `LK`. Equality is exactly equality of these two finite
sets. The equality also says that `M=KL` is a finite subgroup,
and then `e_K e_L=e_M`.

Suppose (1) holds and write `h=|K intersect L|`. The range
projection and its canonical trace are

```text
w w^*=1-e_K-e_L+e_M,
tau(w w^*)=1-2/k+h/k^2.                              (2)
```

The initial projection has the same trace. The lost trace from
the original corner is exactly

```text
tau(q-w w^*)=(k-h)/k^2.                              (3)
```

If `g` does not normalize `K`, then `h<=k/2`, and (3) is
at least `1/(2k)`. Relative to `tau(q)=1-1/k`, the lost
fraction is at least `1/(2(k-1))`. A full corner unitary
therefore occurs only when `L=K`, in which case `g`
normalizes `K` and `qgq=qg` is unitary.

These statements allow proper transports outside the normalizer;
they do not assert that a single such transport fills the corner.

## 2. An explicit nonnormal corner in a wreath product

Take `A=A_4` and choose a double transposition `J in A`.
Let

```text
G=(direct_sum_(i in Z) A_i) semidirect <t>,
t A_i t^(-1)=A_(i+1).
```

This is a countable explicit restricted wreath product. The
copies of `A` at different sites commute, and each embeds.
Write `J_i=t^i J_0 t^(-i)` and

```text
q_i=(1-J_i)/2,
K=<J_0>,
q=q_0=1-e_K.
```

The subgroup `K` is not normal: the shift sends it to the
distinct subgroup `<J_1>`. The full local corner
`q C[A_0] q` is `M_2(C)`, as in the explicit noncentral
Frobenius packet. The calculations below need only the commuting
involutions `J_i` and the shift.

Define

```text
f=q_-1 q_0 (1-q_1),
r=t f t^(-1)=q_0 q_1 (1-q_2),
v=t f,
S=q-f-r.                                            (4)
```

All `q_i` commute. The factor `(1-q_1)` in `f` and the
factor `q_1` in `r` give `fr=0`. Both lie below `q`, so
`S` is a projection. The element `v` satisfies

```text
v^*v=f,
vv^*=r,
v=r v f,
v^2=0,
qv=v=vq.                                            (5)
```

Thus it is a partial isometry in the specified full augmentation
corner. It is a cutdown of the proper literal transport `qtq`:
its initial support is further restricted to make the initial
and final projections orthogonal.

## 3. A complete algebraic transport and two matching contexts

Put

```text
P_+=(f+r+v+v^*)/2,
P_-=(f+r-v-v^*)/2.                                  (6)
```

Equations (5) give `(v+v^*)^2=f+r`, so the following are
exact PVMs in `q Q[G] q`:

```text
Context 1:   (S,f,r),
Context 2:   (S,P_+,P_-).                            (7)
```

They have the same unit `q` and the same first atom `S`.
The corresponding shared Boolean observable is `q-2S` in
both contexts. The other atoms in the two contexts need not
commute, and here they explicitly do not:

```text
[f,P_+]=(v^*-v)/2,
||[f,P_+]||=1/2.                                    (8)
```

The norm identity follows from
`(v^*-v)^*(v^*-v)=f+r!=0`.

There is also a single finite-support unitary transporting the
whole first context to the second:

```text
R=S+(f+r+v-v^*)/sqrt(2).                             (9)
```

Writing `a=f+r` and `x=v-v^*`, equations (5) say
`x^*=-x`, `x^2=-a`, `ax=xa=x`, and `Sx=Sa=0`.
Therefore

```text
R^*R=RR^*=S+a=q,
R S R^*=S,
R f R^*=P_+,
R r R^*=P_-.                                        (10)
```

For example, `Rf=(f+v)/sqrt(2)`, whose product with its
adjoint is `P_+`. This verifies the transport using one
common operator `R`, rather than independent choices on the
two contexts.

The projections (6) have rational group-ring coefficients,
although (9) uses `sqrt(2)`. A rational transport is also
available: replace (9) by

```text
R_(c,s)=S+c(f+r)+s(v-v^*),       c,s real, c^2+s^2=1.
```

It sends `f` to `c^2 f+s^2 r+cs(v+v^*)`. Taking
`c=3/5`, `s=4/5` gives both the unitary and its transported
PVM rational coefficients and gives commutator norm `12/25`.

## 4. The displayed coefficients escape every finite packet

The quotient homomorphism `ell:G->Z` records shift exponent.
Every element of a finite subgroup has exponent zero. The
terms of `v=tf` have exponent one, and those of `v^*`
have exponent minus one. Both sums are nonzero: `f` is a
nonzero product of three independent lamp projections.

All other terms in (6) have exponent zero. Thus no cancellation
can remove either nonzero shift component of `P_+` or `P_-`.
Their support is contained in no finite subgroup of `G`.
The same applies to `R` and to the rational rotation with
`s!=0`.

Furthermore, any group element of nonzero shift exponent sends
the nontrivial subgroup `K` at site zero to a subgroup at a
different site. It cannot normalize `K`. Hence these finite
expressions genuinely involve elements outside `N_G(K)`.
They are not alternative notation for literal corner-preserving
group words.

Canonical trace shows every atom is nonzero:

```text
tau(q)=1/2,
tau(f)=tau(r)=1/8,
tau(S)=1/4,
tau(P_+)=tau(P_-)=1/8.                               (11)
```

In the normalized corner trace the two context distributions are
both `(1/2,1/4,1/4)`. The trace of `v` is zero because its
shift exponent is one.

Despite this support escape, the algebra generated by these two
PVMs is only

```text
M_2(C) direct-sum C.                                 (12)
```

Indeed `f,r,v,v^*` are matrix units on `f+r`, while `S`
is a separate nonzero scalar summand. Conversely `P_+` and
`f,r` recover the off-diagonal matrix units by multiplication.
Thus leaving all finite subgroup supports does not by itself
make the generated algebra infinite-dimensional.

## 5. The host has exact finite-window models

There is an elementary obstruction to completing `B_loop` in
this host. For a positive integer `N`, consider the finite group

```text
G_N=A^(Z/NZ) semidirect (Z/NZ).
```

Given any fixed finite collection of elements of `G` and the
finitely many products and inverses needed in a proposed finite
algebraic diagram, write them in wreath normal form. Only
finitely many lamp sites and integer shift exponents occur,
including those appearing during the required products.
Choose an interval containing all these sites and exponents,
and choose `N` larger than twice its diameter, enlarging it
further if necessary for the specified products.

Reduction of site indices and shift exponents modulo `N` is
then injective on these finite sets. It preserves each specified
product: no two distinct sites involved in that product become
identified, and the multiplication within each copy of `A`
is unchanged. It likewise preserves the required inverses.
This gives an injective multiplicative map on the finite window
into `G_N`.

This is a finite-window construction, not a global quotient map
from `G`: with nonabelian lamps, identifying two commuting
lamp copies at distant sites would not define a group
homomorphism on the whole wreath product.

For a fixed finite group-ring diagram, include every group
element and partial product in its expanded identities in the
chosen window. The finite-window map then preserves all those
identities coefficientwise. Distinct basis elements in the
specified supports remain distinct. The element `J_0` maps
to a nontrivial involution of `G_N`, so the image of `q` is
a nonzero full negative projection.

If a unital *-homomorphism `A(B_loop)->q C[G]q` with finite-support
generator images existed, its finitely many corner and BCS
relations would therefore give an exact map to the corresponding
nonzero corner of `C[G_N]`, for sufficiently large `N`.
The normalized finite-dimensional corner trace would be a
Connes-embeddable tracial state of `B_loop`, contradicting
its defining gap. Thus no such complete map exists in this host.

The cell (7) is a valid step beyond normalizer-only transport.
It proves that a common full augmentation unit and noncommuting
context atoms can coexist with explicit support outside every
finite subgroup. It does not provide the source-specific global
correlation which must also escape the finite-window models
of the ambient group.
