# Quadratic curvature cannot be completed by regular defect tails alone

The uniform quadratic-rank normal form leaves an actual dilation problem.
This audit tests one concrete construction: attach Hilbert spaces indexed
by the Cayley graph, or induced from finite stabilizers, to the small
curvature space and seek a genuine representation containing an almost
unitary copy of the original tuple.

There is a dimension-free obstruction to that construction. For a Kazhdan
group, an almost unitary d-dimensional corner of a genuine representation
must lie almost entirely in that representation's finite-dimensional
sector. Regular defect tails have no such sector. Even an infinite number
of regular tails together with an `o(d)`-dimensional exact seed cannot
supply the required corner. The proof gives an explicit error floor.

## 1. The finite-dimensional-sector mass inequality

Let `G` have a finite symmetric Kazhdan set `S` and constant `kappa>0`
in the convention

```text
dist(x,H^G)<=kappa^(-1) max_(s in S)||pi(s)x-x||
```

for every genuine unitary representation. Let
`Pi:G->U(K)` be any genuine representation, with K possibly infinite,
and let `W:C^d->K` be an isometry. Suppose `U_s in U(d)` are arbitrary
unitaries and

```text
epsilon=max_(s in S)||W^*Pi(s)W-U_s||_(2,d).
```

Let `K_fd` be the closed span of all finite-dimensional invariant
subspaces of Pi, and let `Q_fd` be its orthogonal projection. Then

```text
(1/d)Tr(W^*(I-Q_fd)W) <= 4 epsilon/kappa^2.              (QFD1)
```

The trace on the left is the ordinary finite-dimensional trace divided
by d. No normalization by the possibly much larger dimension of K is
used. In particular, at least `1-4epsilon/kappa^2` of the prescribed
corner's mass must be in `K_fd`.

Proof. Put `P=WW^*` and `A_s=W^*Pi(s)W`. These are contractions, and

```text
||Pi(s)W-WU_s||_HS^2/d
 =2-2 Re tr_d(U_s^* A_s)
 <=2||U_s-A_s||_(2,d)<=2epsilon.
```

Since P and its conjugate have the same finite rank,

```text
||Pi(s)P Pi(s)^*-P||_HS^2
 =2||(I-P)Pi(s)W||_HS^2
 <=4epsilon d.                                        (QFD2)
```

Use the genuine conjugation representation on the Hilbert space of
Hilbert--Schmidt operators on K, and let E be orthogonal projection onto
its invariant vectors. Property `(T)` gives

```text
||P-E(P)||_HS^2 <=4epsilon d/kappa^2.                   (QFD3)
```

Every invariant Hilbert--Schmidt operator is supported on `K_fd` on both
sides. To see this, if a compact operator T commutes with Pi, so do
`T^*T` and `TT^*`. Every positive nonzero spectral subspace of either is
finite-dimensional and Pi-invariant. Their closed spans contain the
initial and final spaces of T. Thus `(I-Q_fd)T=T(I-Q_fd)=0`.

Apply this to `E(P)`. Left multiplication by `I-Q_fd` is a contraction
in Hilbert--Schmidt norm, so

```text
Tr(P(I-Q_fd))
 =||(I-Q_fd)P||_HS^2
 <=||P-E(P)||_HS^2.
```

Since `Tr(P(I-Q_fd))=Tr(W^*(I-Q_fd)W)`, division by d proves `(QFD1)`.

## 2. Small exact seeds plus arbitrarily many regular tails fail

Suppose Pi is a direct sum of an exact finite-dimensional seed of
dimension k and a representation with no nonzero finite-dimensional
invariant subspaces. Then `dim(K_fd)<=k`, so `(QFD1)` implies

```text
epsilon >= (kappa^2/4) (1-k/d).                         (QFD4)
```

The conclusion is nontrivial when `k<d`. If `k=o(d)`, the error stays
at least `kappa^2/4-o(1)`. This is true even if the second summand is
infinite-dimensional and the corner W mixes its coordinates arbitrarily
with the finite seed.

For an infinite group, every multiple `lambda_G tensor I_L` of the
regular representation has no finite-dimensional invariant subspace.
Indeed, a finite-rank invariant projection would have identical diagonal
blocks at every `g in G`, by translation invariance. Its finite trace is
the sum of the traces of these positive blocks over infinitely many g,
so every diagonal block is zero; positivity forces the projection itself
to be zero. Closed invariant subspaces, unitary quotients, and Hilbert
direct sums preserve the absence of finite-dimensional subrepresentations.

An induced representation from a **finite** stabilizer also embeds into
a regular multiple. For a representation `sigma:H->U(L)` with H finite,
realize `Ind_H^G sigma` as functions satisfying
`f(gh)=sigma(h)^(-1)f(g)`, square-summable over `G/H`. The map
`f -> |H|^(-1/2)f` embeds this space isometrically into
`ell^2(G) tensor L` and intertwines the left G-action. Thus finite-cell
or finite-stabilizer defect modules built this way fall under `(QFD4)`.

In particular, if a quadratic-rank curvature support has dimension
`r=O(delta^2 d)`, using only an `O(r)`-dimensional exact seed and regular
tails leaves an error bounded away from zero. To obtain a successful
dilation, the construction must create finite-dimensional representation
content with total corner overlap `d-o(d)`, not merely represent the
small defect space correctly. This is a content requirement on the
genuine dilating representation, not a bound on how much ambient space
one is allowed to add.

## 3. A reduced-algebra ucp construction has the same obstruction

For an infinite Kazhdan group, no representation of `C*_r(G)` contains
a nonzero finite-dimensional group subrepresentation. Here is a proof
that makes the needed representation-theoretic step explicit.

If a finite-dimensional representation sigma were weakly contained in
the regular representation, then `sigma tensor conjugate(sigma)` would
be weakly contained in `lambda_G tensor conjugate(sigma)`. Tensoring a
weak-containment relation with a finite-dimensional representation
preserves it; equivalently, apply the representation of `C*_r(G)`
entrywise to its finite matrix amplification. Fell absorption is explicit
here: on `ell^2(G) tensor conjugate(H_sigma)`, the unitary

```text
delta_g tensor v |-> delta_g tensor conjugate(sigma)(g^(-1))v
```

intertwines `lambda_G tensor conjugate(sigma)` with a multiple of
`lambda_G`. The tensor product `sigma tensor conjugate(sigma)` contains
an invariant vector (the identity operator on `H_sigma`). Therefore the
trivial representation would be weakly contained in the regular one.
This supplies almost invariant vectors in regular multiples, and property
`(T)` would supply a nonzero invariant vector there, impossible for an
infinite group. This proves the assertion.

Now let `Phi:C*_r(G)->M_d` be any ucp map, and let `U_s` be any unitary
tuple. Its Stinespring representation Pi still factors through the
reduced algebra, so its finite-dimensional sector is zero. Applying
`(QFD1)` to the Stinespring isometry gives

```text
max_(s in S)||Phi(lambda_G(s))-U_s||_(2,d)
 >= kappa^2/4.                                        (QFD5)
```

Thus constructing a positive-definite corner through the reduced group
algebra cannot work even if no finite-dimensional bound is imposed on
the dilation. Full-group-algebra positive-definite functions are a
different matter: genuine finite quotient representations can supply
their finite-dimensional sector, and `(QFD5)` makes no assertion about
those full-algebra ucp maps.

## 4. Consequence for the current arithmetic construction

The group `SL_5(Z)` is infinite and Kazhdan, so every estimate above
applies. Its QRC normal form can leave hard relator errors supported on
`O(delta^2 d)` dimensions at a fixed residual tolerance. This gives a
small budget for adding genuinely missing finite-dimensional components;
it does not say that an induced regular defect module is such a
component.

The moving-Schreier certificate avoids this particular obstruction by
inducing a **genuine representation of a finite-index subgroup**. Its
induced ambient representation is itself finite-dimensional when that
subgroup representation is finite-dimensional. But supplying that exact
subgroup holonomy is still necessary; replacing it by regular tail
spaces invokes the obstruction just proved.

This audit does not prove nonexistence of a flexible correction. It rules
out a definite family of constructions and quantifies what an affirmative
dilation must add: an exact finite-dimensional representation sector
carrying nearly all of the prescribed corner. Constructing that sector
from the quadratic hard-curvature data remains unresolved.

All estimates are analytic and use a genuine representation only after
it is explicitly supplied as a dilation candidate. No almost
representation is substituted into a Kazhdan averaging argument. No code,
build, job, commit, or branch was used.
