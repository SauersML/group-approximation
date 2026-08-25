---
rg: 2
id: intrinsic-full-mf-radical-core-proof
kind: route
title: Generate the intrinsic core and use functoriality of the MF radical
target: intrinsic-full-mf-radical-core
requires: []
artifacts:
  - GroupApproximation/Sofic/FullMFRadicalCore.lean
  - GroupApproximation/Sofic/FullMFRadicalExactness.lean
  - GroupApproximation/Sofic/FullMFRadicalReflection.lean
  - GroupApproximation/Sofic/FullMFRadicalProducts.lean
  - GroupApproximation/Sofic/FullMFRadicalExtensions.lean
  - GroupApproximation/Sofic/FullMFRadicalLocalization.lean
  - GroupApproximation/Sofic/FullMFRadicalPullback.lean
  - GroupApproximation/Sofic/FullMFRadicalClosurePullback.lean
  - GroupApproximation/Sofic/FullMFRadicalQuotientLattice.lean
  - GroupApproximation/Sofic/FullMFRadicalVisibleLocalization.lean
---

# Proof

For a group `G`, let

```text
C(G) = join { K ≤ G : Rad_MF(K)=K }.
```

First, `C(G)` is itself full-radical.  Let `rho` be a matrix-corona
representation of `C(G)`.  For every full-radical subgroup `K ≤ G`, compose
`rho` with the inclusion

```text
K --> C(G).
```

The composite is trivial because `Rad_MF(K)=K`.  Hence `ker(rho)` contains
every such `K`, and therefore contains their join `C(G)`.  Thus `rho` is
trivial and

```text
Rad_MF(C(G))=C(G).                                    (1)
```

Second, the inclusion `K --> G` carries `Rad_MF(K)` into `Rad_MF(G)` by
functoriality.  Every subgroup occurring in the join defining `C(G)` is
therefore contained in `Rad_MF(G)`.  Taking the join gives

```text
C(G) ≤ Rad_MF(G).                                     (2)
```

Third, let `f : G --> H`.  The image of a full-radical group under a
surjective homomorphism is full-radical.  Applying this to the canonical
surjection

```text
C(G) --> f(C(G))
```

and using (1) shows that `f(C(G))` is one of the subgroups generating `C(H)`.
Consequently

```text
f(C(G)) ≤ C(H).                                       (3)
```

Taking `f` to be an inner automorphism proves normality; taking an arbitrary
automorphism and its inverse proves characteristicity.

Equation (1), applied with `G` replaced by `C(G)`, gives

```text
C(C(G)) = C(G),                                       (4)
```

where the formal subgroup statement is `fullMFRadicalCore C(G) = top`.

For the quotient statement, let `q : G --> G/C(G)` and suppose
`K ≤ G/C(G)` is full-radical.  Its preimage `P=q^{-1}(K)` fits into an exact
sequence

```text
1 --> C(G) --> P --> K --> 1.
```

Both the kernel and target are full-radical, so closure under extensions makes
`P` full-radical.  Its defining maximality gives `P ≤ C(G)`.  Every element of
`K` has a lift in `P`, hence is trivial.  Therefore

```text
C(G/C(G)) = 1.                                       (5)
```

Functoriality now gives the universal property.  If `f : G --> H` and
`C(H)=1`, then

```text
f(C(G)) ≤ C(H)=1,
```

so `C(G) ≤ ker(f)`.  If also `C(G)=G`, then `f` is trivial.

For uniqueness, suppose `N` is normal, `Rad_MF(N)=N`, and `C(G/N)=1`.
The first condition gives `N ≤ C(G)`.  Applying the universal property to
the quotient map `G --> G/N` gives `C(G) ≤ N`.  Hence `N=C(G)`.

Finally, (2) proves `C(G)=G => Rad_MF(G)=G`.  Conversely, if
`Rad_MF(G)=G`, then the top subgroup of `G` is itself full-radical and occurs
among the generators defining `C(G)`.  Hence

```text
C(G)=G  <=>  Rad_MF(G)=G.                             (6)
```

For exactness, let `f : G --> H` be onto with full-radical kernel, and let
`K ≤ H` be full-radical.  Its preimage `P=f^{-1}(K)` fits into

```text
1 --> ker(f) --> P --> K --> 1.
```

Closure under extensions makes `P` full-radical, hence `P ≤ C(G)`.  Every
element of `K` lifts to `P`, so `K ≤ f(C(G))`.  Functoriality gives the
reverse inclusion and therefore

```text
f(C(G)) = C(H).                                       (7)
```

For a full-radical normal subgroup `N`, apply (7) to `G --> G/N`.  Finally,
if `C(G)=1` and `K ≤ G`, functoriality of the inclusion `K --> G` forces
`C(K)=1`; thus the core-free class is subgroup-closed.  The orthogonality
characterization follows by applying any proposed orthogonality condition to
the canonical core-free quotient `G --> G/C(G)`.

For the universal property, every map `f : G --> H` with `C(H)=1` kills
`C(G)`, so quotient lifting gives a factor

```text
G/C(G) --> H.
```

The factor is unique because the quotient map is onto.  Applying the same
lifting construction to the composite

```text
G --> H --> H/C(H)
```

defines the map induced by an arbitrary homomorphism `G --> H`.  Equality of
induced maps can be checked after precomposition with the quotient map; this
proves preservation of identity maps and composition.

For products, the two coordinate projections carry `C(G × H)` into `C(G)`
and `C(H)`.  This gives one implication in

```text
(g,h) ∈ C(G × H)  <=>  g ∈ C(G) and h ∈ C(H).
```

For the converse, the two coordinate inclusions carry `C(G)` and `C(H)` into
`C(G × H)`.  The elements `(g,1)` and `(1,h)` therefore lie in the product
core, and their product is `(g,h)`.  The full-core and core-free product
criteria follow by setting the three cores equal to the top or bottom
subgroups.

Closure of the full-core class under extensions is the corresponding closure
theorem for the genuine-corona MF residual, translated through

```text
C(G)=G  <=>  Rad_MF(G)=G.
```

For the core-free extension law, let `f : G --> H` have core-free target and
core-free kernel.  Functoriality gives `C(G) ≤ ker(f)`.  Regard this inclusion
as a homomorphism

```text
C(G) --> ker(f).
```

Its source is intrinsically full by idempotence, while its target is
core-free, so orthogonality makes the inclusion trivial.  Hence `C(G)=1`.
Taking `f` to be a quotient map gives closure of the core-free class under
extensions.

Finally, suppose `f : G --> H` is onto with intrinsically full kernel.  Since
`ker(f) ≤ C(G)`, the quotient map `G --> G/C(G)` descends along `f` to a map

```text
H --> G/C(G).
```

The target is core-free, so the universal property factors this map through
`H/C(H)`.  The resulting map is a left inverse to the map induced by `f`.
Surjectivity of `f` makes the induced map onto, hence it is an isomorphism.

The same hypotheses determine the source core before quotienting.  Functoriality
gives

```text
C(G) <= f^(-1)(C(H)).
```

For the reverse inclusion, take `x` with `f(x)` in `C(H)`.  Exactness of the
core image supplies `c in C(G)` with `f(c)=f(x)`.  Then `x c^(-1)` lies in the
kernel, hence in `C(G)`, and therefore `x` lies in `C(G)`.  This proves the
pullback formula (17).

If the target is core-free, functoriality first gives `C(G) <= ker(f)`.  When
the kernel is intrinsically full, maximality gives the reverse inclusion.
This proves (18) without requiring `f` to be onto.

For the genuine corona residual, intrinsic fullness of the kernel first puts
`ker(f)` inside `Rad_MF(G)`.  Every corona representation of `G` therefore
factors uniquely through the surjection `f`.  Intersecting kernels before and
after factorization gives

```text
Rad_MF(G) = f^(-1)(Rad_MF(H)).
```

This proves (19).  If the target residual is trivial, functoriality gives the
upper inclusion in (20).  For the reverse inclusion, the inclusion
`ker(f) --> G` maps the full residual of the kernel into `Rad_MF(G)`.  Hence
the residual equals the kernel, without a surjectivity assumption.

For the closure pullback, let `N` be normal in `G`.  An element of
`Cl_MF^G(N)` is killed by every corona representation of `G` that kills `N`.
Composing a representation of `H` that kills `f(N)` with `f` proves

```text
Cl_MF^G(N) <= f^(-1)(Cl_MF^H(f(N))).
```

Conversely, `ker(f) <= Rad_MF(G)` makes every corona representation of `G`
factor through `f`.  If such a representation kills `N`, its factor on `H`
kills `f(N)`.  Therefore every element of the displayed preimage is killed,
which proves (21).

If `Cl_MF^G(N)=N`, then the residual containment
`Rad_MF(G) <= Cl_MF^G(N)` gives `ker(f) <= N`.  Mapping (21) onto `H` gives
`Cl_MF^H(f(N))=f(N)`.  Conversely, these two conditions turn (21) into

```text
Cl_MF^G(N)=f^(-1)(f(N))=N,
```

which proves (22).  For countable groups, applying the characterization

```text
Cl_MF^G(N)=N  <=>  G/N is MF
```

on both sides of (22) proves (23).

For (24), regard an MF-closed normal subgroup together with its normality and
closure equation as one ordered object.  Formula (22) shows that image along
`f` and inverse image along `f` preserve these objects.  The subgroup identities

```text
f(f^(-1)(M)) = M,
f^(-1)(f(N)) = N  when ker(f) <= N
```

show that the two operations are mutually inverse.  The same identities show
that they preserve and reflect inclusion.

For (25), apply the radical pullback formula to `f`.  If `g(f(x))=1`, then
`f(x)` lies in `ker(g)`, hence in `Rad_MF(H)`.  Pulling this membership back
along `f` puts `x` in `Rad_MF(G)`.  Images of subgroups satisfy

```text
(g o f)(N) = g(f(N)),
```

so the two order isomorphisms compose.

Every homomorphism `f : G --> H` induces a map

```text
G/Rad_MF(G) --> H/Rad_MF(H)
```

by functoriality of the radical.  Under the hypotheses above, surjectivity of
`f` makes this map onto.  If the class of `x` maps to the identity, then
`f(x)` lies in `Rad_MF(H)`; the pullback formula puts `x` in `Rad_MF(G)`, so
its original class was already the identity.  The induced map is therefore
bijective and hence an isomorphism, proving (26).

The Lean proof follows these steps directly.
