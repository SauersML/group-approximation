# STW LXXVI cactus and block-cut enriched-Cu audit

## Results

Let `D` be a simple separable stable-rank-one C*-algebra and put
`S=Cu(D)`.

### One-point wedge theorem

If finite graphs `Y` and `Z` meet in one point, with `y_0` identified with
`z_0`, restriction is a natural isomorphism

```text
Cu(C(Y wedge Z,D))
 ~= Cu(C(Y,D)) pullback_S Cu(C(Z,D)).                     (CW1)
```

The compatibility maps are evaluation at the identified point. Neither
factor is required to have a pointwise Cu formula.

### Block-cut reduction

Let `Blocks(X)` be the blocks of a connected finite graph: its maximal
2-connected subgraphs and its bridge edges. Then

```text
Cu(C(X,D))
 ~= { (xi_B)_B in product_B Cu(C(B,D)) :
      ev_v(xi_B)=ev_v(xi_B') whenever B and B' contain
      the same articulation vertex v }.                   (CW2)
```

All operations and order are coordinatewise. Formula (CW2) is an exact
reduction for every finite graph, not an explicit computation of a
2-connected block with several independent cycles.

### Explicit cactus formula

Suppose `X` is a connected finite cactus graph, equivalently every block is
a bridge edge or an embedded circle. Let `Cycles(X)` denote its cyclic
blocks. Point evaluation on the circle factors and restriction of global
lower-semicontinuous functions give

```text
Cu(C(X,D))
 ~= (product_{C in Cycles(X)} Cu(C(C,D)))
      pullback_{product_C Lsc(C,S)}
    Lsc(X,S).                                              (CW3)
```

The product over no cycles is omitted, so (CW3) reduces to the finite-tree
formula. A finite disconnected cactus is handled componentwise.

Consequently, finite-cactus formation preserves Cu-regularity for simple
separable stable-rank-one Cu-regular fibers. In particular, if `D` is simple,
separable, stably finite, and pure, then `C(X,D)` is pure and Cu-regular for
every finite cactus `X`, with arbitrary projections and arbitrary `K_1(D)`.

## Surjectivity of the one-point wedge map

At the C*-level,

```text
C(Y wedge Z,D)
 = C(Y,D) pullback_D C(Z,D),                              (CW4)
```

and both evaluation maps are surjective. Take compatible classes
`x in Cu(C(Y,D))` and `z in Cu(C(Z,D))`. Represent them by countably
generated Hilbert modules `E_Y` and `E_Z`. Compatibility says that their
fibers at the identified point have the same class in `Cu(D)`.

For a stable-rank-one algebra, Cuntz-equivalent countably generated Hilbert
modules are isomorphic. Thus there is a fiber-module isomorphism

```text
U:(E_Y)_{y_0} -> (E_Z)_{z_0}.                             (CW5)
```

The standard Hilbert-module pullback along (CW5) is a countably generated
module over (CW4), because the algebras and modules are separable and the
evaluation maps are surjective. Its restrictions are `E_Y` and `E_Z`.
Therefore (CW1) is surjective.

A different choice of `U` does not create a relative class. This follows
from the one-point orbit lift used for order reflection below.

## The one-point orbit lift

Let `W` be a finite graph, let `w_0 in W`, let
`g in C(W,D tensor K)_+`, and suppose `zz^* in Her(g)`. Given

```text
u_0 in U(Her(g(w_0))~)
```

and `eta>0`, there is a continuous vector `z_eta` such that

```text
z_eta(w_0)=u_0z(w_0),
z_eta z_eta^* in Her(g),
||z_eta^*z_eta-z^*z||<eta.                               (CW6)
```

If `g(w_0)=0` then `z(w_0)=0` and there is nothing to change. Otherwise
consider the component `U` of `supp(g)` containing `w_0`.

If `U=W`, every fiber of `Her(g)` is nonzero and full because `D` is simple.
Antoine--Dadarlat--Perera--Santiago, Proposition 2.2 and Remark 2.3, extend
the single prescribed unitary `u_0` to a global hereditary unitary. The
`K_1` compatibility condition is vacuous because only one fiber value is
prescribed. Multiplying `z` gives (CW6) with zero source-square error.

If `U` is proper, choose a compact finite subgraph `K` inside `U` which
contains `w_0` and every point where the relevant comparison vector has norm
at least a small `delta`. Lift `u_0` on `K`. In the finitely many boundary
collars, splice the lifted vector back to `z` where both tend to zero. The
splice stays in the hereditary right ideal, and its source-square error is
at most

```text
2 delta (||z_eta||+||z||).
```

Choose `delta` first. This proves (CW6), without extending `u_0` across a
zero or declaring it null-homotopic.

For a compact circle projection bundle with clutching unitary `h`, the same
fact has a concrete gauge description. A prescribed fiber automorphism `u`
requires a path from `u` to `h^{-1}uh`. Conjugation preserves its `K_1`
class, and stable rank one identifies unitary components with `K_1`, so the
path exists. It is a bundle automorphism and does not alter the original
clutching class.

## Order reflection and naturality

Suppose the two restrictions of `a` are Cuntz below the corresponding
restrictions of `b` in the right side of (CW1). Run the standard pullback
comparison-vector construction. Stable rank one supplies an alignment
unitary at the one common fiber. Apply (CW6) on the child factor to absorb
that unitary, then use the usual partition-of-unity estimate. Letting the
source-square error tend to zero gives `a Cuntz-below b`. Thus restriction
reflects order and proves (CW1).

All maps in (CW1) are restrictions and evaluations. The Hilbert-module
pullback and the comparison construction commute with coefficient
*-homomorphisms, so the isomorphism is natural.

## From wedges to the block-cut tree

The block-cut incidence graph of a connected finite graph is a tree. Root
it at one block. A leaf block meets the union of the preceding blocks at
exactly its parent articulation vertex, so (CW1) attaches it by one fiber
product over `S`. Removing leaf blocks inductively proves (CW2).

This also gives a general permanence reduction. For a coefficient map
`phi:D->E` between the relevant stable-rank-one coefficients, if

```text
Cu(C(B,phi)):Cu(C(B,D))->Cu(C(B,E))
```

is an isomorphism for every block `B`, then `Cu(C(X,phi))` is an isomorphism.
This does not infer the hypothesis for an unknown multi-cycle block.

## Reorganizing a cactus invariant

For a bridge block, Antoine--Dadarlat--Perera--Santiago, Theorem 2.6, gives

```text
Cu(C([0,1],D)) ~= Lsc([0,1],S).
```

For a cyclic block `C`, their Theorem 3.7 gives the actual hybrid circle
semigroup

```text
Cu(C(C,D))
 ~= V(C(C,D)) disjointUnion Lsc_nc(C,S).                  (CW7)
```

Here `Lsc_nc` means noncompact as an element of `Lsc`. Gluing all bridge
functions and all circle evaluation functions at the articulation vertices
produces exactly one global element of `Lsc(X,S)`. Keeping the actual circle
classes as additional coordinates reorganizes (CW2) into (CW3).

The use of the actual circle semigroup makes (CW3) coefficient-natural.
One must not pretend that a general coefficient Cu map alone determines the
compact `K_1` clutching coordinate.

## Exact fibers and cactus gluing law

For `F in Lsc(X,S)` define

```text
m_X(F)
 = number of cyclic blocks C for which F|C is
   a nonzero constant compact class.                       (CW8)
```

The finite-graph compact-clutching theorem gives, for each such circle and
a representative nonzero projection `p`,

```text
K_1(Her(p)) ~= K_1(D),                                    (CW9)
```

because simplicity makes `Her(p)` full. The zero projection has only the
zero bundle. The ADPS noncompact circle sector has one lift of its evaluation
function. Therefore point evaluation is surjective and

```text
hat^{-1}(F) ~= K_1(D)^{m_X(F)}.                           (CW10)
```

The coordinates in (CW10) are independent, even when two circle blocks meet
at an articulation vertex. Compatibility equates their underlying value
`F(v)`, not their monodromies. A bouquet of two circles with constant
nonzero compact fiber `p` has exactly the pair of labels

```text
(kappa_1,kappa_2) in K_1(D)^2,
```

and no relative wedge label.

Addition and order are coordinatewise in (CW3), using the exact ADPS mixed
circle laws. On a given circle:

- two compact labels add in `K_1(D)`;
- adding data whose circle restriction is zero preserves the label;
- adding a noncompact circle class moves to the unique noncompact sector and
  erases the label; and
- compact-label order is equality of labels at equal fiber class, while a
  proper projection complement can carry any difference of labels.

Thus point evaluation is an isomorphism for every forest. If a cactus `X`
has at least one cyclic block, then

```text
Cu(C(X,D)) -> Lsc(X,Cu(D)) is an isomorphism
iff K_1(D)=0 or D is stably projectionless.                (CW11)
```

## Cu-regularity and purity

Suppose `D` is simple, separable, stable rank one, and Cu-regular for the
actual first-factor map, and put `E=D tensor_min Z`. The established circle
theorem makes the actual first-factor map an isomorphism on every cyclic
block. The interval theorem and the coefficient Cu-isomorphism do the same
for every bridge block. Naturality of (CW2), or directly of (CW3), gives

```text
Cu(C(X,D)) ~= Cu(C(X,E))
```

for every finite cactus `X`.

If `D` is simple, separable, stably finite, and pure, Lin and the simple-case
STW theorem supply these hypotheses. Seth--Vilalta separately gives purity
of `C(X,D)`.

## Sharp boundary

A cactus may have arbitrarily many cycles and they may meet at articulation
vertices. Thus global first Betti number greater than one is no longer a
boundary.

What remains is a 2-connected block with first Betti number at least two,
for example a theta graph. Its cycles overlap inside one block and cannot be
peeled apart at a single fiber. Formula (CW2) isolates that block but does
not compute it. No independent circle-label formula or Cu-regularity theorem
for such a block is asserted.

## Independent hostile audit

Two independent audits tested:

- Hilbert-module pullback surjectivity and countable generation;
- order reflection for compact, soft, and support-vanishing child factors;
- the figure-eight projection bundle and possible relative wedge unitary;
- multiple descendant articulation vertices;
- independence and support sensitivity of the labels in (CW10);
- coefficient naturality and the actual first-factor map; and
- the boundary between a cactus and a multi-cycle 2-connected block.

No extra articulation invariant or counterexample was found. The audits
rejected any claim that (CW2) computes the remaining 2-connected blocks.

## Primary sources checked

- Antoine--Dadarlat--Perera--Santiago,
  [Recovering the Elliott invariant from the Cuntz semigroup](https://arxiv.org/abs/1109.5803),
  especially Proposition 2.2, Remark 2.3, Theorems 2.6 and 3.7, and
  Remark 3.9.
- Antoine--Perera--Santiago,
  [Pullbacks, C(X)-algebras, and their Cuntz semigroup](https://arxiv.org/abs/1101.4776),
  for the comparison-vector pullback estimates.
- Coward--Elliott--Ivanescu,
  [The Cuntz semigroup as an invariant for C*-algebras](https://doi.org/10.1016/j.jreineangew.2007.10.008),
  for stable-rank-one Hilbert-module realization.
- Brown--Ciuperca,
  [Isomorphism of Hilbert modules over stably finite C*-algebras](https://doi.org/10.1016/j.jfa.2008.12.004),
  for compact Cu classes and projective modules.
- Seth--Vilalta,
  [Continuous functions over a pure C*-algebra](https://arxiv.org/abs/2602.14809),
  for purity of the cactus field.
