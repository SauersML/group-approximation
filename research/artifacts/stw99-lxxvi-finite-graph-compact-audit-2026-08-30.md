# STW LXXVI finite-graph compact-clutching audit

## Result

Let `X` be a connected finite graph, let `D` be simple, separable and
stably finite, and put `E=D tensor_min Z`.  Assume that both coefficients
have stable rank one and that the actual first-factor map
`Cu(D)->Cu(E)` is an isomorphism.  Then

```text
Cu(C(X,D))_c -> Cu(C(X,E))_c
```

is an isomorphism.  This removes every **global compact** obstruction over a
finite one-dimensional CW complex, with no restriction on `K_1(D)`.

It deliberately does not assert that the full Cu map is an isomorphism.
Phillips's circle-with-a-tail example shows that noncompact global elements
can retain clutching on a compact level set even when pointwise Cu data agree.
That supportwise corridor remains the exact finite-graph boundary.

## Stabilized graph calculation

All projections are taken in `C(X,D) tensor K = C(X,D tensor K)`; no
unitality of `D` is assumed.  For a nonzero projection `p`, connectedness
makes every fiber nonzero, and simplicity makes each fiber full.  A spanning
tree trivializes the resulting finitely generated projective module bundle.
Every chord contributes one gluing unitary in the full fiber corner.

Stable rank one is used at exactly one unstable point:

```text
U(q(D tensor K)q)/U_0 ~= K_1(q(D tensor K)q) ~= K_1(D).
```

Thus the graph bundle is classified by a fiber class and a one-cocycle.
For `b=rank H_1(X;Z)` this gives the natural additive description

```text
V(C(X,D))
 ~= {0} disjointUnion
    (V(D) minus {0}) times H^1(X;K_1(D))
 ~= {0} disjointUnion
    (V(D) minus {0}) times K_1(D)^b.                       (1)
```

The formula includes the projectionless case: if `V(D)^*` is empty, only
zero remains.  It also explains why simplicity is essential in this proof:
without it, a nonzero fiber corner need not be full, and the coefficient
system becomes ideal-dependent rather than the constant group `K_1(D)`.

A second proof of the stable coordinates is supplied by Schochet's Kunneth
theorem.  Since a connected graph has free K-theory,

```text
K_0(C(X,D)) ~= K_0(D) direct_sum K_1(D)^b
```

for arbitrary `D`; no UCT hypothesis on `D` is involved.  The tree/chord
argument identifies exactly which elements of this group are represented by
projections and proves cancellation, so this group calculation is a check on
(1), not a substitute for its positive-cone statement.

## Naturality under the Jiang--Su first-factor map

The coefficient Cu-isomorphism carries compact classes bijectively, hence
gives `V(D)~=V(E)`.  The map `C->Z` is a KK-equivalence; exterior product
therefore gives `K_1(D)~=K_1(E)` for the actual first-factor embedding,
without nuclearity or exactness of `D`.  Tensoring a graph module applies
these two maps to its fiber and chord coordinates.  Formula (1) is therefore
natural and proves the graph projection-monoid isomorphism.

The graph fields are stably finite.  Brown--Ciuperca then identify their
compact Cu elements with algebraically finitely generated projective modules,
so no compact positive class lies outside `V`.

## Pure-fiber corollary

If `D` is simple, separable, stably finite and pure, Lin's dichotomy gives
stable rank one, while the simple-case Cu theorem used by STW makes the
actual coefficient first-factor map an isomorphism.  The target is
Z-stable and has stable rank one.  Seth--Vilalta prove that `C(X,D)` is
pure.  Hence this is a genuine Problem LXXVI test class: the source has the
hypothesis, and every compact class is rigid, even when `K_1(D)` is
nonzero.

The remaining finite-graph question is entirely noncompact.  The result does
not extend the published pointwise formula past idealwise `K_1`-vanishing
and does not claim Cu-regularity of the whole graph field.

## Primary sources checked

- Antoine--Dadarlat--Perera--Santiago,
  [Recovering the Elliott invariant from the Cuntz semigroup](https://arxiv.org/abs/1109.5803),
  especially Proposition 2.2 (unitary patching on finite graphs), Theorems
  2.6 and 3.7, and Remark 3.9 (the supportwise warning).
- Brown--Ciuperca,
  [Isomorphism of Hilbert modules over stably finite C-star-algebras](https://doi.org/10.1016/j.jfa.2008.12.004),
  for compact Cu classes versus finitely generated projective modules.
- Seth--Vilalta,
  [Continuous functions over a pure C-star-algebra](https://arxiv.org/abs/2602.14809),
  for purity of the graph field.
- Huaxin Lin,
  [Strict comparison and stable rank one](https://doi.org/10.1016/j.jfa.2025.111065),
  for the simple pure stable-rank-one input.
