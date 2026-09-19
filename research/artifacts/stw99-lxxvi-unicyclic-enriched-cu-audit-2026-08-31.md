# STW LXXVI unicyclic enriched-Cu audit

## Result

Let `X` be a connected finite graph with first Betti number one, let
`Gamma` be its unique embedded circle, and let `D` be a simple separable
stable-rank-one C*-algebra. Put `S=Cu(D)`. Restriction and point evaluation
give a natural isomorphism in `Cu`

```text
Cu(C(X,D))
  ~= Cu(C(Gamma,D))
       pullback_{Lsc(Gamma,S)}
     Lsc(X,S).                                             (UC1)
```

The two maps to `Lsc(Gamma,S)` are circle point evaluation and restriction
of lower-semicontinuous functions. Thus an element is exactly a pair
`(xi,F)` consisting of the actual circle class `xi` and the global pointwise
function `F`, subject to

```text
hat(xi)=F restricted to Gamma.                             (UC2)
```

Addition, order, increasing suprema, and compact containment are those of
this fiber product. In particular the circle coordinate is not discarded
when the global element is noncompact.

For a finite pseudoforest, apply (UC1) to every unicyclic component and the
finite-tree pointwise formula to every tree component. Consequently, if `D`
is Cu-regular for the actual first-factor map, then `C(X,D)` is Cu-regular
for every finite pseudoforest `X`. If `D` is also pure, then `C(X,D)` is pure.
There is no restriction on projections or on `K_1(D)`.

## The circle coordinate

Antoine--Dadarlat--Perera--Santiago, Theorem 3.7, gives

```text
Cu(C(Gamma,D))
 ~= V(C(Gamma,D)) disjointUnion Lsc_nc(Gamma,S).           (UC3)
```

Here `Lsc_nc` means noncompact as an element of the lower-semicontinuous
function semigroup, not pointwise noncompact. Since `Gamma` is connected,
the compact elements omitted from `Lsc_nc` are precisely the constant
compact-valued functions.

The finite-graph projection calculation, or equivalently the usual circle
clutching construction plus stable-rank-one cancellation, gives

```text
V(C(Gamma,D))
 ~= {0} disjointUnion
    (V(D) minus {0}) times K_1(D).                         (UC4)
```

For `0 not equal p in V(D)`, simplicity makes
`Her(p)=p(D tensor K)p` full. Morita invariance and stable rank one give

```text
U(Her(p)~)/U_0 ~= K_1(Her(p)) ~= K_1(D),                  (UC5)
```

which is exactly the clutching-label set. The zero projection bundle has
only one class.

The mixed laws in (UC3) matter. The order on the projection sector is its
algebraic order. The noncompact sector has pointwise addition and order. If
`P` is a projection class and `f` is in `Lsc_nc`, then

```text
f <= P  iff  f(t) <= hat(P)(t) for every t,
P <= f  iff  hat(P)+g=f for some g in Lsc_nc.              (UC6)
```

Also `P+f=hat(P)+f` lies in the noncompact sector. Thus a soft circle
summand erases a clutching label, whereas data supported only on the attached
trees has zero circle coordinate and preserves the label.

## The arbitrary-base one-ended leaf lemma

Let `Y` be any compact space, let `v in Y`, and attach one interval at its
zero endpoint:

```text
Z=Y union_v [0,1],
C(Z,D)=C(Y,D) pullback_D C([0,1],D).                       (UC7)
```

For the finite-graph application, `Y` is the graph already constructed.
There is an order isomorphism

```text
Cu(C(Z,D))
 ~= Cu(C(Y,D)) pullback_{Cu(D)} Cu(C([0,1],D)).            (UC8)
```

Crucially, (UC8) does not require point evaluation on `Cu(C(Y,D))` to be
injective.

Surjectivity is the published pullback theorem. The endpoint evaluation
`C([0,1],D)->D` is surjective, and Antoine--Dadarlat--Perera--Santiago,
Theorem 2.6, makes evaluation on the new interval an order embedding.
Antoine--Perera--Santiago, Theorem 3.3(i), therefore makes the restriction
map in (UC8) surjective.

For order reflection, start with genuine Cuntz comparisons in the two
coordinates of the right-hand side of (UC8). The standard pullback proof
chooses comparison vectors on `Y` and on the new interval. Stable rank one
produces a unitary in the unitization of the hereditary gluing fiber which
aligns their values at `v`.

Only the new interval vector must be changed. If `g` is its positive target,
`zz^* in Her(g)`, and `u_0 in U(Her(g(0))~)` is the alignment unitary, then
for every `eta>0` there is `z_eta` with

```text
z_eta(0)=u_0z(0),
z_eta z_eta^* in Her(g),
||z_eta^*z_eta-z^*z||<eta.                                (UC9)
```

If the support component of `g` reaches the free endpoint, Proposition 2.2
and Remark 2.3 of Antoine--Dadarlat--Perera--Santiago propagate `u_0` with
no terminal condition. If the component ends at `s<1`, propagate on a
compact initial segment and splice `u_0z` back to `z` where `z` tends to
zero. The splice is made on vectors in the hereditary right ideal, not on
unitaries, so no null-homotopy of `u_0` is asserted. The source-square error
is bounded by

```text
2 delta (||z_eta||+||z||)
```

when both vectors have norm below `delta` on the splice. Letting `delta`
decrease proves (UC9). The partition-of-unity comparison estimate in the
pullback proof then proves order reflection in (UC8). Notice that no
pointwise comparison theorem on the old base `Y` entered: its coordinate
was compared in the actual semigroup `Cu(C(Y,D))`.

Because (UC8) is induced by restriction maps and the interval identification
is evaluation, it is natural for coefficient *-homomorphisms.

## Iteration from the cyclic core

Every connected finite unicyclic graph is obtained from `Gamma` by finitely
many leaf-edge attachments. Suppose (UC1) holds for the graph `Y` already
constructed and attach one more leaf. Combine (UC8) with the interval formula
and the elementary gluing identity

```text
Lsc(Y union_v [0,1],S)
 ~= Lsc(Y,S) pullback_S Lsc([0,1],S).                     (UC10)
```

Associativity of the fiber products leaves the circle factor unchanged and
replaces `Lsc(Y,S)` by the left side of (UC10). Induction proves (UC1).
This also proves the claimed naturality.

## Exact fibers of point evaluation

Define

```text
M_X={F in Lsc(X,S):
     F restricted to Gamma is the constant function p
     for some nonzero p in V(D)}.                          (UC11)
```

The global point-evaluation map is always surjective. Formulae (UC1)--(UC4)
give its exact fibers:

```text
hat^{-1}(F) ~= K_1(D)  if F is in M_X,
hat^{-1}(F) is a singleton otherwise.                     (UC12)
```

For `F in M_X`, write a lift as `(F,kappa)`. Two labeled lifts add by

```text
(F,kappa)+(G,lambda)=(F+G,kappa+lambda).                  (UC13)
```

Adding an element whose circle restriction is zero preserves `kappa`.
Adding an element whose circle restriction lies in `Lsc_nc` moves the sum
to the unique noncompact circle sector and erases `kappa`.

If labeled elements have circle fibers `p` and `q`, then

```text
(F,kappa) <= (G,lambda)
```

exactly when `F<=G` off the circle and the circle projection classes are
ordered. Equivalently, either `q=p+r` for a nonzero `r in V(D)`, in which
case the labels impose no restriction, or `p=q` and `kappa=lambda`. All
mixed cases use the exact circle rules (UC6), not a falsely pointwise compact
order.

It follows sharply that, for a connected unicyclic graph,

```text
Cu(C(X,D)) -> Lsc(X,Cu(D)) is an isomorphism
iff K_1(D)=0 or D is stably projectionless.                (UC14)
```

Indeed, either condition makes every fiber in (UC12) a singleton. Conversely,
a nonzero projection `p` is full and every nonzero element of `K_1(D)` gives
two different circle bundles over the constant function `p`.

For a disconnected finite pseudoforest, a function receives one independent
`K_1(D)` label for each cyclic component on which its restriction is a
nonzero constant compact class.

## Cu-regularity and pure-fiber consequences

First suppose the simple separable stable-rank-one coefficient `D` is
Cu-regular for its actual first-factor map, and put
`E=D tensor_min Z`. Lin gives stable rank one for both coefficients, while
the simple-case STW theorem gives the actual coefficient Cu-isomorphism.
The established circle theorem gives

```text
Cu(C(Gamma,D)) ~= Cu(C(Gamma,E))
```

for the actual first-factor map. Pointwise application of
`Cu(D)->Cu(E)` gives the isomorphism on the `Lsc` factors. These maps commute
with restriction, so (UC1) identifies the unicyclic first-factor map with an
isomorphism of fiber products. Tree components use the finite-tree theorem, and finite direct sums handle a
pseudoforest. Thus finite-pseudoforest formation preserves Cu-regularity in
the simple stable-rank-one class.

In particular, if `D` is simple, separable, stably finite, and pure, Lin and
the simple-case STW theorem supply these hypotheses. Seth--Vilalta separately
gives purity of `C(X,D)`.

In the explicit coordinates, the same conclusion says that the coefficient
Cu-isomorphism preserves compact fiber classes and the KK-equivalence
`C->Z` preserves every `K_1` clutching label.

## Phillips audit and scope

Phillips's circle-with-a-tail elements have the same global function `F`
but their circle restrictions are projection bundles with different
`K_1(D)` labels. Formula (UC12) distinguishes them even though the elements
are globally noncompact. This is why neither a global
`V disjointUnion Lsc_nc(X,S)` formula nor a decoration of only globally
compact elements can be correct.

The trigger is compact nonzero restriction to the cyclic core, not merely
full cyclic support: a soft element may have support equal to the whole
circle and still has no clutching label.

The proof stops at finite pseudoforests. A graph with two interacting cycles
can have several overlapping compact cyclic cores and compatibility between
their labels. No formula for that case is asserted here.

## Independent hostile audit

An independent audit checked:

- surjectivity of every leaf pullback against Antoine--Perera--Santiago,
  Theorem 3.3(i);
- order reflection without assuming old-base pointwise injectivity;
- naturality of restriction and evaluation;
- the full-corner identification `K_1(Her(p))=K_1(D)` and the singleton zero
  fiber;
- support-sensitive addition and the non-pointwise mixed order;
- iteration over all rooted trees attached to the unique circle; and
- the pure-pseudoforest first-factor map.

No counterexample was found. The audit rejected any naive support-cohomology decoration with coefficients
in `K_1(D)`, and any claim beyond pseudoforests.

## Primary sources checked

- Antoine--Dadarlat--Perera--Santiago,
  [Recovering the Elliott invariant from the Cuntz semigroup](https://arxiv.org/abs/1109.5803),
  especially Proposition 2.2, Remark 2.3, Theorems 2.6 and 3.7, and
  Remark 3.9.
- Antoine--Perera--Santiago,
  [Pullbacks, C(X)-algebras, and their Cuntz semigroup](https://arxiv.org/abs/1101.4776),
  especially Theorem 3.3 and the comparison-vector estimates.
- Brown--Ciuperca,
  [Isomorphism of Hilbert modules over stably finite C*-algebras](https://doi.org/10.1016/j.jfa.2008.12.004),
  for compact Cu classes and projective modules.
- Seth--Vilalta,
  [Continuous functions over a pure C*-algebra](https://arxiv.org/abs/2602.14809),
  for purity of the pseudoforest field.
