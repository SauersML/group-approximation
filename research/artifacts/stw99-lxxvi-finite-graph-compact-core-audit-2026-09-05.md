# Finite graphs: compact cycle cores and first-factor Cu regularity

## The theorem

Let `D` and `E` be simple separable stably finite C*-algebras of stable
rank one. Let `phi:D -> E` be a *-homomorphism such that both `Cu(phi)`
and `K_1(phi)` are isomorphisms. For every finite graph `X`,

```text
Cu(C(X,phi)): Cu(C(X,D)) -> Cu(C(X,E))
```

is an isomorphism. In particular, if `D` is simple, separable, stably finite,
and pure, then `C(X,D)` is pure and its actual first-factor map into
`C(X,D) tensor Z` induces a Cu isomorphism, for every finite graph `X`.
Theta graphs and arbitrary 2-connected multicycle blocks are included.

The proof has three logically separate stages: identify equivalence classes,
prove bijectivity of the induced map as a set map, and only then reflect
order. A bijective Cu morphism is not simply assumed to reflect order.

## Prior art and the scope of the extension

Tikuisis, *The Cuntz semigroup of continuous functions into certain simple
C*-algebras*, Theorem 1.1, already computes continuous-function Cu using
pointwise values and projection data on compact subsets of compact-value
level sets, for simple unital Z-stable ASH coefficients and arbitrary
second-countable locally compact bases. Retaining compact restriction
data is an established method. The extension proved here is its finite-graph
implementation for arbitrary simple separable stably finite stable-rank-one
coefficients, together with rigidity of the actual map whenever coefficient
Cu and K1 maps are isomorphisms. No ASH, nuclearity, or coefficient
Z-absorption assumption is used. Novelty beyond this precise extension is
not claimed merely from the use of compact restriction data.

## Inputs and their precise uses

Write `B=D tensor K`. The published interval theorem of
Antoine--Dadarlat--Perera--Santiago (ADPS), Theorem 2.6, supplies the
pointwise interval Cu formula. Their circle theorem, Theorem 3.7, implies
that a circle restriction is a nonzero compact class exactly when its
pointwise Cu function is a nonzero constant compact value. Their Lemma 3.1
allows an alignment unitary's K1 class to be changed at small action cost
when the comparison vector has a small positive spectral value.

Brown--Ciuperca, Theorem 3.5, explicitly equates compactness of the Cu
class of a positive element `a` in a stable finite algebra with
`spectrum(a) subset {0} union [epsilon,infinity)` for some `epsilon>0`.
We apply it to `C(C,D) tensor K` for a circle `C`, or another finite graph
restriction. These algebras are stably finite: their unitizations embed in
continuous functions with values in the stably finite coefficient
unitization, and finiteness of matrix projections is checked pointwise.
Stable rank one of the **circle algebra** is not assumed. Conversely, a
spectral gap gives a support projection by continuous functional calculus.

The previously audited one-point wedge theorem is used only for gluing
graphs along articulation points; it is not used for gluing two prescribed
endpoints or to assert a multicycle Cu pullback. Its general block-cut
reduction and the interval formula give comparison on a graph made of
specified core graphs joined by bridge edges.

The finite-graph projection-clutching theorem is used only for compact
classes. Its proof applies to the present `phi`: `Cu(phi)` identifies fiber
projection classes and `K_1(phi)` identifies all cycle coordinates. No
noncompact conclusion is imported from that theorem.

## A quantitative surgery lemma

Let `a,b` be positive contractions in `C(X,B)`. Fix a small number `rho>0`.
Choose finitely many distinct interior edge points `s_1,...,s_m`. At each
point require either `a(s_i)=0`, or choose

```text
lambda_i in spectrum(a(s_i)),       0 < lambda_i < rho^2.
```

Let `q:Y -> X` open each selected point into two endpoints. Suppose
`q^*a` is Cuntz below `q^*b`. Then there is a comparison vector downstairs
whose source square differs from `a` by a quantity tending to zero with
`rho` and the chosen local comparison tolerance. The number of cuts can
be bounded by the first Betti number, and the estimate is a supremum
estimate on disjoint collars, not an accumulating sum.

Here are all of the gluing details. Choose `delta>0` only after the finite
list of positive `lambda_i`, with `delta<min_i lambda_i` and `delta` tending
to zero with the desired error. Comparison upstairs gives a vector `y`
such that

```text
y^*y=(q^*a-delta)_+,         yy^* in Her(q^*b).
```

At each `s_i`, pointwise comparison gives a local downstairs vector of the
form `b(t)^(1/2)d_i`, with constant `d_i`, whose source square approximates
`a` on a sufficiently small neighborhood. Use the same local field on both
paired collars. Stable rank one of `Her(b(s_i))` gives a unitary aligning
`y` at each endpoint with this local vector, to an error tending to zero
with the local source-square error. At a nonzero selected fiber,
`lambda_i-delta` is in the nonzero spectrum of `y(e)y(e)^*`. ADPS Lemma 3.1
changes the alignment unitary to K1 class zero, at action cost less than
`5 rho`. At a zero selected fiber, `y(e)=0`, and the local field can be
chosen zero, so the alignment unitary is the identity.

There is one simultaneous lift of all of these adjusted endpoint unitaries.
To see this without a nowhere-zero hypothesis on `b`, put `H=Her(q^*b)`
and `L=H+C(Y)1`, inside `C(Y,B~)`. Evaluation onto the finite endpoint set
is a surjective *-homomorphism

```text
L -> direct_sum_e Her(b(q(e)))~.
```

The restriction of a hereditary algebra under a quotient is the hereditary
algebra of the image; surjectivity at finitely many distinct points follows
also directly by multiplying lifts by scalar functions with disjoint
supports. The scalar summand `C(Y)1` permits distinct endpoint scalar
quotients. Stable rank one identifies the kernel of the K1 component map
with the identity component in each fiber unitization. A finite tuple of
identity-component unitaries lifts to an identity-component unitary in
`L`: express the tuple as a finite product of exponentials of selfadjoint
elements and lift these selfadjoints. This preserves each prescribed
alignment unitary exactly. Target support zeros cause no obstruction.

Multiply `y` by this simultaneous lift. On sufficiently small pairwise
disjoint collars, it is close to the selected local fields. A scalar
partition of unity now splices it to those fields. The resulting vector
`z` has exactly equal values at paired endpoints and source square close
to `q^*a`. For contractions, if the two fields differ in norm by `eta`, the
source-square error introduced by the splice is at most
`eta (2 sqrt(1+delta)+eta)` in addition to the initial comparison error.
Let the local error and `rho` go to zero.

Both fields lie in the closed right ideal generated by `q^*b`, so does
their splice. The descended vector `c` lies in the right ideal generated
by `b`: since `q^*(b^(1/n)c) -> q^*c` and `q^*` is isometric, one has
`b^(1/n)c -> c`. Thus `cc^*` belongs to `Her(b)`. This proves downstairs
comparison in the limit. The graph `Y` and the cuts may depend on `rho`.

## The compact cycle core

There are finitely many embedded simple circles in a finite graph (up to
their images). For `a`, let `K(a)` be the union of those circles `C` for
which `[a|C]` is nonzero compact. The core can be empty. It is a finite
subgraph. On every connected component of `K(a)`, the element `a` is
nonzero and has a uniform spectral gap: take the minimum of the positive
spectral gaps on the finitely many constituent circles. Consequently
`[a|K_j]` is compact for each core component `K_j`.

The circle theorem shows that `K(a)` depends only on the pointwise Cu
function `F_a(x)=[a(x)]`, not on hidden clutching choices. We can therefore
write `K(F_a)`. Within a connected core component, `F_a` is one constant
nonzero compact value, since intersecting circles agree at their common
vertices.

For any `rho>0`, one can choose at most `b_1(X)` cuts outside `K(a)` such
that the opened graph has no simple circle outside the core. Start with a
circle not contained in the core. Its restriction of `a` is either zero or
noncompact. In the zero case cut at an interior point outside the core.
In the noncompact case choose a positive spectral value less than `rho^2`
and less than the uniform positive spectral gap on the core. Such values
exist because otherwise the whole circle restriction would have a spectral
gap and be compact. The selected point is outside the core. It can be
chosen in an edge interior: a small positive spectral value persists, within
a slightly larger interval in `(0,rho^2)`, at nearby points by norm
continuity. Cut at this point. Each cut opens an edge on a cycle and lowers
the first Betti number by one without disconnecting that component. Repeat.

After these cuts, contraction of each core component gives a forest. If
the quotient contained a cycle, a path through the contracted core pieces
would produce a simple circle of the original opened graph with an edge
outside the core. This contradicts the stopping condition. Therefore the
opened graph is assembled from the actual core components and intervals
by one-point wedge gluing. No graph homotopy invariance of Cu is asserted.

## Exact equivalence criterion

For positive `a,b` in `C(X,B)`, the following are equivalent:

```text
(i)  [a]=[b] in Cu(C(X,D));
(ii) F_a=F_b, and [a|K_j]=[b|K_j] on every connected
     component K_j of their common compact cycle core K(F_a).
```

Necessity follows by restriction. For sufficiency, choose cuts using `a`
as above. On the opened graph, restrictions to every core component agree
by assumption; restrictions to every bridge interval agree by the interval
formula. The one-point wedge theorem gives `q^*a ~ q^*b`. The surgery lemma
then gives `a` Cuntz below `b`. Repeat with cuts chosen using `b` to obtain
the reverse comparison. This proves the criterion. In particular it does
not assign one independent label to each circle of a theta graph: all
compact circles in a connected core are represented by one actual
projection class on that entire core.

## Realization of the equivalence data

Let `F:X -> Cu(D)` be lower semicontinuous. Put `K=K(F)`, defined using
the circle condition that `F|C` be a nonzero constant compact value.
For each component `K_j`, choose a projection-module class over `C(K_j,D)`
whose pointwise fiber class is the value of `F` there. All such classes
exist by finite-graph projection clutching. Then these core classes and `F`
are simultaneously realized by a countably generated Hilbert module over
`C(X,D)`.

There is a direct published realization theorem for exactly this step.
Start with the disjoint union of the core components and the remaining
vertices, and attach the remaining edges one at a time. Each attachment
is the C*-pullback of the existing section algebra and `C([0,1],D)` over
`D direct_sum D`; the map out of the interval algebra is endpoint
evaluation and is surjective. ADPS Theorem 2.6 makes point evaluation on
this interval algebra an order embedding. Thus APS Theorem 3.3(i) applies
and makes the induced Cu pullback map surjective. The prescribed old
class and the interval class realizing `F` have matching endpoint Cu
values, so they lift to a class on the enlarged graph. Iterate finitely.
This use of APS Theorem 3.3(i) needs no vanishing-K1 hypothesis and asserts
surjectivity only, not the unavailable order embedding of a general
two-endpoint pullback.

The same realization can be seen directly in the Hilbert-module picture;
the details below clarify which equality is actually used at endpoints.
Subdivide at the finitely many core vertices. On each remaining closed
edge choose an interval Hilbert module realizing `F` by the interval
theorem. Choose a fiber module at every remaining vertex. At each incidence,
the two endpoint modules have the same Cu class over `D`, hence are
isomorphic by the stable-rank-one Hilbert-module theorem. Fix such
isomorphisms independently and take the Hilbert module of tuples of edge
and core sections whose endpoint values match under those isomorphisms.

For completeness, this finite module pullback has exactly the required
restrictions. Evaluation of a Hilbert module onto its endpoint fiber is a
surjective quotient map. A section on one piece can be extended to matching
endpoint values on each adjacent piece by that surjectivity, using scalar
cutoff functions near distinct endpoints to prescribe all endpoints at once.
Thus the coordinate projection of the pullback module onto any piece is
surjective. Its kernel is the submodule generated by scalar functions
vanishing on that piece; this follows by cutoff approximation. Hence
restriction is the chosen module. The pullback is a closed subspace of a
finite direct sum of separable Banach modules, so is separable. A countable
dense set generates it as a Hilbert module, using the approximate identity
of the coefficient algebra. It therefore represents an element of Cu.

This construction proves realization only. It does not claim that arbitrary
finite endpoint Cu pullbacks reflect order. Independence of the gluing
choices is asserted only to the extent given by the proved equivalence
criterion, which retains all core projection data.

## Set bijectivity for the coefficient map

The coefficient Cu isomorphism carries `F` bijectively and naturally to
the target pointwise data and preserves compactness. Thus source and target
have exactly the same compact cycle core. On each core component, finite
graph projection clutching makes the actual map on compact classes
bijective, because both `V(phi)` and `K_1(phi)` are isomorphisms.

Given any target class, lift its pointwise data and its compact projection
class on each core component, then apply the realization construction. Its
image has precisely the original equivalence data, so the equivalence
criterion proves surjectivity. If two source classes have the same image,
their pointwise data agree, and injectivity of the compact map on every
core component makes their core classes agree. The same criterion proves
injectivity. This stage proves set bijectivity for **every** finite graph;
it has not used order reflection of the global coefficient map.

## Recovering order without circularity

First observe a general consequence of set bijectivity just proved. On any
finite graph `W`, let `p` be a compact source class and suppose

```text
Cu(C(W,phi))(p) <= Cu(C(W,phi))(x).
```

The almost algebraic order axiom `(O5)` for the target Cu semigroup, applied
with the compact element equal to its own way-below approximation, gives
a target class `z` with

```text
Cu(C(W,phi))(x) = Cu(C(W,phi))(p) + z.
```

Lift `z` by the already-proved set surjectivity; set injectivity then gives
`x=p+z'`. Thus the map reflects every comparison with compact left side.
Equivalently, this is the usual splitting of a projection submodule from a
Hilbert module; it requires no cancellation hypothesis.

Now assume `Cu(C(X,phi))([a]) <= Cu(C(X,phi))([b])`. Choose the compact
cycle core and the soft cuts using `a`. On each core component the left
restriction is compact, so the preceding paragraph reflects comparison
there. On each bridge interval comparison reflects by the coefficient Cu
isomorphism and the interval formula. The articulation theorem therefore
gives `q^*a` Cuntz below `q^*b`. Apply the surgery lemma and let the errors
decrease to zero. This reflects the original comparison.

We have now proved an order isomorphism which is already a Cu morphism.
Its inverse preserves increasing suprema by order, and preserves `<<` by
the order definition of compact containment. It is therefore a Cu
isomorphism. This completes the theorem.

## Consequence for STW LXXVI and limitations

For a simple separable stably finite pure `D`, the simple-case theorem and
Lin's stable-rank-one theorem give the coefficient first-factor Cu
isomorphism and stable rank one for both coefficients. The scalar inclusion
into `Z` gives the first-factor K1 isomorphism. Seth--Vilalta's
continuous-function purity theorem separately makes `C(X,D)` pure.
The theorem above therefore closes the entire finite-graph corridor,
including the previously unresolved theta and 2-connected multicycle cases.

This does not solve STW Problem LXXVI for arbitrary pure C*-algebras.
The classification proof uses a finite set of graph cycles, simple
stable-rank-one coefficients, and finite endpoint gluing. A separate
inverse-limit argument extends Cu regularity, though not this finite-core
classification formula, to second-countable locally compact bases of
dimension at most one; see
`stw99-lxxvi-one-dimensional-simple-fiber-cu-regularity`. No conclusion is
asserted here for higher-dimensional spaces or general nonsimple pure
coefficients.

## Primary references

- Tikuisis,
  [The Cuntz semigroup of continuous functions into certain simple C*-algebras](https://arxiv.org/abs/1007.2927),
  Theorem 1.1, for the preceding compact-level-set method under Z-stable
  ASH coefficient hypotheses.
- Antoine--Dadarlat--Perera--Santiago,
  [Recovering the Elliott invariant from the Cuntz semigroup](https://arxiv.org/abs/1109.5803),
  Theorem 2.6, Lemma 3.1, Theorem 3.7.
- Antoine--Perera--Santiago,
  [Pullbacks, C(X)-algebras, and their Cuntz semigroup](https://arxiv.org/abs/1101.4776),
  Proposition 1.1 and Lemma 1.4 for comparison vectors and alignment.
- Brown--Ciuperca,
  [Isomorphism of Hilbert modules over stably finite C*-algebras](https://arxiv.org/abs/0811.0958),
  for compact Cu classes and projective modules.
- Coward--Elliott--Ivanescu,
  [The Cuntz semigroup as an invariant for C*-algebras](https://doi.org/10.1016/j.jreineangew.2007.10.008),
  for the stable-rank-one module isomorphism theorem.
- Seth--Vilalta,
  [Continuous functions over a pure C*-algebra](https://arxiv.org/abs/2602.14809),
  for the pure-fiber corollary's purity assertion.
