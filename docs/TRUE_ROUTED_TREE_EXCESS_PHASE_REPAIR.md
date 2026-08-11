# Forest phase repair and the routing-width gate

Date: 2026-08-11

## 1. Correct result and corrected scope

This note tests whether `cost(R)=1` closes the circle-cocycle gate in
`TRUE_HAAR_PHASE_KERNEL.md`.  The exact finite forest argument is positive,
but **cost one by itself does not supply the quantitative conclusion**.

The valid result is a routed-tree-excess criterion.  Roughly, a finite base
model may be cut to a forest and its phases repaired exactly whenever every
tested transformation crosses the deleted edges on only `o(1)` of its
starting points.  A convenient sufficient condition is

`routing width times normalized tree excess -> 0`.       `(RFR1)`

For a cost-one relation the normalized tree excess can be made arbitrarily
small, but the word length needed to express a fixed external test in that
near-minimal graphing may diverge faster than its reciprocal.  No theorem
currently controls this product.  Thus the earlier unconditional
``cost-one compact-skew permanence'' claim was invalid and is withdrawn.

The correction is load-bearing.  If cost one alone sufficed, one could take
the product of an arbitrary sofic relation with an aperiodic hyperfinite
relation (a cost-one stabilization), apply phase repair there, and try to
pass to a subrelation.  That would prove the general compact-skew permanence
which is precisely open.  The missing routing bound is where this false
shortcut pays back the apparent cost reduction.

## 2. The exact finite forest-repair lemma

Let `G=(V,E)` be a finite undirected multigraph.  Loops and parallel edges
are allowed.  Give every oriented edge `e` a label `a(e)` in a group `K`, with

`a(reverse(e))=a(e)^(-1)`.                              `(RFR2)`

Write `c(G)` for the number of connected components, including isolated
vertices.

> **Lemma 1 (forest phase repair).**  There is a vertex function
> `b:V -> K` such that the coboundary labelling
>
> `a'(e)=b(target(e)) b(source(e))^(-1)`                `(RFR3)`
>
> agrees with `a(e)` on all but at most
>
> `r(G)=|E|-|V|+c(G)`                                  `(RFR4)`
>
> unoriented edges.  If `K=mu_m`, then `b` and `a'` also take values in
> `mu_m`.

**Proof.**  Choose a spanning tree in each nontrivial component and one root
per component.  Put `b(root)=1`.  Recursively across each oriented tree edge
`e=(v,w)`, set `b(w)=a(e)b(v)`.  The unique-path property makes this
well-defined, and `(RFR3)` equals `a(e)` on every forest edge.  A spanning
forest has `|V|-c(G)` edges, leaving exactly `(RFR4)` edges.  Products and
inverses preserve `mu_m`.  End proof.

No small-curvature assumption occurs here.  The only obstruction to
repairing an *arbitrary* edge table is the tree excess `r(G)`.

> **Corollary 2 (vanishing tree excess for the generator table).**  If
>
> `r(G_n)/|V_n| -> 0`,                                  `(RFR5)`
>
> then every sequence of group-valued generator-edge labellings is
> `o(|V_n|)`-close in edge Hamming measure to a coboundary labelling.  For
> circle labels, first approximate the finitely many labels in each model by
> roots of unity; the repaired coboundary is then finite-phase.

This corollary concerns the chosen generator edges.  Passing from them to
external transformations represented by long paths is a separate step.

## 3. Exact routed-tree-excess criterion

For each `n`, let `G_n=(V_n,E_n)` be the finite graph underlying a base
model.  Choose a spanning forest `F_n` and put

`D_n=E_n minus F_n`.                                    `(RFR6)`

Let `T` be a finite collection of transformations to be tested.  Suppose
that, for each `t in T` and every `v` in its finite-model domain, a path

`P_(n,t,v)`                                             `(RFR7)`

in `G_n` represents the model value of `t` at `v`.  Define its forest
exposure by

`q_n(t)=|{v : P_(n,t,v) uses an edge of D_n}|/|V_n|`.   `(RFR8)`

> **Theorem 3 (routed forest phase repair).**  Suppose the finite base
> models converge to a sofic pmp equivalence relation, their quantized
> `mu_(m_n)`-valued generator-edge labels converge to a measurable circle
> cocycle, and forests can be chosen so that
>
> `q_n(t) -> 0` for every fixed tested transformation `t`. `(RFR9)`
>
> Then replacing the labels by the forest coboundaries from Lemma 1 gives
> finite permutation-bundle models of the principal circle skew product.
> In particular, if one exhaustion of finite tests satisfies `(RFR9)`, the
> skew-product relation is sofic.

**Proof.**  Apply Lemma 1 and write the repaired label as

`a'_n(e)=b_n(target(e))b_n(source(e))^(-1)`.            `(RFR10)`

On

`Omega_n=V_n times mu_(m_n)`

lift a model generator edge `v -> sigma_i(v)` by

`(v,u) -> (sigma_i(v),a'_n(v,sigma_i(v))u)`.            `(RFR11)`

The product of `(RFR10)` along every path from `v` to `w` telescopes to

`b_n(w)b_n(v)^(-1)`.                                   `(RFR12)`

Hence every equality between base paths lifts to an exact equality on the
finite phase bundle.  There is no circle carry and no shrinking
root-spacing problem.

For a tested `t`, the repaired and original quantized phase products agree
whenever `P_(n,t,v)` stays in the forest.  Their disagreement set therefore
has density at most `q_n(t)`, which tends to zero by `(RFR9)`.  Initial
circle quantization and base-model errors tend to zero separately.  Uniform
measure on `mu_(m_n)` converges to Haar measure on the circle, and circle
test partitions may be chosen with Haar-null boundary.  Thus all finite
labelled statistics of the lifted tests converge to those of the principal
skew product.  End proof.

The theorem uses exposure `(RFR8)`, not merely the cardinality of `D_n`.
This distinction is precisely what is lost in a bare cost estimate.

## 4. A convenient word-length sufficient condition

Suppose a tested transformation `t` is represented by a word of length at
most `L_n(t)` in partial-bijection generators.  At each fixed step, the map
from starting vertices to the currently traversed oriented generator edge
is injective on its domain.  Therefore a union bound gives

`q_n(t) <= L_n(t)|D_n|/|V_n|`.                         `(RFR13)`

Consequently:

> **Corollary 4 (width times excess).**  The conclusion of Theorem 3 holds
> if, for every fixed test `t`,
>
> `L_n(t) r(G_n)/|V_n| -> 0`.                          `(RFR14)`

For a fixed graphing and fixed test words, `(RFR5)` implies `(RFR14)`.  The
problem for an abstract cost-one relation is that both the graphing and the
representing words change as the graphing cost approaches one.

## 5. Why cost one alone does not prove the criterion

Let `R` be aperiodic with `cost(R)=1`.  For every `epsilon>0` there is a
generating graphing `Phi_epsilon` with

`cost(Phi_epsilon)<1+epsilon`.                         `(RFR15)`

A sufficiently accurate finite model of a large finite subgraphing has

`r(G_n)/|V_n| <= O(epsilon)+o_n(1)`,                   `(RFR16)`

because its edge density is at most `1+epsilon` and its component density
can be made small by aperiodicity.  This part of the original cost-one
argument is correct.

Now fix an external finite test `T`.  Let `L_epsilon(T)` be the largest word
length used to approximate its members in `Phi_epsilon`.  The forest proof
only yields the error estimate

`O(L_epsilon(T) epsilon)`.                             `(RFR17)`

The definition of cost supplies no bound on `L_epsilon(T)`.  In particular,
it does not imply

`inf_(epsilon -> 0) L_epsilon(T)epsilon=0`.            `(RFR18)`

Thus `(RFR15)` does not imply `(RFR9)` or `(RFR14)`.

The same loss appears under finite amplification.  The standard graphing of
an `m`-fold amplification places one copy of the horizontal `R`-edges over
roughly `m` vertical copies, reducing normalized cost excess by `1/m`.
However, the transformation on each of the `m` slices routes through those
same horizontal edges.  A deleted horizontal edge is therefore reused by
`m` starting fibers.  The global edge saving `1/m` is cancelled by routing
multiplicity `m`; after returning to a slice there is no improved Hamming
error.  Infinite hyperfinite stabilization has the same accounting issue.

This explains why the product-with-a-hyperfinite-relation shortcut cannot be
used to deduce arbitrary compact-skew permanence from the forest lemma.

## 6. Consequence for the Haar phase program

In the principal quotient-relation endpoint of Theorem 3H in
`TRUE_HAAR_PHASE_KERNEL.md`, the circle phase gate closes whenever its sofic
models have vanishing routed tree excess `(RFR9)`.  Therefore:

> **Corollary 5.**  A hyperlinear group satisfying the bounded-exponent
> common-Cartan hypotheses of Theorem 3H is sofic if its principal quotient
> relation admits phase-compatible finite models satisfying `(RFR9)` (or the
> sufficient estimate `(RFR14)`).

The previously proved treeable case uses a different cohomological argument;
positive-cost treeings need not have vanishing tree excess in finite models.
Følner models do satisfy the present criterion through their controlled
routing.  The new formulation isolates a possible intermediate class:
relations whose relevant tests admit low-congestion routing through
near-forest sofic models even when no fixed treeing or Følner exhaustion is
available.

For the general problem, the live quantitative question is now:

> Can the normal `0/1` trace law or the simultaneous prefix-path structure
> select phase-compatible base models for which the deleted cycle edges have
> vanishing exposure `(RFR9)`?

This is more precise than asking for cost one and weaker than requiring the
entire graphing model to be cocycle stable.

## 7. Source audit

The forest lemma and routed exposure estimate are proved above.  The
background notions are the graphing definition of cost and the
finite-coloured-model definition of a sofic equivalence relation:

* D. Gaboriau, *What is Cost?*, arXiv:1011.2294.
* G. Elek and G. Lippner, *Sofic equivalence relations*, arXiv:0906.3619.
* L. Paunescu, *On Sofic Actions and Equivalence Relations*,
  arXiv:1002.0605.

A targeted search did not locate a stated phase-repair theorem in this
routed-tree-excess form.  The unconditional cost-one claim should not be
cited; the valid conclusions are Lemma 1, Theorem 3, and their explicitly
quantitative corollaries.
