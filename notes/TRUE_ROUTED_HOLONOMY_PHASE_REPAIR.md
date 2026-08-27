# Forest phase repair and the routing-width gate

Date: 2026-08-11

## 1. Correct result and corrected scope

This note tests whether `cost(R)=1` closes the circle-cocycle gate in
`TRUE_HAAR_PHASE_KERNEL.md`.  The exact finite forest argument is positive,
but **cost one by itself does not supply the quantitative conclusion**.

The strongest valid result is a routed-holonomy criterion.  Roughly, a finite base
model may be cut to a forest and its phases repaired exactly whenever every
tested transformation has asymptotically trivial total fundamental-cycle
holonomy **and the chosen route already reproduces that transformation's
target phase**.  Requiring deleted-edge exposure to vanish is a convenient
but strictly stronger sufficient condition.  Its simplest numerical form is

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

Phase compatibility is equally load-bearing.  Any two vertices in one
finite component are joined by a forest path, so without it one could route
every permutation through an arbitrary spanning tree and make exposure
identically zero.  Products of approximate generator phases along such
unbounded paths need not approximate the cocycle value of the transformation
being tested.

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

### Exact fundamental-holonomy identity

Retain the forest and the functions `a,a'` from Lemma 1.  For an oriented
edge put

`d_F(e)=a'(e)^(-1)a(e) in T`.                          `(RFR5a)`

Thus `d_F(e)=1` on forest edges and
`d_F(reverse(e))=d_F(e)^(-1)`.  On a nonforest edge it is exactly the
holonomy of the corresponding fundamental cycle, up to the chosen
orientation.

> **Lemma 2 (path discrepancy is routed fundamental holonomy).**  For every
> oriented path `P=(e_1,...,e_l)`,
>
> `a(P)=a'(P) product_(j=1)^l d_F(e_j)`.               `(RFR5b)`

**Proof.**  The circle is abelian, so substitute `a(e)=a'(e)d_F(e)` into
the ordered path product and collect the factors.  End proof.

Define

`Hol_F(P)=product_(e in P) d_F(e)`.                    `(RFR5c)`

This identity is sharper than counting nonforest edges.  A path can cross
many chords while `Hol_F(P)=1`, either because their fundamental holonomies
are trivial or because they cancel.

## 3. Exact routed-holonomy criterion

For each `n`, let `G_n=(V_n,E_n)` be the finite graph underlying a base
model.  Choose a spanning forest `F_n` and put

`D_n=E_n minus F_n`.                                    `(RFR6)`

Let `T` be a finite collection of transformations to be tested.  Suppose
that, for each `t in T` and every `v` in its finite-model domain, a path

`P_(n,t,v)`                                             `(RFR7)`

in `G_n` represents the model value of `t` at `v`.  Define its forest
exposure by

`q_n(t)=|{v : P_(n,t,v) uses an edge of D_n}|/|V_n|`.   `(RFR8)`

Let `z_(n,t)(v)` be the quantized phase assigned to the tested transformation
itself, and let `a_n(P_(n,t,v))` be the ordered product of the quantized
generator-edge labels along the chosen path.  The routing is
**phase-compatible** when

`|V_n|^(-1) sum_v`
`  |a_n(P_(n,t,v))-z_(n,t)(v)|^2 -> 0`                 `(RFR8a)`

for every fixed `t` (with the sum restricted to its domain if it is partial).

There are now two possible forest hypotheses.  The sharp one is routed
holonomy decay:

`h_n(t)=|V_n|^(-1) sum_v`
`  |Hol_(F_n)(P_(n,t,v))-1|^2 -> 0`.                  `(RFR8b)`

The coarser exposure hypothesis `(RFR9)` implies `(RFR8b)`, since the
holonomy is exactly `1` on paths avoiding `D_n` and any two circle points
have squared chordal distance at most `4`.

> **Theorem 3A (routed-holonomy phase repair).**  Suppose the finite base
> models converge to a sofic pmp equivalence relation, their quantized
> finite-phase generator labels converge to a measurable circle cocycle,
> the selected paths satisfy phase compatibility `(RFR8a)`, and forests can
> be chosen so that `(RFR8b)` holds for every fixed tested transformation.
> Then the principal circle skew-product relation is sofic.

**Proof.**  Replace the edge table by the finite-phase coboundary from
Lemma 1.  Lemma 2 says that, along `P_(n,t,v)`, the ratio between the old and
new phase products is exactly `Hol_(F_n)(P_(n,t,v))`.  Condition `(RFR8b)`
therefore makes those products `L^2`-close.  Condition `(RFR8a)` compares
the old path product with the phase of the transformation being tested.
The new labels are a coboundary, so all path equalities lift exactly on
`V_n times mu_(m_n)`.  Uniform measure on the growing finite phase groups
converges to circle Haar measure.  The standard diagonal finite-colour
argument now gives the required skew-product models.  End proof.

> **Theorem 3 (routed forest phase repair).**  Suppose the finite base
> models converge to a sofic pmp equivalence relation, their quantized
> `mu_(m_n)`-valued generator-edge labels converge to a measurable circle
> cocycle, the selected paths satisfy phase compatibility `(RFR8a)`, and
> forests can be chosen so that
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

For a tested `t`, the repaired and original generator-edge phase products
agree whenever `P_(n,t,v)` stays in the forest.  The repaired phase therefore
differs from `a_n(P_(n,t,v))` only on a set of density at most `q_n(t)`, which
tends to zero by `(RFR9)`.  Phase compatibility `(RFR8a)` then compares this
path product with the phase `z_(n,t)(v)` which must be modelled.  Initial
circle quantization and base-model errors tend to zero separately.  Uniform
measure on `mu_(m_n)` converges to Haar measure on the circle, and circle
test partitions may be chosen with Haar-null boundary.  Thus all finite
labelled statistics of the lifted tests converge to those of the principal
skew product.  End proof.

The theorem uses both phase compatibility `(RFR8a)` and exposure `(RFR8)`,
not merely the cardinality of `D_n`.  These distinctions are precisely what
is lost in a bare cost estimate or arbitrary tree routing.

Equivalently, Theorem 3 is the immediate coarse corollary of Theorem 3A and
the bound

`h_n(t) <= 4 q_n(t)`.                                  `(RFR12a)`

Theorem 3A can succeed when `(RFR9)` fails, so routed holonomy rather than
raw exposure is the preferred next target.

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

This controls exposure.  Phase compatibility follows from the original
approximate cocycle equations if the accumulated phase error along the same
routes also tends to zero; for instance it is automatic for fixed words, and
follows for growing words from `L_n(t) delta_n -> 0` when `delta_n` uniformly
bounds the relevant per-step phase error.  For a fixed graphing and fixed
test words, `(RFR5)` implies `(RFR14)` and finite-step cocycle convergence
gives `(RFR8a)`.  The problem for an abstract cost-one relation is that both
the graphing and the representing words change as the graphing cost
approaches one.

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
Nor does it bound accumulated phase error along those routes, so it does not
imply `(RFR8a)`.

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
models have vanishing routed fundamental holonomy `(RFR8b)`.  Therefore:

> **Corollary 5.**  A hyperlinear group satisfying the bounded-exponent
> common-Cartan hypotheses of Theorem 3H is sofic if its principal quotient
> relation admits finite models, routes, and forests satisfying `(RFR8a)`
> and `(RFR8b)`.  Vanishing exposure `(RFR9)`, with `(RFR14)` as a convenient
> numerical sufficient estimate, is one way to force `(RFR8b)`.

The previously proved treeable case uses a different cohomological argument;
positive-cost treeings need not have vanishing tree excess in finite models.
Følner models do satisfy the present criterion through their controlled
routing.  The new formulation isolates a possible intermediate class:
relations whose relevant tests admit low-congestion routing through
near-forest sofic models even when no fixed treeing or Følner exhaustion is
available.

For the general problem, the live quantitative question is now:

> Can the normal `0/1` trace law or the simultaneous prefix-path structure
> select routes satisfying phase compatibility `(RFR8a)` whose total
> fundamental-cycle holonomy vanishes in the sense of `(RFR8b)`?

This is more precise than asking for cost one, strictly weaker than
vanishing deleted-edge exposure, and weaker than requiring the entire
graphing model to be cocycle stable.  It asks only for the cycle errors seen
by the finite family of transformations whose statistics are currently
being tested.

## 7. Source audit

The forest lemma, fundamental-holonomy identity, and routed repair estimates
are proved above.  The
background notions are the graphing definition of cost and the
finite-coloured-model definition of a sofic equivalence relation:

* D. Gaboriau, *What is Cost?*, arXiv:1011.2294.
* G. Elek and G. Lippner, *Sofic equivalence relations*, arXiv:0906.3619.
* L. Paunescu, *On Sofic Actions and Equivalence Relations*,
  arXiv:1002.0605.

A targeted search did not locate a stated phase-repair theorem in this
routed-holonomy form.  The unconditional cost-one claim should not be cited;
the valid conclusions are Lemmas 1--2, Theorem 3A, Theorem 3, and their
explicitly quantitative corollaries.
