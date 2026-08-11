# Cost-one sofic relations admit finite circle-phase repair

Date: 2026-08-11

## 1. Result and scope

The circle-cocycle gate in `TRUE_HAAR_PHASE_KERNEL.md` has a positive
solution whenever the already-sofic base relation has cost one.

> **Theorem (cost-one circle-skew permanence).**  Let `R` be an aperiodic
> pmp countable equivalence relation.  Assume that `R` is sofic and
> `cost(R)=1`.  If
>
> `alpha:R -> T`
>
> is a measurable circle-valued cocycle, then its principal skew-product
> relation `R(alpha)` on `X times T`, with relatively Haar measure, is sofic.

The proof is a direct finite-model argument.  It does not assert an analogous
statement for arbitrary compact structure groups, it does not assert that every
action of a sofic group is sofic, and it does not assume a general
compact-extension permanence theorem.  The soficity of the *particular base
relation* is a hypothesis.

This theorem enlarges the treeable and hyperfinite cases already recorded in
the Haar-phase note.  It does not prove that every hyperlinear group is sofic:
the quotient relation produced by an arbitrary hypothetical common-Cartan
model need not have cost one, and construction of a common Cartan from an
arbitrary hyperlinear table remains a separate gate.

## 2. The finite forest-repair lemma

Let `G=(V,E)` be a finite undirected multigraph.  Loops and parallel edges
are allowed.  Give every oriented edge `e` a label `a(e)` in a group `K`, with

`a(reverse(e))=a(e)^(-1)`.                              `(CFR1)`

Write `c(G)` for the number of connected components, including isolated
vertices.

> **Lemma 1 (forest phase repair).**  There is a vertex function
> `b:V -> K` such that the coboundary labelling
>
> `a'(e)=b(target(e)) b(source(e))^(-1)`                `(CFR2)`
>
> agrees with `a(e)` on all but at most
>
> `|E|-|V|+c(G)`                                       `(CFR3)`
>
> unoriented edges.  If `K=mu_m`, then `b` and `a'` also take values in
> `mu_m`.

**Proof.**  Choose a spanning tree in each nontrivial component and one root
per component.  Put `b(root)=1`.  Recursively across each oriented tree edge
`e=(v,w)`, set `b(w)=a(e)b(v)`.  The unique-path property makes this
well-defined, and `(CFR2)` equals `a(e)` on every forest edge.  A spanning
forest has `|V|-c(G)` edges, so exactly `(CFR3)` edges remain.  Products and
inverses preserve `mu_m`.  End proof.

No small-curvature assumption occurs here.  The only obstruction is the
cycle excess of the finite graph.

> **Corollary 2 (vanishing tree excess).**  Suppose `G_n=(V_n,E_n)` are
> finite graphs such that
>
> `|E_n|/|V_n| -> 1`,  `c(G_n)/|V_n| -> 0`.            `(CFR4)`
>
> Then every sequence of group-valued edge labellings is `o(|V_n|)`-close
> in Hamming edge measure to a coboundary labelling.  For circle labels, one
> may first approximate the finitely many labels in each model by roots of
> unity and obtain a finite-phase coboundary.

This is stronger than qualitative cocycle stability on this particular
sequence: it repairs arbitrary curvature after changing only the cycle-excess
edges.

## 3. Sparse models supplied by cost one

Fix a finite test in the skew relation and a tolerance `epsilon>0`.  Choose a
countable graphing `Phi=(phi_i)` generating `R` with

`sum_i mu(dom(phi_i)) < 1+epsilon`.                    `(CFR5)`

This is the definition of `cost(R)=1`, using the standard normalization in
which one partial isomorphism contributes the measure of its domain.

Only finitely many graphing letters are needed to approximate the fixed test
by words.  Enlarge this finite family further so that, outside a set of
measure at most `epsilon`, its connected components have more than
`M` vertices.  This is possible because the increasing union of the finite
subgraphings generates the aperiodic relation: for almost every `x`, the
size of its finite-subgraphing component increases to the infinite size of
`[x]_R`.

Partition the domains of these finitely many graphing letters so that every
edge value

`alpha(phi_i(x),x)`                                    `(CFR6)`

is, outside measure `epsilon`, within `epsilon` of a constant root of unity
on each partition cell.  One common group `mu_m` suffices for the finite
partition.  Include these cells as finite colours in a sofic model of `R`.

Let `G_n=(V_n,E_n)` be the resulting finite coloured graph.  Soficity and
`(CFR5)` give, for sufficiently accurate models,

`|E_n| <= (1+2 epsilon)|V_n|`.                         `(CFR7)`

The chosen component-size statistic gives

`|{v: |component(v)| <= M}| <= 2 epsilon |V_n|`.       `(CFR8)`

Every component of size greater than `M` accounts for more than `M`
vertices, while the number of small components is at most the number of
vertices in them.  Hence

`c(G_n)/|V_n| <= 2 epsilon + 1/M`.                     `(CFR9)`

Lemma 1 therefore changes at most

`(4 epsilon+1/M)|V_n|`                                `(CFR10)`

edge labels, up to the vanishing finite-model errors.  Call the resulting
`mu_m`-valued coboundary label `a'_n`.

## 4. Lift to a genuine finite permutation bundle

Let a model edge for `phi_i` run from `v` to `sigma_i(v)`.  On

`Omega_n=V_n times mu_m`

define the lifted partial permutation

`hat(sigma_i)(v,u)`
`  =(sigma_i(v),a'_n(v,sigma_i(v))u)`.                 `(CFR11)`

Because `a'_n` is the vertex coboundary `(CFR2)`, its product along *every*
finite path from `v` to `w` is

`b_n(w)b_n(v)^(-1)`.                                  `(CFR12)`

Consequently every equality between base paths in the finite model lifts to
an exact equality on `Omega_n`.  There is no circle carry and no shrinking
root-spacing problem.  The uniform measure on `mu_m` converges to Haar
measure on `T` as `m` increases.

For a word of length at most `L`, the corrected and original quantized phase
products can differ only if the path crosses a changed edge.  By a union
bound and `(CFR10)`, this affects at most

`L(4 epsilon+1/M)+o(1)`                               `(CFR13)`

of the starting vertices.  The initial phase quantization and the base
sofic-model error contribute another quantity tending to zero.  Circle
partitions may be chosen with Haar-null boundaries, so convergence of the
finite labelled statistics follows.

First take the finite model size to infinity, then `M` and `m` to infinity,
and finally `epsilon` to zero.  A diagonal sequence models every finite test
in `R(alpha)`.  This proves the theorem.

## 5. Consequence for the Haar phase kernel

In the bounded-exponent common-Cartan setup of Theorem 3H in
`TRUE_HAAR_PHASE_KERNEL.md`, slow tensor amplification makes the quotient
relation `R_Q` principal.  If in addition

`cost(R_Q)=1`,                                         `(CFR14)`

then the theorem above makes the circle skew product `R_Q(lambda)` sofic.
Theorem 3H then gives:

> **Corollary 3.**  A hyperlinear group satisfying the bounded-exponent
> common-Cartan hypotheses of Theorem 3H is sofic whenever its principal
> quotient relation is sofic of cost one.

This removes the Bockstein, uncountable-range, and finite-phase stability
obstructions simultaneously in the cost-one case: sparse graphings let one
discard all global holonomy edges at vanishing density.

The remaining general case has positive tree excess.  If a finite graphing
model has asymptotic edge density `c>1`, the same argument changes at most

`(c-1+o(1))|V_n|`                                     `(CFR15)`

edges, which is not negligible.  Thus the proof identifies the exact place
where cost one is used and does not smuggle in a Følner assumption.

## 6. Source and novelty audit

The only external inputs are the standard graphing definition of cost and
the finite-coloured-model definition of a sofic equivalence relation.  The
forest estimate and the skew-bundle construction are proved above.

Relevant background:

* D. Gaboriau, *What is Cost?*, arXiv:1011.2294.
* G. Elek and G. Lippner, *Sofic equivalence relations*, arXiv:0906.3619.
* L. Paunescu, *On Sofic Actions and Equivalence Relations*,
  arXiv:1002.0605.

A targeted search did not locate a stated compact-skew permanence theorem
under exactly the hypotheses above.  Until independently checked against a
fully fixed formal definition of sofic groupoids, it should be cited as the
finite-model theorem proved in this note, rather than attributed to those
papers.
