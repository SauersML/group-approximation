# All quotient radicals and arbitrary monotone rules inside LEF Kazhdan groups

2026-09-13. Written proof, not Lean-verified.

Use the [directed-seam construction](pestov91-directed-seams-and-normal-lattices-2026-09-13.md).
For a finite directed graph `D=(V,E)`, the three-torsion-generated
Kazhdan group `G_D` has simple locally finite edge kernels `L_e` and
simple Kazhdan LEF endpoint factors `Q_v`. Its normal subgroups are
`N(J,S)`, where `J subset E`, `S subset V`, and every edge incident
to `S` lies in `J`. Matrix rank and binary coding are held fixed when
taking quotients.

For a normal subgroup `N` define

`cl_MF(N)=q_N^{-1}(Rad_MF(G_D/N))`.

Equivalently it is the intersection of kernels of all MF-target
homomorphisms of `G_D` that kill `N`. It is a closure operator, and
its fixed points are exactly the normal subgroups with MF quotient.

## 1. Compute the closure on the entire normal lattice

Let `B_J` be the edges of `D\J` lying on no directed cycle. Then

`cl_MF(N(J,S))=N(J union B_J,S)`.                       (1)

In particular every normal quotient of `G_D` is MF exactly when it
is LEF. The MF-closed normal subgroups are precisely those incidence
pairs for which every retained edge lies on a directed cycle.

To prove (1), first delete the edge orbits in `J`. In the resulting
group the image of `N(J,S)` is the product of the isolated vertex
factors in `S`. Removing these clopen components gives the exact
quotient associated to the graph

`(V minus S, E minus J)`.

There are no edges incident to `S` left, by the admissibility of the
pair. Removing these isolated vertices therefore changes no directed
cycles. The directed-seam radical theorem says that the quotient's
radical consists exactly of its edge kernels in `B_J`, with no vertex
factors. Its full preimage is precisely (1). If the graph is empty,
the quotient is trivial and the same formula applies.

This is a finite calculation on every normal subgroup once its
incidence label `(J,S)` is supplied: find the strongly connected
components of `D\J` and adjoin all edges between different components.
The formula does not claim an algorithm to recover `(J,S)` from an
arbitrary list of group words.

For a retained edge `e:a->b`, the formula has a useful equivalent form:

`L_e <= cl_MF(N(J,S))`
`iff there is no directed path from b to a in D\J`.    (2)

Thus losing every return path makes an edge kernel MF-invisible.
If a return path remains, the cycle-core quotient is a LEF target
that kills `N(J,S)` and is injective on `L_e`.

## 2. Arbitrary monotone Boolean rules for one kernel's MF visibility

Let `F:{0,1}^m->{0,1}` be any nonconstant monotone Boolean function.
There exists a three-torsion-generated LEF Kazhdan group `G`, normal
locally finite subgroups `K_1,...,K_m`, and an infinite simple locally
finite normal subgroup `L`, such that

`L <= cl_MF(product_(i in I) K_i) iff F(1_I)=1`         (3)

for every `I subset {1,...,m}`. The input groups are products of
distinct simple edge factors, commute pairwise, intersect pairwise
trivially, and their total product intersects `L` trivially. A variable
that does not occur can have `K_i=1`.

Consequently `L` remains an actual nontrivial subgroup of every input
quotient. Equation (3) determines when all MF-target maps kill it.
When the right side is zero there is a LEF target, killing the chosen
inputs, that embeds `L` faithfully. The source has three generators
of orders `7,2,2` and no nontrivial finite quotients.

Here is a finite construction and proof. Express `F` as a positive
formula using AND and OR; for example use its minimal true subsets
to form a monotone disjunctive normal form. Since `F` is nonconstant,
`F(0)=0` and `F(1)=1`. Its dual function

`F^*(y)=1-F(1-y)`

has a positive formula obtained by interchanging AND and OR. Build
a two-terminal directed network for this dual formula. A variable
occurrence is a directed edge labeled by that variable. An AND joins
the two networks in series; an OR joins them in parallel. Induction
on the formula proves:

- the network is acyclic;
- every vertex and edge lies on a source-to-sink path when all
  occurrence edges are present;
- a source-to-sink path remains when precisely the variables with
  `y_i=1` are enabled if and only if `F^*(y)=1`.

Add one feedback edge `e` from sink to source. Every edge of the full
graph lies on a directed cycle, so its seam group `G` is LEF. Choose
one fixed infinite minimal binary endpoint system at every vertex.
Let `K_i` be the product of the edge factors labeled `i` and set
`L=L_e`. Quotienting by the input product indexed by `I` deletes
exactly the occurrence edges whose variables have `x_i=1_I(i)`.

The feedback edge lies on a cycle exactly when the remaining network
has a source-to-sink path, which is the condition
`F^*(1-x)=1-F(x)=1`. Applying (2) gives (3). If it survives, restricting
to the cycle core gives the asserted faithful LEF image of `L`.

This realizes a specified monotone rule on designated input subgroups
and one output subgroup. It does not assert that an arbitrary abstract
closure operator is realized on the entire normal lattice, or that
every input quotient is itself MF when the output remains visible.
Other surviving edges can have lost their own return paths.

## 3. Arbitrarily many inputs can be jointly necessary

For each `m>=2`, take two vertices, one edge `e:0->1`, and `m`
parallel return edges `f_i:1->0`. Let `G_m` be the associated group,
`L=L_e`, and `K_i=L_(f_i)`. All these factors are infinite simple
locally finite. Both vertex systems can be the same fixed system `Y`.
Every edge lies on a cycle, so `G_m` is LEF Kazhdan.

For every proper subset `I` of the `m` inputs, at least one return
edge remains. Every remaining edge then lies on a cycle, giving

`G_m / product_(i in I) K_i is LEF`,
`cl_MF(product_(i in I) K_i)=product_(i in I) K_i`.     (4)

If all inputs are killed, only `e` remains. The quotient `H_m` is
just non-MF, with exactly five normal subgroups and with `L` as its
MF radical. In the original group,

`cl_MF(K_1...K_m)=K_1...K_m L`,                        (5)

and the inclusion is strict. Its maximal MF quotient is `Q x Q`,
where `Q=EL_(3ell)(R_Y)` at the fixed rank for this graph. Both `G_m`
and `H_m` have three torsion generators of orders `7,2,2`, property
(T), and no nontrivial finite quotients.

The source has `2^(m+1)+3` normal subgroups. Every proper set of deleted
edges leaves the two vertices incident to an edge, giving one normal
subgroup for each of the `2^(m+1)-1` proper edge sets; deleting all
edges allows four choices of vertex factors. This gives the count.

Thus MF-closed normal subgroups can have a nonclosed join even when
every proper subjoin is closed, with no bound on the number of inputs
needed for the first failure. The inputs here are simple locally
finite groups, and this minimality is measured among the designated
simple factors. This realizes
the rule `F(x)=x_1 AND ... AND x_m` in its particularly strong form
where every proper input quotient is itself LEF.

The ambient radical is trivial, while (5) is nontrivial. In this
family MF closure therefore cannot be computed by adjoining one
fixed normal subgroup to every input: such a subgroup would have to
equal `cl_MF(1)=1`, which would make the closure the identity.

## Scope and verification

All results concern the finite directed-seam construction over `F_2`.
The quotient formulas follow from its complete normal-lattice and
exact-radical theorems. The Boolean construction is a finite path
construction and adds no analytic approximation theorem. These are
written proofs, not Lean formalizations, with no global priority
assertion.

The [finite audit](check-pestov91-mf-closure-rules-2026-09-13.py) checked
all 24 input assignments for three mixed monotone formulas, including
a repeated variable and the two-of-three threshold. It checked
extensivity, monotonicity and idempotence on all 176 edge-deletion
inputs of those networks, plus all 124 input subsets for the parallel
families with two through six inputs and their normal-lattice counts.
All assertions passed on MSI in 0.005097 seconds; see the
[finite receipt](pestov91-closure-finite-receipt-2026-09-13.json).
These finite checks do not verify the group-theoretic proof.

Cairn 2.13.1 checked the six new graph nodes against snapshot
`d8bc03e202da8a19a6b86e010840c674f2969ad0` on MSI in 33.066 seconds.
`check --changed` and `preview` returned zero, all three new claims
were `ESTABLISHED`, and neither baseline nor current graph had errors.
The graph had 10,323 claims and 10,583 routes. The
[Cairn receipt](pestov91-closure-cairn-receipt-2026-09-13.json) records
the source-delta and runner hashes. These validation paragraphs and
receipts were added after the run. Cairn validates dependencies, not
the written mathematical argument; no Lean check was run.
