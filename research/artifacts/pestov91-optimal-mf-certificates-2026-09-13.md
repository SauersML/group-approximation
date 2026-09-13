# Optimal finite normal detectors and minimum MF implication certificates

2026-09-13. Written proofs, not Lean-verified.

Use the finite directed-seam group `G_D`, its simple edge kernels `L_e`,
its simple endpoint quotients `Q_v`, and its incidence normals `N(J,S)`.
Write `b_e` for the marker involution normally generating `L_e` and `a_v`
for the vertex involution from the
[finite controller theorem](pestov91-finite-normal-control-2026-09-13.md).
The coding table and original matrix rank remain fixed in all quotients.

## 1. The finite detector has the smallest possible order

Say that a finite subgroup `H <= G_D` detects normal subgroups if the map
`N -> H intersection N` is injective on the normal lattice. Then

`|H| >= 2^(|V|+|E|)`.                                (1)

The already constructed `A=<a_v,b_e> ~= C_2^(|V|+|E|)` attains equality.
Thus it is optimal even among finite detectors that are not abelian and
that need not provide single normal generators.

For each edge, comparing `L_e` with the trivial normal subgroup forces
`H intersection L_e != 1`. These finite intersections commute and have
independent supports. Their product lies in `H intersection L_E`, so
that kernel has at least `2^|E|` elements.

Let `pi:G_D -> product_v Q_v` be endpoint restriction. Comparing
`N(E,{v})` with `N(E,empty)=L_E` forces an element of `H` whose endpoint
image is nontrivial and supported only at `v`. Thus `pi(H) intersection Q_v`
is nontrivial for each vertex. These subgroups also have independent
supports, so `|pi(H)|>=2^|V|`. The finite-group order formula
`|H|=|H intersection L_E| |pi(H)|` proves (1).

If equality holds, every displayed intersection has order two. In
particular `H intersection L_E ~= C_2^|E|` and `pi(H) ~= C_2^|V|`.
We do not assert that every optimal detector `H` is itself abelian.

## 2. The exact number of premises needed in the worst case

Inside this fixed group, every family of relators with normal closure
`N(J,S)` has a subfamily of size at most

`|S|+|J minus inc(S)|`                               (2)

with the same ordinary normal closure, and hence the same MF closure.
For each vertex of `S`, choose an original relator witnessing its
vertex coordinate. Those choices already cover all of `inc(S)`. Then
choose one original relator for each remaining edge coordinate in `J`.
The coordinate unions are exactly `(J,S)`, proving (2).

This is sharp for each admissible `(J,S)`: use the relator family
`{a_v:v in S} union {b_e:e in J minus inc(S)}`. Omitting any member
loses its vertex coordinate or its nonincident edge coordinate.
Consequently the exact worst-case subfamily bound for ordinary normal
closure is

`h(D)=max_(S subset V) (|S|+|E minus inc(S)|)`.         (3)

This is the width of the incidence poset, whose edges are below their
incident vertices: its antichains are exactly a vertex set together
with a set of edges not incident to it. Sharpness here concerns ordinary
normal closure. MF closure can identify additional coordinates, so no
claim that (3) is always the sharp MF-only bound is made.

## 3. Individual edge relations obey a minimum-cut theorem

Fix a nonloop output edge `f:a->b`. Designate a set `P subset E\{f}`
of allowed input edges, with nonnegative rational costs `c_e`. Let

`tau=min {sum_(e in J)c_e : J subset P and`
`         every MF-target map killing all b_e, e in J, kills b_f}`.

The value is infinity if there is no successful selection. Put
`K=D\{f}`. Then exactly

`tau=min {sum_(e in delta^+(U)) c_e :`
`          b in U, a notin U, delta^+_K(U) subset P}`. (4)

Here `delta^+_K(U)` denotes the edges of `K` leaving `U`; the sum uses
that same boundary. In words: minimum cost of sufficient MF relations
equals minimum cost of an allowed directed return-path cut.

Indeed the cycle-pruning theorem says that a chosen `J` succeeds iff
there is no return path from `b` to `a` in `D\J`. Such a path can always
be chosen simple, and then cannot use `f`, so work in `K`. A boundary
cut is sufficient. Conversely, for any successful `J`, let `U` be the
vertices reachable from `b` in `K\J`. Then `a notin U` and
`delta^+_K(U) subset J`, whose cost is at most that of `J`. This proves
both inequalities in (4), including zero costs and the infeasible case.

All selected input subgroups have trivial intersection with `L_f`.
Thus the output remains algebraically nontrivial in every input
quotient. If a selection fails, its surviving return path certifies
a LEF cycle-core quotient that is injective on all of `L_f`.

With unit costs and every nonoutput edge allowed, (4) also equals the
maximum number of pairwise edge-disjoint return paths from `b` to `a`.
To recall the finite argument, augment an integral unit-capacity flow
until no residual path remains. Residual reachability gives a cut whose
capacity equals the flow value. Decomposing the integral flow into
paths and cycles, then discarding cycles, gives that many edge-disjoint
paths. Each successful relation selection must hit every one of them.
Thus an optimal cut and an equal-size path packing give certificates
for both directions of the minimum relation count.

Weighted optimization is polynomial time. Clear rational denominators
and give forbidden edges capacity `1+sum_(e in P)c_e`; this quantity
has polynomial bit length. The shortest-augmenting-path algorithm
computes a minimum cut with polynomially many augmentations independent
of capacity magnitude: residual distances never decrease, and between
successive saturations of the same oriented arc its tail distance
increases by at least two. There are at most linearly many such
saturations per arc. A cut below the forbidden-edge capacity is exactly
a feasible answer to (4). For a loop output, no allowed selection can
remove its length-one cycle, so the answer is infinity.

## 4. Grouping edges into one relation makes optimization NP-complete

The input to the grouped decision problem consists of a finite graph
`D`, a nonloop output edge `f`, disjoint nonempty edge sets `P_1,...,P_m`
not containing `f`, and an integer budget `k`. Input relation `i` is
the single word `r_i=product_(e in P_i)b_e`. Decide whether at most `k`
of these relations imply `b_f=1` in every MF-target map out of `G_D`.

This decision problem is NP-complete, even when `G_D` is LEF Kazhdan,
all inputs and the output are independent commuting involutions, and
`D\{f}` consists of internally disjoint directed paths of length two.

Membership in NP follows by guessing the selected indices, deleting
their edge sets, and checking return reachability. For hardness take
an undirected graph `Gamma=(W,F)` with at least one edge, discard isolated
vertices, and form one path

`s --[u]--> z_{uv} --[v]--> t`

for each undirected edge `{u,v}` (choose either ordering). Distinct
edges get distinct intermediate vertices. Add `f:t->s`. For each
vertex `u`, group all occurrence edges labeled `u` into `P_u`.
These groups partition the nonoutput edges and are all nonempty.

A return path survives precisely when some edge `{u,v}` of `Gamma`
has neither endpoint selected. Therefore

`minimum number of sufficient designated relations = vertex-cover number of Gamma`.

Vertex cover is NP-complete: see Karp, *Reducibility Among Combinatorial
Problems* (1972), Main Theorem, item 5, NODE COVER, original page 94
([primary reprint](https://www.cs.umd.edu/~gasarch/BLOGPAPERS/Karp.pdf)).
Discarding isolated vertices preserves its optimum, and instances with
no edges are trivial. This gives a size-preserving budget reduction.

Every source edge lies on a three-edge directed cycle, so the source
group is LEF. The involution theorem supplies the independence and
commutation assertions and ensures that the output survives in every
ordinary input quotient. Fix quadratic Sturmian endpoints throughout.
The positive formula `AND_({u,v} in F)(x_u OR x_v)` feeds directly into
the existing word compiler. If `q=|F|`, it has `2q` occurrences, and
the total expanded word length is at most `256(2q+1)ell^2`, with
`ell=O(log(q+2))`. Hence hardness persists when the input includes
the actual expanded three-generator words, together with their graph
and edge-group certificate; there is no exponential word encoding.

This is a uniform optimization result with the graph varying. It does
not contradict the fixed-graph polynomial algorithm for checking all
given premises. Costs are charged per designated relation: if arbitrary
new relations may replace the designated list, their product normally
generates the whole selected edge kernel and trivializes this count.

## Scope and implementation

The group-theoretic input is the existing exact normal-lattice and MF
closure calculation. The minimum-cut transfer and the vertex-cover
reduction are written deductions from it, not new proofs of those
classical combinatorial results. No global priority or Lean claim is made.

The [minimum-cut solver](minimize-pestov91-edge-mf-relations-2026-09-13.py)
accepts graph endpoint pairs, an output edge and integer costs, using
`null` for forbidden inputs. It returns an optimal selected edge set,
its cost, and the return-source side of the cut, or reports infeasibility.
It uses exact shortest augmenting paths and supports loops, parallel
edges, zero costs and protected edges. Rational input costs can first
be scaled to integers as in the proof.

The [bounded audit](check-pestov91-optimal-mf-certificates-2026-09-13.py)
compared 102 cut instances against exhaustive relation-subset search.
It compiled all 71 nonempty simple graph instances on two through four
labeled vertices into the existing involution-word compiler, discarded
isolated labels, and checked all 856 selections against vertex cover.
All optima agreed. The largest compiled total expanded length was
350,168 letters, represented by its word DAG; all length bounds passed.
The exact incidence width formula was also checked on 34 graphs.
The [finite receipt](pestov91-optimal-finite-receipt-2026-09-13.json)
records a successful MSI run in 0.111855 seconds. These finite graph
and compiler checks do not verify the infinite-group deductions.

Cairn 2.13.1 checked all six new nodes on MSI against snapshot
`8f952bf27b7327e63142d97ecae3a562d15b6c11` in 33.851 seconds.
Both `check --changed` and `preview` returned zero, all three new
claims were `ESTABLISHED`, and neither graph had errors. The graph
contained 10,395 claims and 10,654 routes. The
[Cairn receipt](pestov91-optimal-cairn-receipt-2026-09-13.json) records
the source-delta and runner hashes. This paragraph and that receipt
were added after the check. This is dependency validation, not
mathematical proof verification; no Lean check was run.
