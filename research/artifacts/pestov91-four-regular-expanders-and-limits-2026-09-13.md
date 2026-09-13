# Four-regular simple expanders with a complete symbolic limit description

2026-09-13. Written proofs, not Lean-verified. The earlier finite-simple
approximation theorem gave bounded degree for each minimal subshift.
Here one explicit family has degree four, a common absolute spectral
gap, complexity-controlled model sizes, and an exact description of all
its limits as the dimensions grow.

## 1. The finite family

Let `z` be any primitive cyclic binary word of length `N>=2`. Primitive
means that its least period is `N`. Let `P` act on the standard basis by
`P e_j=e_(j+1 mod N)`, and let `D=diag(z_0,...,z_(N-1))`. In block
matrices over `M_N(F_2)`, define

`c_N=[[0,0,I],[I,0,I],[0,I,0]]`,
`t_z=[[I,I-D,D],[0,I,0],[0,0,I]]`,
`w_N=[[0,P,0],[P^{-1},0,0],[0,0,I]]`.

**Finite-family theorem.** These generate
`Q_z=SL_(3N)(F_2)`, and have exact orders `7,2,2`. The undirected Cayley
graph with symmetric generating set

`Sigma_z={c_N,c_N^{-1},t_z,w_N}`

is a simple connected four-regular graph. There is a single `kappa>0`,
independent of `z,N`, such that its normalized adjacency operator on
the orthogonal complement of the constants has spectrum in

`[-(1+cos(pi/7))/2, 1-kappa^2/8]`.                       (1)

Thus the absolute spectral gap is at least
`min(kappa^2/8,(1-cos(pi/7))/2)>0` for this entire family. No numerical
value for `kappa` is asserted.

**Generation.** The conjugates of `D` by powers of `P` give the
indicators of letters at every cyclic position. Products of these and
their complements give the indicators of cyclic length-`N` windows.
Distinct positions have distinct such windows because `z` is primitive.
Hence these products include every singleton diagonal matrix. Together
with `P`, they generate every matrix unit. Therefore `P,P^{-1},D`
generate `M_N(F_2)` as a unital algebra.

Apply the unit-idempotent three-generator theorem to this ring. It gives
`<c_N,t_z,w_N>=EL_3(M_N(F_2))=SL_(3N)(F_2)`. The last equality follows
by flattening elementary roots; roots inside one outer colour are
commutators through a different colour. These finite groups are simple,
as the usual finite groups `PSL_(3N)(F_2)=SL_(3N)(F_2)`.

The two elements of order seven are distinct, the two involutions are
distinct by their block entries, and neither is the identity. Orders
also separate the former pair from the latter. This proves the precise
degree and absence of loops or multiple edges.

**Spectral gap.** The fixed group

`U=EL_3(F_2<u,v,p>/(uv=vu=1,p^2=p))`

is Kazhdan and has the same generating triple, by the marked encoding
theorem. Mapping `u,v,p` to `P,P^{-1},D` is onto on rings and hence on
elementary groups. Choose a Kazhdan constant `kappa` for
`{c,c^{-1},t,w}` in `U`. For the normalized adjacency operator `M` of
any quotient and any unit vector `xi` orthogonal to invariant vectors,

`< (I-M)xi,xi > = (1/8) sum_(s in Sigma) ||s xi-xi||^2`
`                   >= kappa^2/8`.

This proves the upper spectral bound. The unitary `c` has order seven,
so `c+c^{-1} >= -2 cos(pi/7) I`. The two involutions are self-adjoint
and each is at least `-I`. Adding these three inequalities and dividing
by four proves the lower bound in (1). No holding probability is added.

## 2. Balance the word graph to obtain short primitive periods

For a nonempty binary subshift `X`, write `L_r(X)` for its length-`r`
language and `p_X(r)=|L_r(X)|`. Its directed word graph at level `r>=1`
has vertices `L_r(X)` and edges `L_(r+1)(X)`, with an edge going from
its length-`r` prefix to its length-`r` suffix.

**Word-graph lemma.** If this graph is strongly connected, there is a
primitive cyclic word `z` with

`L_(r+1)(z^infinity)=L_(r+1)(X)` and
`p_X(r+1) <= |z| <= b_X(r) <= p_X(r)p_X(r+1)`,           (2)

where, writing `V=p_X(r)` and `E=p_X(r+1)`,

`b_X(r)=E+(E-V)(V-1)`.

Start with one copy of each directed edge. At a vertex let
`d=outdegree-indegree`. The total positive imbalance is at most `E-V`:
every vertex has indegree and outdegree at least one, so the sum of
positive `d` is at most the sum of all `outdegree-1`. Add shortest
directed paths from vertices with negative imbalance to vertices with
positive imbalance, one unit at a time. Each path has at most `V-1`
edges and reduces the total positive imbalance by one; internal vertices
have unchanged imbalance. After at most `E-V` paths the multigraph is
balanced and still strongly connected. An Euler circuit traverses every
original edge and has length at most `E+(E-V)(V-1)`. This is at most
`EV`, since their difference is `V(V-1)`.

The overlap rule for prefix and suffix vertices spells a cyclic binary
word whose length-`r+1` windows are exactly the traversed edges. Replace
it by its primitive root: this does not change the bi-infinite periodic
sequence or any of its languages. Its `N` positions have to realize
all `E` distinct edges, so `N>=E`; also `N<=b_X(r)`. This proves (2).

The construction uses only the finite word graph. In particular no
recurrence function or return-time bound is needed.

## 3. Exactly which subshifts arise at unbounded periods?

Call a subshift admissible here if it is infinite and every one of the
word graphs in section 2 is strongly connected. This is a definition
for the following theorem, not a new dynamical hypothesis on the
original minimal examples.

**Periodic-limit lemma.** The limits, in finite-language topology, of
single primitive periodic orbits with least periods tending to infinity
are exactly the admissible subshifts.

For necessity, finite-language convergence makes each fixed word graph
eventually equal to that of the periodic orbit. The latter is strongly
connected because a full circuit traverses every vertex and edge. A
finite subshift with all these graphs strongly connected is a single
periodic orbit: for sufficiently long windows the distinct points are
distinguished and the word graph is a disjoint union of their orbit
cycles. Strong connectivity leaves only one cycle. A periodic orbit of
least period `N` is isolated among periodic orbits by its length-`N+1`
language. Those windows have a unique successor at each length-`N`
vertex and force exactly that orbit. It therefore cannot be approached
by primitive orbits with least periods tending to infinity.

For sufficiency, apply (2) at successively larger levels. The languages
of the primitive periodic orbits agree with `X` through length `r+1`.
Their periods tend to infinity because `p_X(r)` tends to infinity for
every infinite subshift. To see the last fact directly, the numbers of
distinct centered finite windows are nondecreasing, and boundedness
would leave only finitely many full sequences. This proves the lemma.

Every infinite minimal subshift is admissible. For vertices `a,b` of
one word graph, choose a point containing `a`. Minimality implies that
`b` occurs arbitrarily far to its right, and the intervening segment
gives a directed path from `a` to `b`.

For an admissible `X`, in fact `p_X(r)>=r+1`. Strong connectivity gives
at least one outgoing edge per vertex. If `p_X(r+1)=p_X(r)`, each vertex
has exactly one outgoing edge and the graph is a single directed cycle.
Its allowed paths force `X` to be a finite periodic orbit, a contradiction.
Thus complexity strictly increases at every level, starting with
`p_X(1)=2`.

## 4. Exactly which groups are limits of the finite family?

Mark `G_X=EL_3(LC(X,F_2) semidirect Z)` by `(c,t,w)` as in the marked
encoding theorem, and mark `Q_z` by the triple in section 1.

**Boundary theorem.** As `|z|` tends to infinity, the marked limit points
of the finite family `Q_z` are precisely the marked groups `G_X` for
admissible subshifts `X`. The parameter `X` is unique. These limit groups
are all Kazhdan and LEF. They are simple exactly when `X` is minimal.
In particular every binary Pestov group, including the fixed universal
locally finite host, is a limit of this one four-regular expander family.

Here is the finite-model comparison that proves the assertion. Let `X_z`
be the orbit of `z^infinity`. There is a ring epimorphism

`R_(X_z) -> M_N(F_2)`, `f -> diag(f(T^j z))`, `u -> P`.

It is faithful on all normal forms `sum_(k=-l)^l f_k u^k` when `N>2l`:
different exponents occupy disjoint cyclic matrix diagonals, and diagonal
evaluation is faithful on functions on the orbit. Every relation word
of length at most `l` in the three generators has degrees in `[-l,l]`.
Thus `Q_z` and `G_(X_z)` agree on all such relations whenever `N>2l`.

Consequently, if `N_j -> infinity` and `X_(z_j) -> X`, then
`Q_(z_j) -> G_X`, by continuity of the marked encoding. Conversely any
convergent sequence of the finite groups with `N_j -> infinity` has a
subsequence along which the periodic orbits converge, by compactness of
the space of subshifts. Its group limit is `G_X` by the same comparison,
and section 3 characterizes `X`. Injectivity of the marked encoding
proves uniqueness. Its simplicity criterion proves the last assertion.
Being marked limits of finite groups gives LEF, also for the admissible
nonminimal parameters. Property (T) comes from the common source `U`.

## 5. Model sizes from complexity alone

For an admissible `X` and integer `l>=1`, apply (2) at `r=2l`. It gives
a primitive period

`2l+2 <= p_X(2l+1) <= N <= b_X(2l)`.                    (3)

The finite word agrees with `X` on windows of length `2l+1` and has
`N>2l`. The finite-window bound from the marked encoding theorem and
the comparison in section 4 therefore give agreement on every group
relation of length at most `l` in `SL_(3N)(F_2)`.

For the LEF growth function in this three-generator word metric, a
model agreeing on relations through length `3R` locally embeds the
radius-`R` ball. Indeed it identifies none of its distinct elements
(comparison words have length at most `2R`), and preserves every
product `xy=z` staying in the ball (length at most `3R`). Since
`|SL_(3N)(F_2)| < 2^(9N^2)`, (3) gives

`LEF_(G_X)(R) <= 2^(9 b_X(6R)^2)`.                      (4)

For a Sturmian subshift, `p_X(r)=r+1` and `E-V=1`, so
`b_X(r)=2r+2`. The relation-radius-`l` model has `N<=4l+2`, hence
matrix dimension at most `12l+6`, and

`LEF_(G_X)(R) <= 2^(9(12R+2)^2) = exp(O(R^2))`.

This is a size bound, not an algorithm choosing valid models without
access to `L(X)`. For a noncomputable Sturmian language, such a computable
choice for every radius would decide the word problem by evaluation in
the chosen finite model, contradicting the earlier language/word-problem
equivalence. The uniform size bound is compatible with every Turing
degree occurring in the Sturmian family.

## 6. Scope

The generic bounded-degree finite-simple approximation theorem was
already established in the repository. The additions here are degree
four, the uniform absolute spectral interval, the word-graph construction
with bound (2), and the exact description of the limits at unbounded
periods. The same graph construction extends the approximation argument
from minimal systems to all admissible systems. The algebraic, Kazhdan
and marked-encoding inputs remain the existing proved claims. These are
written proofs, with no global priority assertion or Lean verification.

The [word-graph receipt](pestov91-expander-word-graph-receipt-2026-09-13.json)
records a bounded MSI check of degree balancing, the Euler circuit,
primitive-root extraction and exact cyclic languages on 18 finite word
graphs: levels 1--6 of the full binary shift, golden-mean shift and
sampled Fibonacci language. Every language equality and period bound
passed. The single Python 3.12 process took 0.016 seconds. These checks
exercise the finite construction; the general spectral and limit
arguments are the written proofs above.

The [Cairn receipt](pestov91-expanders-cairn-receipt-2026-09-13.json)
records successful check and preview on the archived research snapshot
at `aefed65f3f9989b7cd298c1599f86e1662f28b32`, overlaid with this change.
Cairn 2.13.1 parsed 10,244 claims and 10,501 routes with no baseline or
final graph errors. All three new claims resolved as established. The
single Python 3.12 process on MSI took 30.038 seconds.

The runner replaced source and HEAD loading while retaining Cairn's
parser, lint, solver, check and preview policies. Artifact existence
used the exact tracked manifest plus the delta; revision-pinned
artifacts used the warm repository's Git objects. This receipt and
paragraph were added afterward. These checks verify graph wiring,
not the mathematical proofs by Lean.
