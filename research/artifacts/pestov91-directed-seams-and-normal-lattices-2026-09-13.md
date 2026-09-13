# Directed seams compute MF radicals and incidence computes normal lattices

2026-09-13. Written proof, not Lean-verified.

Replace the single seam by a finite directed graph `D=(V,E)`, allowing
loops and parallel edges and requiring `V` nonempty. Assign an infinite
minimal binary subshift `Y_v` to each vertex. The resulting group has
one simple locally finite normal subgroup for each edge, and one simple
Kazhdan LEF endpoint factor for each vertex. Direction determines which
edge groups are MF-invisible; incidence determines all normal subgroups.

## 1. The finite graph of isolated joining orbits

Choose a point `y^v in Y_v` for each vertex. The alphabet consists of
the vertex letters `(v,0),(v,1)` and one distinct marker `m_e` per edge.
For `e:v->w`, define

`z^e_j=(v,y^v_j)` for `j<0`,
`z^e_0=m_e`,
`z^e_j=(w,y^w_j)` for `j>0`.

Let `X_D` be the union of all vertex systems and the orbit closures of
these finitely many points. Exactly as for one seam, it consists of
the tagged minimal components and the isolated orbits `O_e={T^j z^e}`.
The marker identifies both the edge and the shift, so each orbit point
is isolated, including for loops or parallel edges. The two ends limit
on the prescribed vertex systems by minimality. The whole subshift is
aperiodic. Put `R_D=LC(X_D,F_2) semidirect Z` and `R_v=R_(Y_v)`.

For any `J subset E`, deleting the orbits `O_e`, `e in J`, leaves the
closed subshift `X_(D\J)`. Restriction of coefficient functions is
onto: finite-window tables on a closed subset extend to the remaining
windows. Its ring kernel is

`I_J=directSum_(e in J) M_fin(Z,F_2)`.                  (1)

Indeed a locally constant function vanishing on the retained closed
set has compact support in the deleted discrete orbits, hence finite
support. Shifts give all their matrix units.

For `n>=2`, restriction gives an exact epimorphism of elementary groups
with kernel

`L_J=product_(e in J) L_e`,
`L_e=GL_fin(Z x {1,...,n},F_2)`.                       (2)

This is the full kernel, by the finite-block proof: different outer
colors give the coefficient transvections and one other color gives
transvections within a color by commutators. Every invertible finite
block over `F_2` has determinant one. Each `L_e` is infinite simple
locally finite. For `GL_n`, including `n=1`, the kernel of restriction
onto its image is the same finitary product. Surjectivity for general
linear or unit groups is not needed or asserted.

## 2. The cycle core is exactly the maximal MF quotient

Let `B` be the set of edges not lying on a directed cycle, equivalently
edges between distinct strongly connected components. Then

`Rad_MF(EL_n(R_D))=L_B` for every `n>=2`,              (3)
`Rad_MF(GL_n(R_D))=L_B` for every `n>=1`.              (4)

For elementary groups, the maximal MF quotient is exactly
`EL_n(R_(D\B))`; for general linear groups it is the image of restriction
to that ring. All these quotients are LEF. In particular the groups
in (3)--(4) are MF exactly when they are LEF, exactly when every edge
of `D` lies on a directed cycle.

First suppose every edge lies on a cycle. At any word-graph level,
the words wholly inside a vertex system form a strongly connected
subgraph, by minimality. All other words lie on a finite bridge walk
along one marked seam, starting in the source vertex subgraph and
ending in the target vertex subgraph. A directed cycle through the
original edge, together with paths inside the vertex subgraphs, closes
every edge of that bridge into a directed walk. Thus every word-graph
edge lies on a cycle. The earlier ring criterion makes `R_D` LEF.
These walks need not be actual recurrent seam orbits: they are finite
word-graph walks, which is precisely what the finite ring models use.
This argument applied to `D\B` proves the upper inclusions in (3)--(4).

To prove the lower inclusions, fix a bad edge `e:v->w`. Let `W` be
the vertices reachable from `w`, so `w in W`, `v notin W`, and no edge
leaves `W`. Define a clopen indicator `p_W` by assigning value one
to the vertex letters in `W` and assigning to each marker the value
of its target vertex. Along each seam orbit this indicator is constant
or makes a single `0->1` transition. It is forward increasing, and
the chosen edge makes a transition.

Use the clopen return-section construction with separation `k=2` for
`n>=2`, or `k=4` for `n=1`. Let `C` be the section, `P=1_C R_D 1_C`
its return ring, and `a` its return-shift unit. The return indicator
`r=1_C p_W` is also forward increasing. Its defect

`d=r-a r a^{-1}`

is supported on exactly one return point in every seam crossing the
cut into `W`, and on no other points. This follows because each such
orbit meets `C` with bounded gaps in both directions: its return
itinerary has exactly one `0->1` transition. In particular its
component on the chosen edge is nonzero. The pair

`s=a r+(1_C-r)`, `t=r a^{-1}+(1_C-r)`

satisfies `ts=1_C` and `1_C-st=d`. Apply the printed torsion-defect
theorem in `EL_(nk)(P)`. The return-tower embedding puts its invisible
root into the original group as `e_12(d)` for `n>=2`, or as the
invisible unit `1+d u^{-1}` for `n=1`.

In the product of edge kernels, this element has a nonidentity
component on every edge crossing the cut. The MF radical is normal.
Commuting with a suitable element of the chosen `L_e` isolates a
nonidentity element of that factor: its component is noncentral since
`L_e` is centerless. Simplicity then puts all of `L_e` in the radical.
This works for every bad edge and proves (3)--(4). It also explains
why cycle-edge finitary kernels survive: the cycle-core quotient is
LEF and embeds each retained edge kernel faithfully.

## 3. Three torsion generators and simple endpoint factors

Write `m=2|V|+|E|`, `d=ceil(log_2 m)` and `ell=2d+4`. Assign distinct
binary `d`-bit strings to the alphabet symbols and encode each by

`11 (0 b_1)(0 b_2)...(0 b_d) 00`.

In every encoded sequence, `11` occurs exactly at codeword starts.
The `ell` possible shift phases are disjoint compact sets and hence
clopen in their union `Z_D`. The return map on phase zero is the
original shift. Full cyclic matrix units give

`R_(Z_D) ~= M_ell(R_D)`.

Thus `G_D=EL_(3ell)(R_D)` is `EL_3(R_(Z_D))`, with the universal
three torsion generators of orders `7,2,2`. It is Kazhdan. Put
`Q_v=EL_(3ell)(R_v)`. Binary letter repetition, applied to each `Y_v`,
makes every `Q_v` infinite simple Kazhdan LEF. Endpoint restriction is
the exact sequence

`1 -> product_(e in E) L_e -> G_D -> product_(v in V) Q_v -> 1`. (5)

Every finite image kills each infinite simple `L_e`, then every
infinite simple `Q_v`. Hence `G_D` has no nontrivial finite quotients.
In all deletions and restrictions below the rank `n=3ell` stays fixed
at its value for the original graph: `G_(D\J)` means `EL_n(R_(D\J))`,
without recomputing the coding length after deleting edges.

## 4. The entire normal lattice is the vertex-edge incidence lattice

Normal subgroups of `G_D` are in bijection with pairs `(J,S)` such that

`J subset E`, `S subset V`, and every edge incident to `S` belongs to `J`.

The corresponding subgroup `N(J,S)` contains exactly the edge factors
in `J` and has endpoint image exactly `product_(v in S) Q_v`. Inclusion
is componentwise inclusion of the two subsets. In particular the
normal lattice is distributive and has

`sum_(J subset E) 2^(number of isolated vertices of D\J)`            (6)

elements. Direction does not enter this formula or the lattice order.

Here is the proof, including uniqueness. For a normal subgroup `N`,
the intersection with the kernel in (5) is `L_J` for some `J`, since
a finite product of nonabelian simple groups has only products of
factors as normal subgroups. Pass to `G_(D\J)` using (2). The image
of `N` intersects every remaining `L_e` trivially, so it centralizes
all of them.

On a retained edge orbit, the representation is faithful for the
restricted ring and the kernel contains every finitary transvection.
Commuting with all these forces a linear map to be scalar: the
off-diagonal entries vanish and the diagonal entries coincide. Over
`F_2` it must be the identity. Thus a centralizing element is the
identity on every retained edge orbit, and by continuity of its
coefficient functions also on every incident endpoint component.

The only remaining components are the isolated vertices of `D\J`.
They are clopen components and give the direct product factors `Q_v`.
Conversely those factors centralize every retained edge kernel.
Therefore the centralizer is exactly that product. Normality forces
the image of `N` to be a subproduct `Q_S`, with `S` a set of these
isolated vertices. Its full preimage is the unique `N(J,S)`.

Conversely each such preimage is normal and has precisely the claimed
intersection and endpoint image. This proves the bijection and its
order statement. The lattice is the down-set lattice of the poset
with an edge below each of its incident vertices; intersections and
unions give meet and join. This also proves (6).

The groups are centerless. A central element first lies in the product
of isolated vertex factors by the same centralizer calculation, and
then in its trivial center. Moreover the direct-product decomposition
of `G_D` is exactly the decomposition by connected components of the
underlying undirected graph. Indeed the subshifts for distinct such
components are clopen, giving the product; a further nontrivial
product decomposition would partition the incidence poset into two
down-sets with no common element and no incidence crossing between
them. This is impossible for a connected component.

## 5. A matched LEF/non-MF pair with 18 normal subgroups

Take three vertices, the three edges of a triangle, and the same
fixed infinite minimal binary system `Y` at every vertex. Compare

`D_cycle: 0->1, 1->2, 2->0`,
`D_order: 0->1, 1->2, 0->2`.

Both alphabets have nine symbols, so `ell=12`. Set
`Q=EL_36(LC(Y,F_2) semidirect Z)` and `L=SL_infinity(F_2)`. Both
groups have exact sequences

`1 -> L^3 -> G -> Q^3 -> 1`,

three torsion generators of orders `7,2,2`, property (T), no nontrivial
finite quotients, trivial center, and no nontrivial direct-product
decomposition. Their normal lattices are isomorphic and have exactly
18 elements: the contributions in (6) for `|J|=0,1,2,3` are
`1,3,6,8`, respectively.

Yet `G_(D_cycle)` is LEF and has trivial MF radical, whereas
`Rad_MF(G_(D_order))=L^3!=1`. Thus the same abstract kernel, endpoint
quotient, full normal lattice and torsion-generator orders do not
determine MF approximability. The endpoint quotient in (5) is common;
the two maximal MF quotients are different, as the radical computation
requires.

## 6. A LEF Kazhdan group can have a non-MF quotient by a simple locally finite subgroup

An even smaller graph gives a quotient counterexample. Take two
vertices with edges `e:0->1` and `f:1->0`, using the same fixed `Y`
at both vertices. The alphabet has six symbols, so the binary coding
has length ten and the group rank is thirty. The two-edge group `G`
is LEF, since both edges lie on a cycle. Delete only `f` and keep this
rank fixed. The exact restriction sequence is

`1 -> L_f -> G -> H -> 1`,

where `L_f ~= SL_infinity(F_2)` is infinite simple locally finite.
The remaining one-edge graph has
`Rad_MF(H)=L_e!=1` and maximal MF quotient
`Q x Q`, `Q=EL_30(R_Y)`. Its five-element normal lattice makes every
proper quotient LEF: `H` is just non-MF. Both `G` and `H` are Kazhdan,
have three torsion generators of orders `7,2,2`, and have no nontrivial
finite quotients. The marking on `H` is the restricted binary marking
of `G`, so no recoding after deletion is involved.

Thus neither operator MF nor LEF is preserved by quotienting by an
infinite simple locally finite normal subgroup, even within these
three-generator Kazhdan groups. The source `G` has seven normal
subgroups (`1+2+4` from the incidence formula), while `H` has five.
This is a quotient nonclosure statement; it is distinct from the
earlier failure of MF to be closed under extensions.

## Scope

The graph construction is over `F_2`, which supplies simple finitary
kernels with trivial scalar centralizers. No general-field normal
lattice assertion is made. The MF calculation uses the printed
torsion-defect theorem through the return-tower embedding. The LEF
half uses actual finite-word graph models. These are written proofs,
not Lean formalizations, with no global priority assertion.

The [finite audit](check-pestov91-directed-seams-2026-09-13.py) checked
all eight triangle orientations, their common 18-element incidence
lattice and its meet/join closure, the seven- and five-element counts
for the two-cycle and one edge, and all 117 adjacent codeword pairs
in the six- and nine-symbol encodings. All assertions passed on MSI
in 0.002066 seconds; see the
[finite receipt](pestov91-graphs-finite-receipt-2026-09-13.json).
These finite checks do not verify the group-theoretic argument.

Cairn 2.13.1 checked the final eight graph nodes against snapshot
`d07caec4727a225745f4fc72bbbb96ac550481b0` on MSI in 31.401 seconds.
`check --changed` and `preview` returned zero, all four new claims
were `ESTABLISHED`, and neither baseline nor current graph had errors.
The graph had 10,318 claims and 10,579 routes. The
[Cairn receipt](pestov91-graphs-cairn-receipt-2026-09-13.json) records
the source-delta and runner hashes. These validation paragraphs and
receipts were added after the run. Cairn validates the dependency
graph, not the mathematical proof; no Lean check was run.
