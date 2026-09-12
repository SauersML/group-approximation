# Surjunctivity of graphs of groups with a faithful vertex map

Date: 2026-09-11. Lane: `group_frontiers`.

This is an extension of the preexisting shared-tree proof
[`finitary-split-extension-surjunctivity-2026-09-11.md`](finitary-split-extension-surjunctivity-2026-09-11.md)
and its underlying
[`rf-lamp-wreath-surjunctivity-2026-09-11.md`](rf-lamp-wreath-surjunctivity-2026-09-11.md).
The marked-site peeling argument and the double-group case belong to those
artifacts. The additional argument here handles arbitrary graphs of groups
using the action on the free kernel's quotient graph. In particular, it
verifies the tree-path correction terms rather than assuming that the free
basis is permuted.

## 1. Statement

**Theorem.** Let `P` be the fundamental group of a connected graph of groups
with injective edge maps. Suppose there is a homomorphism

```text
f : P -> G
```

to a surjunctive group `G` whose restriction to every vertex group is
injective. Then `P` is surjunctive.

The underlying graph, groups, indices, and edge stabilizers can be infinite.
There is no amenability, residual finiteness, separability, or soficity
assumption on the edge groups or their coset actions. The map `f` need not be
surjective or injective on `P`.

Two concrete forms are:

* If `A,B <= G` and `C <= A intersection B`, then `A *_C B` is
  surjunctive. The amalgam identifies the two given copies of `C`.
* If `A <= G`, `H,K <= A`, and `g in G` satisfies `g H g^-1 = K`, then
  `<A,t | t h t^-1 = g h g^-1, h in H>` is surjunctive.

These statements require the common surjunctive host and, in the second
case, the prescribed conjugation in that host. They do not assert closure
under arbitrary amalgams or arbitrary HNN extensions of surjunctive groups.

## 2. The finitary input and its audited scope

The following is Theorem 0 of the preexisting finitary artifact. We restate
its hypotheses exactly in the form used below.

Let `W=N semidirect G` and let `X` be a `G`-set. For finite `S <= X`, assume
there are epimorphisms `p_S:N->N_S`, where `N_S` is residually finite and
`N_empty=1`. For `U <= S`, there are compatible injections
`i_(U,S):N_U->N_S`. Assume:

1. Any finite list of nonidentity elements of `N` is simultaneously
   nonidentity under some `p_S`.
2. Each `n in N` has finite support data `L(n) <= X` such that

   ```text
   g L(n) intersection (S minus U) = empty
       => p_S(g.n) = i_(U,S)(p_U(g.n)).                     (2.1)
   ```

3. `p_S(k.n)=p_S(n)` for every `k` fixing `S` pointwise.

Then `G` surjunctive implies `W` surjunctive.

The proof uses only finite quotients of the groups `N_S`. For clarity, the
points at which their non-product structure matters are as follows.
Choose `q:N_S->Q` finite and write
`Q_U=q(i_(U,S)(N_U))`. Transplants to
`ker(q i_(U,S) p_U)\W` have coordinates `Q_U x G` and are injective.
When the local memory misses `S minus U`, the top rule becomes the
`U`-rule independently on each left coset of `Q_U` in `Q`.

A map on `B^(Q_U x G)` commuting with left `Q_U`-translation extends
canonically across left cosets to `B^(Q_V x G)` for `U <= V`: changing a
coset representative changes coordinates by a left translation and hence
does not change the extension. Such extensions compose transitively along
subgroup chains. Intersections `Q_U intersection Q_V` are not required to
equal `Q_(U intersection V)`.

The original peeling induction therefore applies: after undoing the
proper-subset maps in an order refining inclusion, the remaining injection
is identity except on finitely many right cosets of the pointwise
stabilizer `G_S`. The finite-memory windows are enlarged at each step to
include all earlier inverse windows. On the exceptional cosets, the rule is
left-`G_S`-invariant. Including finitely many boundary cosets turns it into
an injective cellular automaton over `G_S`, with a finite enlarged alphabet.
Surjunctivity of the subgroup `G_S` gives a local inverse. Induction gives
surjectivity of all transplants. Their separating pullbacks are dense in
the full shift; compactness gives surjectivity on `W`.

This is the existing finite-memory peeling proof, with its coset-extension
compatibility spelled out. No approximation of the action on `X` enters.

## 3. Fundamental groups of vertex-fixed graphs

**Lemma.** Let `G` act on a connected graph `Y`, preserving an orientation
of its geometric edges and fixing every vertex. Choose a base vertex `o`
and put `N=pi_1(Y,o)`. The induced action of `G` on `N` makes
`N semidirect G` carry the finitary structure in Section 2.

**Proof.** Let `X` be the set of positively oriented edges. Choose a
spanning tree `T` of `Y`. For each vertex `v`, let `a_v` be the unique
oriented path in `T` from `o` to `v`. For a positive edge `e:v->w`, put

```text
b_e = [a_v e a_w^-1] in pi_1(Y,o),
b_(e^-1) = b_e^-1.
```

If `e` belongs to `T`, then `b_e=1`; otherwise the elements `b_e` form a
free basis of `N`. Every finite edge loop
`ell=e_1^eps_1 ... e_r^eps_r` based at `o` satisfies

```text
[ell] = b_(e_1)^eps_1 ... b_(e_r)^eps_r.                 (3.1)
```

For finite `S <= X`, let `N_S` be the free group on
`{b_e : e in S minus T}` and let `p_S` kill the other free generators.
The maps `i_(U,S)` are free-factor inclusions. These groups are finitely
generated free groups, hence residually finite. Detection follows by
taking `S` to contain the basis letters in finitely many nontrivial reduced
words.

Given `n in N`, choose a finite edge loop `ell` representing `n` and let
`L(n)` contain all its geometric edges, including the edges in the chosen
tree paths. Since every vertex is fixed, `g.ell` is again a loop at `o`.
Equation (3.1) gives the exact formula

```text
g.n = product_(j=1)^r b_(g e_j)^eps_j.                  (3.2)
```

If `g L(n)` avoids `S minus U`, deleting the basis symbols outside `S`
in (3.2) is precisely deletion outside `U` followed by the free-factor
inclusion. This proves (2.1), including cases where a translate of a tree
edge becomes a non-tree edge.

Now let `k` fix `S` pointwise. It preserves `X minus S` setwise. For
every positive edge `e`,

```text
p_S(b_(k e)) = p_S(b_e).                               (3.3)
```

Indeed, if `e in S`, then `k e=e`; if `e not in S`, both basis symbols
are deleted, with any tree symbol already equal to one. Applying (3.3)
to the loop formula (3.2) proves `p_S(k.n)=p_S(n)`.

Thus all finitary hypotheses hold. Notice that the action does not need
to preserve `T` or permute the free basis. The finite loop formulas account
for all changing tree-path terms. QED.

## 4. Enlarge each vertex group without losing reduced words

Fix a maximal tree `D` in the original underlying graph, and use the
associated Bass--Serre presentation of `P`. Write `A_v` for vertex groups,
`A_e` for edge groups, and `j_e:A_e->A_(t(e))` for oriented edge injections.
Use the convention

```text
t_e j_(bar e)(a) t_e^-1 = j_e(a),
t_(bar e)=t_e^-1, and t_e=1 for e in D.
```

The chosen presentation embeds every `A_v` in `P`. Write
`f_v=f|_(A_v)` and `c_e=f(t_e)`. The homomorphism relation says

```text
c_e f_(o(e))(j_(bar e)(a)) c_e^-1
       = f_(t(e))(j_e(a)).                             (4.1)
```

Build a new graph of groups on the same underlying graph. Its vertex
group at every vertex is a distinct copy `G_v` of `G`. Its edge group is
still `A_e`, with injections `f_v j_e`. Let its fundamental group be `W`.
There is a natural map

```text
J:P->W,       a in A_v |-> f_v(a) in G_v,
              t_e |-> t_e.
```

**The map `J` is injective.** This is the elementary reduced-word
criterion, not an assumption about intersections between different vertex
groups. At a possible pinch along edge `e`, a vertex element `a` maps
into `f_v(j_e(A_e))` exactly when `a` already lies in `j_e(A_e)`, because
`f_v` is injective. Thus an original reduced edge path stays reduced in
the enlarged graph of groups. A nontrivial vertex word also stays
nontrivial. Bass--Serre normal form proves injectivity.

There is a retraction

```text
r:W->G,       g in G_v |-> g,
              t_e |-> c_e.
```

It respects all relations by (4.1); for tree edges `c_e=1`.
It is the identity on the distinguished base vertex group `G_o`, so

```text
W = N semidirect G_o,       N=ker r.                    (4.2)
```

## 5. Identify the kernel graph and conclude

Let `Z` be the Bass--Serre tree of `W`. The kernel `N` meets every
conjugate vertex stabilizer trivially: `r` is injective on every `G_v`,
and injectivity persists on conjugates. Therefore `N` acts freely on
`Z`, and the quotient map

```text
Z -> Y=N\Z
```

is a graph covering. Choose as basepoint in `Z` the vertex stabilized
by `G_o`. Covering theory identifies `N` with `pi_1(Y,o)`.

The residual action of `W/N=G` on `Y` fixes every vertex. In fact the
vertices of type `v` are

```text
N\W/G_v  ~=  G/r(G_v)  =  G/G,
```

so there is exactly one such vertex for each original vertex. The edges
of type `e` form the coset set `G/r(A_e)`. Their orientations come from
the original underlying graph and are preserved by the action.

The action of the section `G_o` fixes the chosen lift of `o`; hence the
covering identification intertwines conjugation on `N` with the induced
based action on `pi_1(Y,o)`. Explicitly, a path in `Z` from the chosen
basepoint to its translate by `n` is sent by `g in G_o` to a path ending
at its translate by `g n g^-1`. This verifies the action used in (4.2).

Section 3 supplies the finitary structure for this exact action.
Section 2 makes `W` surjunctive. Finally `J(P)<=W`, so subgroup heredity
makes `P` surjunctive. This proves the theorem.

## 6. Consequences and exact boundary

The two examples in Section 1 have homomorphisms to `G` given by the
specified inclusions, with the HNN letter sent to the specified `g`.
Hence they follow directly. For `A=B=G`, the amalgam example recovers
the earlier double theorem. In particular the Kun--Thom doubles over
their residually finite actor satisfy Gottschalk surjunctivity, using
the local peeling theorem proved in the cited artifact.

More generally every connected graph of subgroups of `G` with compatible
edge inclusions has a surjunctive fundamental group. Non-tree edge maps
may be conjugated by specified elements of `G` as in (4.1).

This does **not** prove surjunctivity for every free-by-surjunctive group.
An arbitrary action on an infinite-rank free group has not been realized
here by a graph action fixing every vertex. It also does not prove
Gottschalk's conjecture or Boone--Higman, and it does not make arbitrary
quotients of the constructed groups surjunctive.

## 7. Status and source audit

Checked 2026-09-11. Repository searches for graph-of-groups surjunctivity,
vertex-injective surjunctive maps, and free-kernel surjunctivity found
the two preexisting peeling artifacts but no statement of the theorem
above. Its new content is the finite-edge deletion proof for
vertex-fixed graphs and the faithful vertex enlargement.

The primary comparison is Arzhantseva--Gal,
[On approximation properties of semidirect products of groups](https://ambp.centre-mersenne.org/item/10.5802/ambp.386.pdf),
Theorem 1 and Lemma 6. Their surjunctivity consequence assumes a finitely
generated residually finite kernel. Here the free kernel can have
arbitrary rank; the additional condition is its realization by the
specified graph action. Their proof and the present proof use different
finite quotients: the present quotients need not be invariant under `G`.

Bowen--Chapman's
[primary preprint](https://arxiv.org/abs/2511.06586) and
[Bowen's maintained research page](https://web.ma.utexas.edu/users/lpbowen/research-exp.html)
continue to describe the universal Gottschalk conjecture as open.
Their result is about invariant random subgroups and does not supply
this graph-of-groups permanence theorem. Targeted external searches for
surjunctivity with graphs of groups, vertex groups, amalgamated doubles,
and free kernels did not locate the theorem. This search is a bounded
prior-art audit, not an assertion of exhaustive bibliographic novelty.

The argument is a mathematical proof; no search exhaustion, numerical
experiment, or Lean formalization is claimed. No heavy computation was
performed.
