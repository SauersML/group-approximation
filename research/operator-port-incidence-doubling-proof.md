---
rg: 2
id: operator-port-incidence-doubling-proof
kind: route
title: Turn degree-two ports into edges and double open incidence groups
target: degree-two-operator-ports-are-boundary-edges
requires:
  - two-magic-square-incidence-overlaps-never-separate
---

# Turn degree-two ports into edges and double open incidence groups

## 1. Paired operator ports are graph edges

Consider a finite binary LCS.  Its variables are involutions, variables in
one equation commute, and an equation has the form

$$
\prod_{x\in C}x=J^{b_C}.                              \tag{1}
$$

Suppose every variable occurs in exactly two distinct equations.  Make one
graph vertex `v_C` for each equation `C` and one graph edge `e_x` for each
variable `x`, joining the two equations in which `x` occurs.  Then the
incidence matrix of the resulting multigraph is exactly the LCS matrix.
The commutations and products in (1) are precisely the graph-incidence
relations

$$
[x_e,x_f]=1\quad(e,f\ni v),
\qquad
\prod_{e\ni v}x_e=J^{b(v)}.                           \tag{2}
$$

This is the elementary identification stated explicitly by
Paddock--Russo--Silverthorne--Slofstra, *Arkhipov's theorem, graph minors,
and linear system nonlocal games*, Algebraic Combinatorics **6** (2023),
1119--1162, [doi:10.5802/alco.292](https://doi.org/10.5802/alco.292),
pp. 1120--1122.

In particular, writing one context as

$$
\prod_{e\in C}x_e=z                                   \tag{3}
$$

does not change the syntax.  Since `z^2=1`, (3) is
`(\prod_{e\in C}x_e)z=1`, and the context requires `z` to commute with the
other variables.  Thus `z` is simply one more incident edge.  If `z` is the
port of exactly one other context, those two contexts are the endpoints of
that edge.

It follows that any collection of blocks, ports, and additional parity
contexts is a graph-incidence LCS whenever the **total** occurrence count of
every variable is two.  A new parity equation joining several once-open
ports is just a new graph vertex; it is not a non-incidence coupling.

Theorem 4.1 and Corollary 4.7 of the cited paper state that, for every
possibly disconnected graph-incidence group,

$$
J=1\text{ in }\Gamma(G,b)
\quad\Longleftrightarrow\quad
J\text{ is trivial in every finite-dimensional representation}.   \tag{4}
$$

Together with their Theorem 2.4, (4) gives

$$
\omega^{\mathrm{co}}(G,b)=1
\quad\Longleftrightarrow\quad
\omega^q(G,b)=1.                                      \tag{5}
$$

Therefore paired operator ports cannot create the desired perfect gap.

## 2. The universal group with open vertices

The unpaired case is not a closed game, but it has a useful exact
presentation.  Let `G=(V,E)` be a finite graph, let `B\subseteq V` be the
set of open boundary contexts, and put `S=V\setminus B`.  Fix
`b:S\to\mathbb F_2`.  Define

$$
\Pi(G,B,b)=
\left\langle J,(x_e)_{e\in E}
\ \middle|\begin{array}{l}
J^2=x_e^2=1,\quad[J,x_e]=1,\\
[x_e,x_f]=1\quad\text{whenever }e,f\text{ share a vertex},\\
\displaystyle P_s:=\prod_{e\ni s}x_e=J^{b(s)}
\quad(s\in S)
\end{array}
\right\rangle .                                      \tag{6}
$$

There is no product equation at `v\in B`.  The boundary port is the word

$$
P_v=\prod_{e\ni v}x_e.                               \tag{7}
$$

All its factors commute, so `P_v` is itself an involution.  Adding a source
variable `z_v` and the relation `P_v=z_v` merely eliminates `z_v` back to
(7).

## 3. Boundary doubling gives a split injection

Construct the boundary double `D_BG` as follows:

- take two copies `G_1,G_2`;
- keep the two copies of every vertex in `S` distinct;
- identify the two copies of each vertex in `B`;
- retain distinct copies `e_1,e_2` of every edge.

Colour `(s,k)` by `b(s)` for `s\in S` and `k=1,2`, and colour every
identified boundary vertex evenly.  The closed incidence group
`\Gamma(D_BG,\widetilde b)` has an inclusion

$$
\iota:\Pi(G,B,b)\longrightarrow\Gamma(D_BG,\widetilde b),
\qquad
x_e\longmapsto x_{e_1},quad J\longmapsto J.          \tag{8}
$$

To see that this map is injective, define

$$
r:\Gamma(D_BG,\widetilde b)\longrightarrow\Pi(G,B,b),
\qquad
r(x_{e_1})=r(x_{e_2})=x_e,quad r(J)=J.                \tag{9}
$$

Every defining relation is preserved:

1. involution and centrality relations are immediate;
2. edges meeting in one copy map to edges meeting at the corresponding
   vertex of `G`;
3. edges from different copies can meet only at a boundary vertex, and their
   images commute by the boundary commutations in (6);
4. an internal product equation maps to `P_s=J^{b(s)}`;
5. an even doubled-boundary equation maps to `P_vP_v=P_v^2=1`.

Hence `r` is a homomorphism and

$$
r\circ\iota=\operatorname{id}_{\Pi(G,B,b)}.          \tag{10}
$$

So every open incidence group is a retract subgroup of a closed graph
incidence group.

## 4. Exact finite-dimensionality frontier

Say that finite-dimensional unitary representations separate a group `H`
if, for every `1\neq h\in H`, some finite-dimensional unitary
representation `\rho` has `\rho(h)\neq I`.  Then the following two
statements are equivalent:

1. finite-dimensional representations separate every finite open incidence
   group `\Pi(G,B,b)`;
2. finite-dimensional representations separate every closed graph-incidence
   group `\Gamma(G,b)`.

Indeed, (1) implies (2) by taking `B=\varnothing`.  Conversely, if all
closed groups have the property, embed `\Pi(G,B,b)` into its double by
(8).  A finite-dimensional representation of the double separating
`\iota(h)` restricts to one of `\Pi(G,B,b)` separating `h`.

More pointedly, if a boundary word `w(P_v:v\in B)` were nontrivial in
`\Pi(G,B,b)` but trivial in every finite-dimensional representation, then
`\iota(w)` would be a nontrivial element of the closed graph-incidence
group `\Gamma(D_BG,\widetilde b)` invisible in all finite-dimensional
representations.

Arkhipov's theorem proves this separation only for the distinguished central
word `J`, as written in (4).  It makes no statement that arbitrary words,
including boundary words, are separated.  The Paddock et al. paper studies
finiteness and abelianness of the whole group and explicitly leaves further
approximation-relevant group properties for future work (Section 6); its
central-sign theorem must not be cited as residual finite-dimensionality.

## 5. Minimal escape from the no-go

There are exactly two syntactic ways past (5):

- make some variable occur in at least three contexts; for example, attach
  the same already-paired port to a third context;
- impose a relation which is not an ordinary commuting parity context.

By contrast, joining any number of once-open ports in one new parity equation
keeps every occurrence count at two and merely adds one graph vertex.
The load-bearing resource is therefore higher occurrence or non-incidence
algebra, not the number of Magic-Square cycles and not the word “port”.
