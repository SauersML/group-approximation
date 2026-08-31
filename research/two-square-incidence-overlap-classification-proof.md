---
rg: 2
id: two-square-incidence-overlap-classification-proof
kind: route
title: Enumerate simple context overlaps of two Magic-Square incidence blocks
target: two-magic-square-incidence-overlaps-never-separate
requires:
  - magic-square-one-port-is-a-universal-phase-absorber
---

# Enumerate simple context overlaps of two Magic-Square incidence blocks

## 1. Scope and universal presentation

This calculation concerns **closed graph-incidence networks**.  Every variable
is an edge and occurs in exactly the two endpoint contexts.  It does not cover
identifying a cell variable across three or four contexts, nor does it cover
operator-valued line-product ports.

For a graph `G` and vertex colouring `b:V(G)\to\mathbb F_2`, the universal
incidence group is

$$
\Gamma(G,b)=
\left\langle J,(x_e)_{e\in E(G)}
\ \middle|\begin{array}{l}
J^2=x_e^2=1,\ [J,x_e]=1,\\
[x_e,x_f]=1\quad\text{if }e,f\text{ share a vertex},\\
\displaystyle\prod_{e\ni v}x_e=J^{b(v)}
\quad(v\in V(G))
\end{array}
\right\rangle .                                      \tag{1}
$$

A Magic Square is (1) for `G=K_{3,3}`.

Take two copies of `K_{3,3}` with aligned bipartitions.  Suppose their left
parts have `r` common context vertices and their right parts have `c` common
context vertices.  Identify the edge between every common left/right pair.
The resulting simple graph is

$$
G_{r,c}=K_{3,3}\cup_{K_{r,c}}K_{3,3}.                  \tag{2}
$$

The automorphism group of each block is transitive on subsets of a fixed
size, and interchanging rows and columns sends `(r,c)` to `(c,r)`.  Thus,
assuming `r\geq c`, the connected cases are

$$
(1,0),(2,0),(3,0),(1,1),(2,1),(3,1),(2,2),(3,2),(3,3).
                                                                    \tag{3}
$$

The last case is complete overlap and gives just one `K_{3,3}`.

## 2. The five two-disjoint-cycle cases

Use common left vertices `L_1,\ldots,L_r` and common right vertices
`R_1,\ldots,R_c`.  Denote private left vertices in block A by
`A_1,A_2,\ldots` and in block B by `B_1,B_2,\ldots`.  Denote private
right vertices by `P_1,P_2,\ldots` and `Q_1,Q_2,\ldots`, respectively.
Every alternating word below closes to a four-cycle because each block is
complete bipartite.

The following table exhibits two vertex-disjoint cycles in every indicated
case.

| `(r,c)` | cycle in block A | disjoint cycle in block B |
|---|---|---|
| `(1,0)` | `A_1P_1A_2P_2A_1` | `B_1Q_1B_2Q_2B_1` |
| `(2,0)` | `L_1P_1A_1P_2L_1` | `L_2Q_1B_1Q_2L_2` |
| `(1,1)` | `A_1P_1A_2P_2A_1` | `B_1Q_1B_2Q_2B_1` |
| `(2,1)` | `L_1P_1A_1R_1L_1` | `L_2Q_1B_1Q_2L_2` |
| `(2,2)` | `L_1P_1A_1R_1L_1` | `L_2Q_1B_1R_2L_2` |

Contracting each four-cycle to a two-cycle shows that all five graphs contain
`C_2\sqcup C_2` as a minor.

## 3. The common-bipartition cases

When all three contexts on one side are common, (2) is itself complete
bipartite:

$$
G_{3,c}=K_{3,,6-c}.
$$

Consequently,

$$
G_{3,2}=K_{3,4},\qquad
G_{3,1}=K_{3,5},\qquad
G_{3,0}=K_{3,6}.                                      \tag{4}
$$

Paddock--Russo--Silverthorne--Slofstra,
*Arkhipov's theorem, graph minors, and linear system nonlocal games*,
Algebraic Combinatorics **6** (2023), 1119--1162,
doi:10.5802/alco.292, Theorem 1.4, prove

$$
\Gamma(G,b)\text{ is finite}
\quad\Longleftrightarrow\quad
G\text{ has neither }C_2\sqcup C_2\text{ nor }K_{3,6}
\text{ as a minor}.                                  \tag{5}
$$

Finiteness is independent of `b`.  Equations (3)--(5) and the explicit
cycle witnesses give the promised table:

| overlap | graph-theoretic witness | incidence group |
|---|---|---|
| `(3,3)` | `K_{3,3}` | finite |
| `(3,2)` | `K_{3,4}` | finite |
| `(3,1)` | `K_{3,5}` | finite |
| `(3,0)` | `K_{3,6}` | infinite |
| all other cases in (3) | `C_2\sqcup C_2` minor | infinite |

The same paper computes the homogeneous orders
`|\Gamma(K_{3,4})|=256` and `|\Gamma(K_{3,5})|=8192`, and proves
`\Gamma(K_{3,6})` infinite (Table 1 and Proposition 5.24).  In particular,
the proposed theorem that every finite Magic-Square incidence network has
an extraspecial finite universal group is false.  Infinitude begins already
with two blocks sharing one entire bipartition and no contexts on the other.

## 4. Infinitude still does not create the marked gap

The useful marked statement is much stronger than a finiteness calculation.
Corollary 4.7 of the same paper states, for every graph `G`, that

$$
J=1\text{ in }\Gamma(G,b)
\quad\Longleftrightarrow\quad
J\text{ is trivial in every finite-dimensional representation}.   \tag{6}
$$

Equivalently, `J\neq1` in the universal group if and only if some
finite-dimensional representation sends `J` to `-I`.  This is the
disconnected form of Arkhipov's theorem.  Through the solution-group
correspondence, (6) is exactly

$$
\omega^{\mathrm{co}}(G,b)=1
\quad\Longleftrightarrow\quad
\omega^q(G,b)=1.                                      \tag{7}
$$

For the connected graphs `G_{r,c}` one can also see (7) directly.  Even
`b` has a scalar solution.  Odd `b` has a finite-dimensional perfect
solution precisely when `G_{r,c}` is nonplanar; every graph in (3) contains
a `K_{3,3}` block and is nonplanar.

Therefore the infinite entries in the table are not candidate
nonhyperlinear marked sectors.  They show only that the whole universal
group has infinite directions; the distinguished sign is already witnessed
in finite dimension whenever it is witnessed at all.

## 5. Exact residual

The two-block scalar arrangement lane is exhausted, but this is not a
no-go for every way of drawing two grids.  The following operations leave
the hypotheses of (1) and hence remain live:

1. identify a cell observable across more than two contexts;
2. replace a scalar vertex product by an operator-valued source port;
3. impose cross-block equations that are not graph-incidence vertex
   products.

Any claimed escape must state which of these higher-incidence features it
uses.  Merely producing an infinite incidence group, or merely adding a
second nonplanar square, cannot supply a perfect commuting-versus-finite
separation.
