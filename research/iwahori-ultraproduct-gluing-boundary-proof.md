---
rg: 2
id: iwahori-ultraproduct-gluing-boundary-proof
kind: route
title: Separate local index-three induction from global free-lattice holonomy
target: iwahori-index-data-does-not-block-ultraproduct-gluing
requires:
  - homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse
  - homogeneous-k-orbit-factor-has-no-finite-a-refinement
  - dense-s-arithmetic-translation-algebra-is-amplified-profinite
---

Put `L=SL_2(Q_2)`.  Let `K_0,K_1` be adjacent maximal compact subgroups,
`I=K_0 cap K_1`, let `C_i` be the corresponding dense arithmetic subgroups,
and put `D=C_0 cap C_1`, dense in `I`.  Torsion-freeness of `Lambda'` implies
that every compact stabilizer `K_i cap x Lambda' x^-1` is trivial.

## 1. The finite-index regular embeddings

Fix right coset representatives `t_(i,1),t_(i,2),t_(i,3)` for `D` in `C_i`.
The usual Fourier decomposition gives, as right `B`-modules,

```text
L^2(N_i)=directSum_(a=1)^3 u_(t_(i,a))L^2(B).             (RIP1)
```

Left multiplication is therefore a faithful normal homomorphism

```text
lambda_i:N_i->End_B(L^2(N_i)_B)=M_3(B),                  (RIP2)
```

with entries

```text
(lambda_i(x))_(ab)=E_B(u_(t_(i,a))^* x u_(t_(i,b))).     (RIP3)
```

The normalized trace of `(RIP2)` is the original trace on `N_i`.  It is
enough to check this on crossed-product Fourier terms: the diagonal sum is
`3` at the identity term and zero at every nonidentity group term.  Thus any
trace-preserving `beta:B->Q` gives `(RIG3)`.

For the two induced embeddings to agree on the one literal copy of `B`, one
needs unitaries after matrix amplification and subsequence selection such
that, on every fixed finite set `F subset B`,

```text
max_(b in F)||U_k Lambda_(0,k)(b)U_k^*-Lambda_(1,k)(b)||_2 -> 0. (RIP4)
```

Equation `(RIP4)` is precisely equality of the two restrictions in the
tracial ultraproduct.  The Pimsner--Popa bound says that `(RIP2)` has module
dimension three and proves trace preservation.  It contains no assertion of
the form `(RIP4)`.  Such an assertion would follow formally from uniqueness
of embeddings only for an amenable common algebra.  Here `L(D)` is an expected
subalgebra of `B`, and `D` is a nonamenable finite-index subgroup of
`SL_2(Z)`, so `B` is nonamenable.

The absence of a common exact compact level says that the canonical
coordinate versions of `(RIP4)` cannot be made equal before passage to the
ultraproduct.  Equality in the ultraproduct asks only for the normalized-HS
error in `(RIP4)` to vanish, after reindexing and amplification.  The former
statement does not negate the latter.

## 2. Centers carry no obstruction

Let `T` be the Bruhat--Tits tree.  The quotient `G=Lambda'\T` is a finite
bipartite `3`-regular graph.  Write `V_i` for its vertices of type `i` and
`E` for its unoriented edges.  Density gives

```text
L^infinity(X)^(C_i)=L^infinity(X)^(K_i)=ell^infinity(V_i),
L^infinity(X)^D=L^infinity(X)^I=ell^infinity(E).         (RIP5)
```

Essential freeness makes these precisely the centers of the crossed
products.  Haar normalization gives `|V_0|=|V_1|=r`, `|E|=3r`, vertex trace
`1/r`, and edge trace `1/(3r)`.  Under `Z(N_i)->Z(B)`, a vertex indicator is
the sum of the three incident edge indicators.

Choose equal-rank orthogonal projections `(q_e)_(e in E)` in a matrix algebra
and define

```text
p_v=sum_(e incident v)q_e.                               (RIP6)
```

For either `i`, `(p_v)_(v in V_i)` is an orthogonal partition of one and has
the required trace.  The two partitions use the same `(q_e)`, so both center
inclusion diagrams are realized simultaneously and exactly.

## 3. The local Jones data are the same

For a vertex `v` of type `i`, its central corner is the inclusion

```text
L^infinity(K_i) rtimes D  subset  L^infinity(K_i) rtimes C_i. (RIP7)
```

The three `I`-cosets in `K_i` are the three edge atoms incident to `v`.
Equations `(RIP1)--(RIP3)` show directly that `(RIP7)` has Jones index three
and Pimsner--Popa constant `1/3`.

The two local group pairs are isomorphic.  If `g=diag(2,1)` is used to write
`C_1=gC_0g^-1`, then `Ad(g^-1)` sends `D` to the opposite Iwahori subgroup of
`C_0`; conjugation by the Weyl element
`w=[[0,-1],[1,0]]` sends that opposite Iwahori subgroup back to `D`.  The same
map identifies `(K_1,I)` with `(K_0,I)`.  On each free compact orbit in `X`,
the action is the left-translation action on `K_i`, so this pair isomorphism
identifies the local crossed-product inclusions and hence all their Jones
towers.

## 4. What is left after local alignment

Local isomorphisms identify the three edge corners around each vertex.
Choosing them around a spanning tree of `G` causes no compatibility problem.
For every edge outside the spanning tree, the product of these choices around
the resulting cycle is an automorphism of the initial edge factor.  These
cycle return maps are the right-translation return maps of the deck lattice
`Lambda'=pi_1(G)` (a free group).  Thus coherent choices for all cycles are
the same global holonomy problem exposed by

```text
(N tensor B(ell^2)) rtimes Lambda'                        (RIP8)
```

in `(DT2)`.  The local finite-index invariants neither force nor forbid a
matrix-ultraproduct implementation of those returns.  This proves the stated
boundary.
