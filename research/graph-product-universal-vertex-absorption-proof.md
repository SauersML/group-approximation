---
rg: 2
id: graph-product-universal-vertex-absorption-proof
kind: route
title: Anchor one noncommuting component and absorb all universal factors
target: graph-products-noncomplete-selfless-criterion
requires:
  - complete-selflessness-tensor-permanence
  - cstar-simple-groups-products-directed-unions
  - graph-products-connected-complement-are-selfless
  - non-dihedral-free-products-are-completely-selfless
  - robert-tracial-selfless-regularity
artifacts:
  - research/artifacts/stw91-universal-vertex-absorption-audit-2026-08-30.md
---

Let (C_i) be the connected components of the complement Gamma^c and put

    P_i = graph_product_(Gamma[C_i]) G_v.

Different complement components are completely joined in Gamma. Graph-product
normal form therefore gives the restricted direct-product decomposition

    P = direct_sum_i P_i.

A singleton complement component {v} is exactly a universal vertex of Gamma.

For a nonsingleton component C_i there are two cases. If |C_i| is at least
three, the complement of Gamma[C_i] is connected, so
graph-products-connected-complement-are-selfless makes C*_r(P_i) completely
selfless. If C_i={v,w}, then v and w are nonadjacent in Gamma and

    P_i = G_v * G_w.

The two-factor classification
non-dihedral-free-products-are-completely-selfless makes C*_r(P_i)
completely selfless unless both labels are C_2. In the exceptional case P_i
is the infinite dihedral group and its reduced algebra is not simple.

We first classify simplicity. Each P_i is a direct factor of P. If
C*_r(P_i) had a nonzero proper ideal I, the quotient map, tensored with the
identity on the complementary direct factor, would give a unital
noninjective quotient of C*_r(P). Hence C-star-simplicity of P forces every
P_i to be C-star-simple. This forces precisely the two conditions in item 3:
singleton factors are the universal vertex groups, and the only nonsingleton
factor not already known to be simple is the C_2*C_2 exception.

Conversely, assume item 3. Every singleton component factor is C-star-simple
by hypothesis, and every nonsingleton component factor is completely
selfless, hence C-star-simple, by the preceding classification. Finite
products of these factors are C-star-simple, and P is their directed union.
The product-and-directed-union permanence theorem therefore makes P
C-star-simple. This proves the equivalence of items 1 and 3.

Selflessness implies simplicity by Robert's theorem, so item 2 implies item
1. For the converse, assume P is C-star-simple. Since Gamma is not complete,
Gamma^c has a nonsingleton component C_0. Its factor P_0 cannot be the
infinite-dihedral exception, and the preceding argument shows that

    A = C*_r(P_0)

is completely selfless. Write P=P_0 times H, where H is the restricted direct
product of all remaining component factors. If H is trivial, A itself is
completely selfless. Otherwise H is a direct factor of the C-star-simple
group P, so the same quotient argument makes C*_r(H) simple. Its canonical
trace is its unique trace. The complete-selflessness tensor theorem, which
does not require exactness of the second factor, now gives selflessness of

    C*_r(P)
      = C*_r(P_0) tensor_min C*_r(H).

This proves item 1 implies item 2. Robert's tracial regularity theorem gives
all stated consequences.

The noncomplete hypothesis is exact for this method: it supplies the
nonsingleton complement component whose completely selfless algebra is the
absorbing anchor. If Gamma is complete, all components are singletons and P
is merely a restricted direct product of the vertex groups; a one-vertex
instance is the still-open universal XCI problem itself.
