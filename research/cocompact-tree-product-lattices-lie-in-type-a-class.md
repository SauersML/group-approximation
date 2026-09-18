---
rg: 2
id: cocompact-tree-product-lattices-lie-in-type-a-class
kind: claim
title: Every cocompact lattice in the automorphism group of a finite product of thick leafless trees lies in the type (A) class, torsion allowed
distinct_from:
  virtually-torsion-free-tree-lattices-satisfy-pbh: that needs a torsion-free subgroup of finite index and uses plain k-graphs; this allows torsion, carrying the cube stabilizers as a finite groupoid acting self-similarly (Li's Zappa--Szep case).
  product-of-trees-lattices-satisfy-permutational-boone-higman: that allows a finite kernel on X and trees with leaves or two ends; this is its faithful case on thick leafless trees.
---

**ESTABLISHED** through `tree-lattice-with-torsion-via-zappa-szep-kgraphs` (lane
proof; not independently reviewed; no priority claimed). The finiteness input is
Li's Zappa--Sz\'ep Example (III) (arXiv:2110.04505v2, `ex:ZS`, read at source).
Its condition (F) is checked in the route, using Li's definition of the bisection
category.

**Statement.** Let `T_1, ..., T_k` be locally finite, leafless trees with more
than two ends, and `Γ <= Aut(T_1 x ... x T_k)` discrete with finitely many vertex
orbits. Factors may be permuted, and `Γ` may have torsion. Then `Γ ∈ B_A`, so
every subgroup of `Γ` embeds in a finitely presented simple group.

**Scope.**
- Faithfulness on `X` is used: `Γ` must embed in the full group through its
  action on `∏ ∂T_i`. Actions with a finite kernel, and trees with leaves or
  lines as factors, are reduced to this case only up to such a kernel (see
  Attempt 8 of `product-of-trees-lattices-satisfy-permutational-boone-higman`).
- Nothing here uses residual finiteness, irreducibility, or the factor closures.
