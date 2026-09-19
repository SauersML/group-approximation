---
rg: 2
id: iwahori-index-data-does-not-block-ultraproduct-gluing
kind: claim
title: The rank-one Iwahori finite-index data obstructs exact levels, not compatible ultraproduct embeddings
distinct_from:
  sl2-homogeneous-quotient-crossed-product-is-connes-embeddable: that is the open Connes-embeddability claim for the whole reduced amalgam; this identifies exactly what the missing common finite level does and does not prove.
  homogeneous-k-orbit-factor-has-no-finite-a-refinement: that excludes finite Cartan refinements of the spherical label; this shows why the finite-index von Neumann data do not promote that exact-level obstruction to a non-Cartan ultraproduct obstruction.
  index-three-qsystem-rounding-is-relative-repair: that is the normalized-HS repair problem for two finite-dimensional group representations; this is the tracial embedding problem for the two profinite crossed-product vertices of the homogeneous quotient.
---

**THEOREM (established here; proof in
`rank-one-iwahori-ultraproduct-gluing-boundary-proof`).**  Use the notation of
`sl2-homogeneous-quotient-crossed-product-is-connes-embeddable` at `p=2`:

```text
M=N_0 *_B N_1,
N_i=L^infinity(X) rtimes C_i,
B=L^infinity(X) rtimes D,                 [C_i:D]=3.       (RIG1)
```

The failure of the two adjacent compact filtrations to have one common exact
finite level proves only that the two canonical profinite models cannot be
glued **level by level**.  It gives no trace, center, Pimsner--Popa, or local
standard-invariant obstruction to compatible embeddings in a tracial matrix
ultraproduct.

More precisely:

1. Choosing three coset representatives gives trace-preserving left-regular
   embeddings

   ```text
   lambda_i:N_i -> M_3(B).                                  (RIG2)
   ```

   Hence every trace-preserving embedding `beta:B->Q` into a tracial matrix
   ultraproduct produces embeddings

   ```text
   Lambda_i=(id_(M_3) tensor beta) o lambda_i:N_i->M_3(Q).   (RIG3)
   ```

   The unresolved compatibility datum is exactly stable approximate unitary
   equivalence, after amplification and reindexing, of the two restrictions
   `Lambda_0|_B` and `Lambda_1|_B`.  Finite index proves that both restrictions
   preserve the same trace; it does not produce the conjugating unitary.

2. Let `G=Lambda'\T` be the finite bipartite `3`-regular quotient of the
   Bruhat--Tits tree, with vertex classes `V_0,V_1` and edge set `E`.  Then

   ```text
   Z(N_i)=ell^infinity(V_i),       Z(B)=ell^infinity(E),     (RIG4)
   ```

   and the center inclusion sends a vertex atom to the sum of its three
   incident edge atoms.  Vertex atoms have trace `1/r` and edge atoms trace
   `1/(3r)`.  Both center diagrams therefore coexist exactly in one finite
   tracial algebra: take mutually orthogonal equal-rank projections `(q_e)`
   and put `p_v=sum_(e incident v)q_e`.  Thus center weights and the incidence
   graph do not obstruct compatible matrix models.

3. Every edge-to-vertex local inclusion has Jones index three, Pimsner--Popa
   constant `1/3`, and the same local Jones tower on the two vertex types.
   The upper and lower Iwahori group pairs are conjugate after the Weyl swap,
   so the corresponding local profinite crossed-product inclusions are
   isomorphic.  Separate standard invariants consequently cannot distinguish
   the two sides.

What remains is global: the local matrix completions must be chosen coherently
around cycles of `G`.  Their return maps are the right-translation holonomies
of the free lattice `Lambda'`, exactly the action appearing in `(DT2)` of
`dense-s-arithmetic-translation-algebra-is-amplified-profinite`.  Proving
stable conjugacy of `(RIG3)` is therefore a genuine action/holonomy theorem,
not a consequence of finite index.

**Scope.**  This theorem does not construct compatible embeddings and does not
prove `M` Connes embeddable.  It sharply rules out promoting “there is no
common exact congruence level” into an ultraproduct no-go using only the index,
trace, centers, or the individual local standard invariants.  Since `B` is
nonamenable, uniqueness of embeddings of an amenable algebra into `R^omega`
is unavailable; the stable-unitary-equivalence problem in `(RIG3)` is real.

## Attempt after the reduction

- **Use the compact right-translation permutations already present in the
  profinite models.**  Refuted by
  `noncompact-right-holonomy-is-not-compact-profinite`.  In the stabilized
  translation factor, right translation gives an injection
  `L/Z(L)->Out(P)`.  A nontrivial torsion-free lattice element is not compact,
  so its outer class differs from every compact `K`-translation even after an
  arbitrary inner correction.  The finite quotients `K/K_m` therefore
  implement exactly the wrong holonomies.  This does not exclude a new
  embedding into `R^omega` in which the genuine noncompact returns become
  spatial.

DERIVATION
iwahori-ultraproduct-gluing-boundary-proof
