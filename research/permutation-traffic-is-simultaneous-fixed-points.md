---
rg: 2
id: permutation-traffic-is-simultaneous-fixed-points
kind: claim
title: Branching graph moments of a genuine finite action count simultaneous fixed points
artifacts:
  - research/artifacts/hyperlinear-divergent-strategies-2026-08-18.md
---

Let `X` be finite, let `F` act on `X` by permutations (`P_s` the permutation
matrices of the generators), and let `T` be a connected finite directed graph
with edges labelled by generators.  The graph-indexed moment

```text
tau_T(P) = (1/|X|) · sum over phi : V(T) → X of
                       prod over e = (v → w) of (P_{l(e)})_{phi(w), phi(v)}
```

is computed as follows.  Choose a root `v_0` and a spanning tree; each vertex
`v` carries the word `a_v` read along the tree, and each non-tree edge `e`
carries the cycle word `r_e`.  Then

```text
tau_T(P) = (1/|X|) · | ∩_{e non-tree} Fix(r_e) |.
```

**Proof.**  `(P_s)_{j,i} = 1` iff `j = s·i`, so a nonzero summand forces
`phi(w) = l(e)·phi(v)` on every edge.  Along the spanning tree this determines
`phi(v) = a_v·phi(v_0)`; a non-tree edge is then consistent exactly when its
cycle word fixes `phi(v_0)`.  So the surviving maps `phi` biject with roots
fixed by all cycle words simultaneously.  ∎

**Caveat on normalization.**  This is the *plain* graph sum, not Male's
injective traffic moment `tau^0` (arXiv:1111.4662), which restricts to
injective `phi`.  The two families determine each other by Möbius inversion
over partitions of `V(T)`, so no information is lost, but a reader comparing
formulas with the traffic literature will not see this one verbatim.

**Two consequences, pulling in opposite directions.**

1. *No new invariant survives to the limit.*  If a sequence of finite actions
   has fixed-point characters converging to a normal `0/1` character `1_N`,
   every connected branching moment has a forced limit: `1` when all cycle
   words lie in `N` (union bound over finitely many almost-full fixed sets),
   `0` when some cycle word does not (bounded by that word's fixed-point
   fraction).  So one cannot hope to separate hyperlinear from sofic by
   evaluating a branching graph observable at the limit — the limit values are
   already determined by word membership, exactly as ordinary word traces are.
2. *A genuine finite-defect hierarchy does survive.*  Away from the limit the
   branching moments are not determined by cyclic ones: they measure whether
   several matrix-entry paths can be made simultaneously compatible at shared
   vertices, which is the precise datum a permutation model has and a diffuse
   unitary model need not have.  That is what
   `traffic-branching-rounding-hierarchy` proposes to use, and it is why the
   finite search in the source dossier is restricted to *branching* test
   graphs: directed cycles carry nothing beyond word traces.

Source and re-derivation: `research/artifacts/hyperlinear-divergent-strategies-2026-08-18.md`
(its Lemma 14.1 and §21.8).
