---
rg: 2
id: leavitt-hs-block-compatibility
kind: claim
title: Synchronize one-level HS Kun blocks for the Leavitt prefix-compression pair
distinct_from:
  hs-one-level-expander-block-decomposition: That produces a block partition for one Kazhdan group; this assumes such one-level control is available for both groups in the explicit Leavitt pair and asks to synchronize the two partitions and the compressors.
  hs-expander-block-decomposition: That is the full application-specific nested decomposition consumed downstream; this is only the compatibility step which, together with the one-level theorem, would produce it.
  nonmonomial-multiplicity-obstructs-hs-compressor-transport: That refutes this synchronization for arbitrary Kazhdan pairs; this claim exploits the specific prefix-compression relations of `EL_3(R) <= EL_9(R)` and makes no general assertion.
---

Use the explicit triple from `openai-nine-leaf-leavitt-configuration`:

```text
Gamma = EL_alpha(R) ~= EL_3(R) <= G = EL_D(R) ~= EL_9(R),
G=<Gamma,u,v>,
u Gamma u^(-1), v Gamma v^(-1) <= Gamma,
```

where `R=L_(F_2)(1,2)` and `u,v` are the two prefix compressors.

Assume that, for a sequence of normalized-HS almost-representations
`phi_n:G -> U(d_n)` with defect tending to zero, the one-level conclusion of
`hs-one-level-expander-block-decomposition` is available both for `phi_n` as
a `G`-model and for `phi_n|_Gamma` as a `Gamma`-model.

Ask whether the two one-level decompositions can be replaced, after changing
a projection of trace `o(1)` and paying `o(1)` additional total generator
boundary, by decompositions whose abelian block algebras satisfy

```text
B_(G,n) <= B_(Gamma,n)
```

and whose fine atoms obey, for `t in {u,v}`,

```text
forall p_j in At(B_(Gamma,n)), exists p_k in At(B_(Gamma,n)),
||phi_n(t) p_j phi_n(t)^* - p_k||_2 = o(1),
tau(p_k) >= tau(p_j)-o(1).
```

The replacement must preserve dimension-independent positive scalar adjoint
gaps on all surviving coarse and fine blocks.  The `o(1)` bounds are required
to be uniform over the finitely many fixed generators and compressors.

This is a **choice/synchronization** problem, not another spectral-gap
problem.  Independent applications of a one-level decomposition theorem do
not give nesting: two finite-dimensional abelian subalgebras of a matrix
algebra need not commute, so there is no projection-valued analogue of
intersecting two set partitions.  Nor does almost invariance by itself make a
chosen multiplicity MASA compressor-invariant; the established
`nonmonomial-multiplicity-obstructs-hs-compressor-transport` shows that this
fails even at zero defect for a general Kazhdan pair.

The claim is restricted to the Leavitt prefix pair because the exact algebraic
relations carry more information than the abstract one-sided inclusion.  Both
compressors send the three `alpha` leaves into the corresponding three
`alpha_i 0` leaves, and the two complementary leaf packets are exchanged in
the specific nine-leaf configuration.  Any positive proof has to turn that
prefix geometry, expressed only through almost-multiplicative unitary words,
into an approximately common coordinate algebra.

## Attempts

1. **Intersect the two block algebras.**  There is no usable literal
   intersection/refinement operation for noncommuting finite-dimensional
   abelian subalgebras.  Taking products of coarse and fine projections does
   not produce projections and can destroy the scalar block gaps.
2. **Normalize an arbitrary multiplicity MASA.**  Refuted in general by
   `nonmonomial-multiplicity-obstructs-hs-compressor-transport`; the former
   exact-case argument in `hs-expander-block-decomposition` made precisely
   this invalid step.  Any proof must use the Leavitt relations to select the
   algebra, not choose it after the fact.
3. **Use the coarse gap to align the fine algebra.**  A promising direction is
   to encode the fine partition by a bounded self-adjoint size/frequency
   observable, average or pin it inside each coarse expander block, and recover
   spectral projections with the common-threshold coarea lemma.  The missing
   estimate is that the compressor-conjugated fine observable remains close
   to the same finite-dimensional commutative algebra before the median
   argument is available; using median concentration here would be circular.
4. **Exploit both compressors simultaneously.**  The two prefix tables are
   genuinely complementary in the exact Leavitt criterion.  A common
   low-energy algebra for the word packets associated to both `u` and `v`
   might rigidify the multiplicity action enough to force monomiality.  No
   dimension-free quantitative statement of this kind is currently in the
   graph.
