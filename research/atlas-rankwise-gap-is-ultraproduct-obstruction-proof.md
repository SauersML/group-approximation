---
rg: 2
id: atlas-rankwise-gap-is-ultraproduct-obstruction-proof
kind: route
title: Use compactness at fixed rank and the definition of a tracial matrix ultraproduct
target: atlas-rankwise-gap-is-ultraproduct-obstruction
requires:
  - atlas-exact-matrix-zero-set-is-a-finite-quotient-test
  - atlas-a4-context-exact-regular-normalization
---

Fix `k`.  The unitary group `U(20160k)` is compact, and `epsilon(k,U)` is a
continuous function: it is the maximum of finitely many normalized-HS norms
of fixed words.  Hence its infimum `delta_k` is attained.  If `delta_k=0`, a
minimizer is an exact finite-dimensional regular-margin packet/collision
model.  By `atlas-exact-matrix-zero-set-is-a-finite-quotient-test`, this would
give a nontrivial finite quotient of `Gamma_A4`, contrary to the hypothesis.
Thus `delta_k>0`.

If `inf_k delta_k=0`, choose `k_n,U_n` with
`epsilon(k_n,U_n)->0`.  The classes of the fixed chart matrices and `U_n` in
any free tracial ultraproduct satisfy every packet relation and `q_19243`
exactly.  The chart restrictions retain their regular traces, giving
`(RANK-GAP-3)`.

Conversely, represent an exact regular-margin ultraproduct solution by matrix
tuples.  The finite-group chart relations and regular characters may be
simultaneously exactified and normalized using the established A4 context
normalization, changing the tuples by `o_2(1)`.  The two normalized chart
embeddings are unitarily conjugate blockwise, so choose their relative frames
`U_n`.  Evaluation of each of the finitely many fixed words changes by
`o_2(1)`, and therefore `epsilon(k_n,U_n)->0`.  This proves `(RANK-GAP-2)`.

If the multiplicities of a witnessing sequence were bounded, some value of
`k` would occur infinitely often.  Compactness in that fixed unitary group
would produce an exact zero, contradicting `delta_k>0`.  Thus the
multiplicities escape every finite bound.

Finally `(RANK-GAP-4)` is precisely `inf_k delta_k>0`, the negation of
`(RANK-GAP-2)`.  This proves the claimed quantitative no-go without asserting
that the ultraproduct zero set is empty.
