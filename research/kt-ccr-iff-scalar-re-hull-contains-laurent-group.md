---
rg: 2
id: kt-ccr-iff-scalar-re-hull-contains-laurent-group
kind: claim
title: Commutant collapse for every Kun--Thom compressor is equivalent to the least scalar-RE overgroup of Gamma containing the Laurent elementary group
distinct_from:
  relative-embedding-is-commutant-separation: that defines the least scalar-RE overgroup K_C of any subgroup and equates global collapse for C <= A with K_C = A; this compares the commutants of two conjugate subgroups Lambda = t Gamma t^(-1) <= Gamma, characterizes that comparison by K_Gamma, and computes the resulting condition on the compressor monoid for the Kun--Thom pair.
  approximate-collapse-for-kt-compressor: that asks whether the collapse holds for every trace-faithful approximate representation; this proves that the answer depends only on which subgroups between Gamma and G are scalar-RE, and records the one-directional lamp observation made there as half of an equivalence.
  kt-intermediate-coset-wreaths-are-nonsofic: that proves every intermediate coset wreath missing the normal closure is nonsofic; this shows that (CCR) for all compressors is exactly non-hyperlinearity of that same family.
  kt-subgroup-is-a-ce-commutation-stabilizer: that asks for an exact CE stabilizer equal to Gamma and records a weaker target (an exact stabilizer K >= Gamma missing EL_r(R)); this proves that the weaker target exists exactly when (CCR) fails for some compressor.
  rigid-compression-defect-normalization-dichotomy: that equates normalization of Kazhdan centralizers with trivial rigid defects over all approximable groups; this is a single-pair statement with no rigidity input, about commutant comparison inside canonical models of one fixed actor.
artifacts:
  - research/relative-embedding-is-commutant-separation.md
  - research/artifacts/commutation-stabilizer-relative-embedding-2026-09-07.md
  - research/approximate-collapse-for-kt-compressor.md
---

**ESTABLISHED.**  Let `Gamma = EL_r(F_q[N^d]) < G = E rtimes SL_d(Z)` be
the Kun--Thom Theorem E pair, `r, d >= 3`, with
`E = EL_r(F_q[Z^d])`.  Write `alpha(t)` for the integer matrix by which
`t in SL_d(Z)` acts on exponent vectors, so that
`t e_ij(c x^v) t^(-1) = e_ij(c x^(alpha(t) v))`.  A *strict compressor*
is a `t` with `alpha(t)` nonnegative and not a permutation matrix; then
`Lambda_t = t Gamma t^(-1) = EL_r(F_q[alpha(t) N^d]) <= Gamma`.

For a trace-faithful `sigma : G -> U(M)` into a tracial matrix
ultraproduct (`tau o sigma` is the canonical trace) put

```text
CCR(sigma, t):   sigma(Lambda_t)' cap M = sigma(Gamma)' cap M.
```

Assume `G` is hyperlinear (otherwise there is no such `sigma` and every
statement below is vacuous or true), and let `K_Gamma` be the least
intermediate subgroup `Gamma <= K <= G` with `L(K) <= L(G)` scalar
relatively embeddable (`relative-embedding-is-commutant-separation`).

1. **One compressor.**  `CCR(sigma, t)` holds for every trace-faithful
   `sigma` if and only if `t^(-1) Gamma t <= K_Gamma`.  Equivalently,
   for every `K` with `Lambda_t <= K <= G` and `Gamma` not contained in
   `K`, the binary coset wreath `W_K = (direct_sum_(G/K) Z/2) rtimes G`
   is not hyperlinear.
2. **Monoid.**  The set `S = {s in G : s^(-1) Gamma s <= K_Gamma}` is a
   submonoid of `G` (it equals `{s : s^(-1) K_Gamma s <= K_Gamma}`).  So
   the compressors that satisfy universal (CCR) are closed under products
   and positive powers.
3. **All compressors.**  Universal (CCR) holds for every strict
   compressor if and only if `E <= K_Gamma`, if and only if no scalar-RE
   subgroup `K` with `Gamma <= K <= G` misses `E`, if and only if every
   intermediate coset wreath `W_K` with `E` not contained in `K` is
   non-hyperlinear.
4. **Finite reduction.**  It suffices to check the `d(d-1)` elementary
   compressors `alpha = I + E_ij` and the one extra compressor
   `alpha = [[1,2],[1,3]] (+) I_(d-2)`: universal (CCR) for these
   `d(d-1) + 1` compressors implies universal (CCR) for every compressor.

By `kt-intermediate-coset-wreaths-are-nonsofic` each such `W_K` is
already nonsofic.  So (CCR) for all compressors is equivalent to this:
*every* member of the nonsofic intermediate wreath family is also
non-hyperlinear.  A positive answer to
`approximate-collapse-for-kt-compressor` implies (CCR), so it proves
non-hyperlinearity of the whole family, including the Kun--Thom wreath
(`K = Gamma`).  Conversely, one hyperlinear intermediate wreath with
`K >= Lambda_t` and `Gamma` not in `K` (for example a cone subgroup) refutes (AC) for `t`,
without deciding the flagship.  The weaker Question 3.4 target of
`kt-subgroup-is-a-ce-commutation-stabilizer` exists exactly when
universal (CCR) fails for some compressor.

DERIVATION
kt-ccr-iff-scalar-re-hull-contains-laurent-group-proof
