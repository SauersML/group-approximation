---
rg: 2
id: shared-context-exclusive-v4-tagging
kind: claim
title: Shared BCS context data produce exclusive finite tags for every V4 exit
distinct_from:
  disjoint-tag-covariance-controls-cross-gram: that proves the analytic capacity estimate once exclusive tags and their covariances are supplied; this must construct those tags jointly from the original contextual words.
  globally-conditioned-v4-exit-capacity: that states the final partial-isometry capacity decoder; this isolates its sole remaining matrix-only representation-theoretic input.
  finite-predicate-signed-permutation-sector: that stores one nonlinear predicate in an isolated finite irreducible sector; this must preserve shared-variable compatibility across all contexts and cannot adjoin independent local selector copies.
---

For the fixed non-CE BCS and its synchronized full-V4 context packets,
construct one finitely presented marked extension with the following decoder
for every sufficiently accurate finite-dimensional marked microstate.

After simultaneous fixed-packet exactification, let

```text
P=directSum_c P_c,
i=(c,b),                 b in {00,01,11},
```

where `P_c` is the forbidden parent carrier and `F_i` is the corresponding
V4 failure projection.  The decoder must produce:

1. one fixed finite tag group `H` with inverse-closed generators `S`;
2. an exact target representation `rho:H->U(K)` for which `P` commutes with
   `rho(H)`;
3. exact source tag representations `pi_i:H->U(V_i)` satisfying

   ```text
   Hom_H(V_j,V_i)=0                 for i!=j,
   Hom_H(V_i,(1-P)K)=0              for every i;       (SCT1)
   ```

4. partial isometries `T_i:V_i->K` with `T_i^*T_i=F_i`; and
5. a bounded-overlap covariance estimate

   ```text
   sum_(i,s)||rho(s)T_i-T_i pi_i(s)||_2^2
     <= C E_rel+o(1),                                  (SCT2)
   ```

where `E_rel` is a fixed sum of defining-relator energies formed before the
context copies are separated.

The tag types and the maps in `(SCT1)--(SCT2)` must be extracted jointly from
the original shared selector tuple or from one simultaneous correction on
its overlap complex.  Independently tagging each context is not sufficient.
Completeness requires only an exact unitary representation retaining the
marked word.  It need not extend the non-CE trace, and may absorb the return
atlas in properly infinite multiplicity.  The finite-dimensional decoder and
its HS estimate remain unchanged.

This is intentionally a finite-dimensional decoder, not a family of fixed
group-algebra partial isometries valid in every representation.  The latter
would also exist in the left regular representation, where the embedded
packet has positive forbidden mass, and would contradict the exact
five-fourths capacity inequality at zero relator defect.  The allowed
matrix-only operation is selection by finite multiplicity data after
simultaneous exactification; the forbidden operation is a hidden relator-ideal
certificate for `P`.

Together with `disjoint-tag-covariance-controls-cross-gram`, `(SCT1)--(SCT2)`
give `(VGC5)` directly.  Thus contextual tag exclusivity, not the analytic
Gram estimate, is the remaining content of the global V4 capacity theorem.

## Attempts

- The Schur flip square supplies a group-native projective cocycle on every
  forbidden simple, but its canceling Pauli pair lives in external
  multiplicity and one fixed pair is dilutable.  A successful tagger must use
  this cocycle together with shared-context compatibility, rather than treat
  the packet factors independently.
- A tag representation supported exactly on `P` cannot simply be adjoined as
  a finite controlled group: `P` is a nonlinear selector projection and the
  regular representation would contain the excluded types.  The exclusivity
  in `(SCT1)` must be a consequence of finite-dimensional multiplicity
  selection, not a universal finite-group relation.
- Exhaustive sparse fusion confirms that the present order-128 support packet
  does not supply enough pointwise allowed-flat tag types by coefficient
  enrichment alone: `support-packet-five-sparse-wedderburn-tag-capacity-is-two`
  finds capacity two through five summands.  Any use of this packet must add
  contextual cross-copy information or exploit a broader automorphism-
  covariant equivalence than the pointwise classification.
