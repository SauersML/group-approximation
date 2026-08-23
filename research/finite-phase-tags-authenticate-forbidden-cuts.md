---
rg: 2
id: finite-phase-tags-authenticate-forbidden-cuts
kind: claim
title: Authenticate the forbidden selector inside an already phase-matched type
distinct_from:
  phase-covariance-words-exactly-measure-type-transport-leakage: that exactly eliminates wrong-type population once the type tags are word-spectral; this asks for the nonlinear forbidden selector inside the matched type.
  fourier-normalizer-words-control-block-gram-leakage: that exactly eliminates off-type block-Gram coherence once the spectral packet is given; this must recover the noncanonical forbidden-weighted projection itself.
  compressed-k2m-deficit-is-one-aggregate-sign-row: that leaves one aggregate binary covariance after removing the rectangle gauge; this asks for word authentication of the two analytic signs in that covariance.
  amplification-natural-words-cannot-read-packet-multiplicity: that rules out every selector built only from the fixed packet and its anonymous multiplicity; this explicitly permits the shared BCS source to break that multiplicity symmetry, which is necessary here.
---

**OPEN WITHIN-TYPE GATE.**  For the fixed shared non-CE BCS and its marked
context-type menu, construct a finite ordinary word menu `T`, a constant
`C<infinity`, and an error modulus tending to zero such that every sufficiently
accurate finite-dimensional canonical microstate satisfies

```text
sum_omega
 ||Q_(sigma(omega))U_omega e_omega U_omega^*
   Q_(sigma(omega))-f_(sigma(omega))||_2^2
 <=C sum_(r in T)||r(U)-1||_2^2+o(1).                  (WI1)
```

Here `e_omega,f_omega` are decoded from the analytic forbidden-weighted
carriers `P_omega<=F_cQ_omega`.  The source and target types in `(WI1)` are
already matched.  The exact theorem
`phase-covariance-words-exactly-measure-type-transport-leakage` controls all
wrong-type population, while
`finite-phase-codewords-weight-type-gram-leakage` controls off-type Gram
coherence.  The projection reduction in
`phase-tagged-row-defect-reduces-to-within-type-selector-mismatch` then turns
`(WI1)` into the full summed GTC4 row estimate.

At the aggregate `K_(2,m)` interface, the same gate is the binary covariance
between the analytic signs

```text
I-2sum_j B_jG_jB_j^*       and       I-2C.             (WI2)
```

Authenticating those signs by ordinary words, only in finite canonical
microstates, is the smallest concrete target.

The construction must be genuinely finite-matrix/canonical-profile: it must
extend the perfect commuting model and keep its central mark nontrivial, but
need not impose the forbidden cuts as universal group-algebra projections.

## Attempts

- Type authentication is no longer part of this claim.  Two-sided phase
  covariance controls diagonal wrong-type transport exactly once the type
  cuts are word-spectral.
- The Fourier and covariance identities hold in every finite factor, so they
  cannot distinguish matrix microstates from the regular representation.
  Authentication of `F_cQ_omega` remains the matrix-only step.
- Literal spectral tag relators on all forbidden cuts would kill those cuts
  in the perfect infinite model.  The tags must be decoded from the shared
  game tuple rather than postulated as universal selector identities.
- Hadamard normalizer transport does not assemble independent selector
  blocks; `hadamard-does-not-semidir-independent-selector-blocks` still
  applies.  The useful new object is the finite phase fingerprint, not a
  classicalized transport.
- If a finite-order word `S_c` had a spectral projection satisfying
  `||F_cQ_omega-1_(lambda)(S_c)Q_omega||_2^2<=C E_rel` in matrices, then
  `spectral-compressed-leakage-is-finite-word-moment-functional` would
  finish the subsequent leakage calculation.  Such a surrogate cannot be a
  universal tracial identity without recreating the regular-trace firewall.
- The local finite-group predicate word from
  `boolean-predicate-central-phase-word` does not by itself supply `S_c`.
  On a fixed irreducible packet type it is a fixed scalar/matrix spectral
  label tensored with the identity on anonymous multiplicity.  By
  `amplification-natural-words-cannot-read-packet-multiplicity`, packet-only
  words cannot recover the shared-source projection `F_cQ_omega` living in
  that multiplicity space.  A successful tag must therefore mix the packet
  with the shared BCS observables in a genuinely source-dependent way.
- The `K_(2,m)` rectangle cell removes the last multiplicity gauge.  Its
  remaining compressed leakage is the first concrete test case for `(WI1)`.
