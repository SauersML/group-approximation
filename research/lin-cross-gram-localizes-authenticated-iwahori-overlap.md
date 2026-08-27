---
rg: 2
id: lin-cross-gram-localizes-authenticated-iwahori-overlap
kind: claim
title: The Lin cross-Gram package localizes authenticated Iwahori overlap but does not enter the UGO basin
distinct_from:
  two-transport-cross-gram-has-a-fixed-mass-reducing-corner: that is the unconditional finite-matrix transport and cutoff estimate; this identifies exactly when its corner can be exactified and why the raw UGO data do not provide those hypotheses.
  lin-state-dependent-gh-preserves-the-commutant: that preserves the opposite algebra while exactifying one finite packet; this audits the all-left square-free Iwahori coordinates and the flexible-rank scale.
  regular-congruence-endpoint-orbit-has-uniform-selberg-retraction: that starts with two authenticated exact congruence representations of equal character; this permits approximate transports and extracts only their positive-overlap subrepresentation.
---

Suppose two contraction transports from one source packet `(B_s)` into the
same target packet `(A_s)` have total error `D=o(1)` and cross-Gram mass
`m>=m_0>0`.  Then
`two-transport-cross-gram-has-a-fixed-mass-reducing-corner` produces a
source projection of trace at least `m_0/2` whose total commutator square is
`O(D)`.  If the source is already an authenticated odd-congruence packet,
its uniform Selberg commutant gap produces in the same dimension an exact
source-reducing projection of trace `m_0/2-o(1)`.

Lin's state-dependent Gowers--Hatami dilation is compatible with this
localized conclusion.  Applied to a finite packet and a density supported
on the selected corner, it exactly intertwines the complete opposite
algebra.  Moreover the displayed column isometry obeys

```text
||(P tensor 1)V-VP||_(2,rho)^2
 =E_g ||[P,phi(g)]||_(2,rho)^2,                       (LCI1)
```

so an approximately reducing selected carrier is preserved in precisely
the state seminorm paid by its commutators.

These facts narrow the **authenticated positive-overlap** part of the
`X`/endpoint-orbit mismatch.  They do not imply
`uniform-gauge-optimized-induced-energy`, for five exact reasons.

1. The square-free input supplies no pair of common-target transports and
   no lower bound on their cross-Gram mass.  Constructing them is already an
   endpoint-type authentication statement.
2. An exact core in `C_N(d)` need not be a representation of any finite
   packet to which Lin's theorem applies.  For example `T=1` and an
   arbitrary unitary `R` satisfy `(GOI2)`; `R` may have infinite order.
3. The square-free generators `X,R,T` all act in the same left matrix
   algebra.  Lin's exact functoriality protects `A'`, not a second left
   vertex.  `lin-canonical-dilation-twirls-unprotected-left-carriers`
   gives the exact Reynolds formula and a zero-defect `M_2` example in which
   an unprotected left Pauli carrier is annihilated.
4. The theorem guarantees an amplification by the finite packet size and
   a state-seminorm compression; it gives no bound saying that the added
   relative rank is `O(E_end)`.  Likewise, before congruence authentication,
   an approximately core-reducing spectral cut cannot be replaced by its
   exact BS-invariant hull at energy scale:
   `long-bs14-packets-defeat-invariant-op-thresholding` makes that hull the
   whole packet.
5. A positive common corner need not cover the endpoint-type mismatch.
   `cuspidal-redistribution-refutes-regular-core-orbit-basin` gives two exact
   congruence endpoints with the same represented core but different global
   multiplicities.  Their largest common subrepresentation has asymptotic
   density only `1/2`, while the redistributed endpoint has zero presentation
   energy.  Cross-Gram cutting against the regular reference can recover the
   common half, but the complement must be assigned its adaptive cuspidal
   endpoint type; no defect can pay for discarding it.

Therefore this package closes a real conditional substep: once two
positive-overlap transports into one authenticated congruence type are in
hand, their common exact reducing corner is available.  The surviving UGO
gate is to produce/authenticate those transports and cover the complementary
mass without twirling the other left vertex; root-multiplicity-stratum
crossing is untouched.
