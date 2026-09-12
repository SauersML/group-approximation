---
rg: 2
id: two-chart-jacobi-action-holonomy
kind: claim
title: A finite two-chart holonomy absorbs the truncated Jacobi parameter drift
distinct_from:
  jacobi-congruence-clifford-tower: that requests the whole finitely presented tower; this isolates its remaining compatibility problem after the exact two-chart geometry is known.
---

Using the `P_n,Q_n` atlas from `truncated-weyl-two-chart-boundary`, construct
finitely many word templates which:

1. implement upper elementary transformations in the `Q` chart and lower
   elementary transformations in the `P` chart;
2. use the Fourier/coordinate-swap word to pass between the charts;
3. absorb the exact parameter drift `r |-> ur` by the tape compressor;
4. transport the local signs as `J_n=t^nJ_0t^(-n)`; and
5. make the resulting one-cell chart holonomy pay normalized-HS energy, with
   constants independent of `n` and polynomial word-derivation cost.

Together with the fixed relative-Kazhdan words, this supplies the compatible
finite syntax required by `jacobi-congruence-clifford-tower`.

## Attempts

- The exact atlas geometry, including its fixed one-qubit transverse pieces,
  is `truncated-weyl-two-chart-boundary`; sign transport is
  `conjugate-local-signs-preserve-marked-carrier`. What remains is to spell a
  finite compressor presentation for `(TWC3)`. The analytic payment is now
  discharged: `forbidden-packet-reynolds-holonomy-payment` proves that any
  returned Reynolds-channel rank gap costs ordinary normalized-HS word
  energy. Direct finite-table return is impossible by
  `termwise-finite-reynolds-holonomy-has-zero-rank-gap`; the corrected
  algebraic claim is `stabilized-two-chart-reynolds-word-transport`.
- The two parabolics cannot be closed by transporting the ordinary rank-one
  braid.  `jacobi-drifted-braid-defect-is-extensive` computes

  ```text
  A_uB_uA_u-B_uA_uB_u=u(1+u^2)F,
  ```

  of rank `2(N-1)` on `R_N^2`.  The uniquely forced fixed Fourier cocycle
  moves `2N-1` dimensions.  Thus the separate one-cell covariance laws in
  `(TWC3)` do not make the closed chart holonomy one-cell.  Any successful
  stabilized transport must either duplicate the two rank-one actors and
  never transport their braid, or explicitly cancel this extensive cocycle
  in the tail; boundary signs and projective phases cannot do so.
- The first alternative does not retain the analytic engine.
  `braid-free-two-chart-actor-is-amenable` shows that confining the two
  additive parabolics to separate charts makes their actor
  `(R^2) semidirect C_2`, hence amenable; adjoining the Heisenberg tape stays
  amenable and the pair with the infinite tape cannot have relative `(T)`.
  The only surviving exact target is therefore stabilized cancellation of
  the extensive braid cocycle while retaining a mixed nonamenable actor.
