---
rg: 2
id: arithmetic-star-packet-hs-wall-placement
kind: claim
title: The HNN relations place the S9 Reynolds gap in the compressed Kazhdan spectral wall
refuted_by: arithmetic-star-packet-is-sofic
distinct_from:
  property-t-hs-positive-density-commutant-no-growth: That theorem forbids any already-placed positive-density wall; this must place the concrete packet Reynolds gap into its two spectral cutoffs.
  arithmetic-star-packet-hs-plancherel-anchor: That computes internal packet density; this must overcome the external P multiplicity gauge and connect that density to the HNN source Laplacians.
artifacts:
  - notes/ARITHMETIC_STAR_PACKET_HYPERLINEAR_AUDIT.md
---

**REFUTED FOR THIS CARRIER.**  The requested placement cannot hold because
`arithmetic-star-packet-is-sofic` constructs canonical normalized-HS
microstates for the entire carrier.  If the statement below held, those
microstates and `property-t-hs-positive-density-commutant-no-growth` would
contradict one another and make the same group non-hyperlinear.

The original target was to let `P_n` and `Q_n` be the parent and compressed
adjoint low-spectrum projections and use packet covariance plus
`t p t^(-1)=alpha(p)` to construct projections `W_n` satisfying

```text
W_n <= Q_n,
W_n perpendicular P_n,
tr_ad(W_n) >= 1/192-o(1).
```

Such a theorem would have had to pay the commuting multiplicity representation
exposed by `arithmetic-star-packet-host-splits-inner-action-gauge`.  Merely
identifying the internal Reynolds projection `R_(Q_0)-R_Q`, or selecting the
single marked matrix difference, is insufficient.

## Attempts

- **Direct reuse of scaled transport dies at the metric hypothesis.**
  `ScaledKazhdanTransport.scaled_transport_both` takes an
  `OpAlmostRepresentation`, so its multiplication error is operator-norm
  null.  Hyperlinear lifts are only normalized-HS multiplicative.  Taking
  the dimension weight changes the commutant norm, not this ambient input.
- **The internal Reynolds gap alone dies at the multiplicity gauge.**  In the
  splitting `K times P`, external source matrices have the form
  `V(theta(p)) C_p` with `C_p` in the packet commutant.  Thus
  `R_(Q_0)-R_Q` need not be low for the external compressed action or high
  for the external parent action.
- **Decisive escape.**  The multiplicity gauge globalizes to a sofic envelope.
  The amalgam kernel is a twisted free product of packet copies over `E/P`.
  Diagonal conjugacy embeds each copy into the `K^Q` clique fiber over
  `E/ker(theta)`, converting the inner twist into pure site permutation.
  Exact telescope-orbit graph models and graph-wreath permanence then make
  the carrier sofic.  Thus no overlap estimate with the proposed conclusion
  can follow from these relations.
