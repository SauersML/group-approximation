---
rg: 2
id: s3-standard-operator-channel-has-fivefold-reduced-gauge
kind: claim
title: The standard conjugation channel of an arbitrary S3-relative operator has five reduced block sources
distinct_from:
  s3-hard-cell-three-channel-data-is-nondegenerate: that computes the three intermediate carrier channels in sigma tensor sigma tensor sigma to sigma; this counts the reduced operator-block sources before any triple product is recoupled.
  regular-subgroup-branching-is-hall-balanced: that concerns restriction-type weights from S4 to S3; this concerns the diagonal-conjugation decomposition of the full operator space on an S3 packet.
  atlas-hard-packet-s3-channel-decoder: that asks the literal hard packet to recover three Leavitt path products; this identifies two additional standard-channel gauges which must first be eliminated or authenticated.
---

Let an exact `S3` packet be written

```text
H=(1 tensor M_1) directSum (epsilon tensor M_epsilon)
  directSum (sigma tensor M_sigma).                    (S3O1)
```

Under diagonal conjugation by `S3`, the carrier of an arbitrary operator
block from `V_beta tensor M_beta` to `V_alpha tensor M_alpha` is
`V_alpha tensor V_beta^*`.  Since all three `S3` irreducibles are self-dual,
the nine carrier blocks decompose as

```text
(1,1)               -> 1
(1,epsilon)         -> epsilon
(1,sigma)           -> sigma
(epsilon,1)         -> epsilon
(epsilon,epsilon)   -> 1
(epsilon,sigma)     -> sigma
(sigma,1)           -> sigma
(sigma,epsilon)     -> sigma
(sigma,sigma)       -> 1 + epsilon + sigma.           (S3O2)
```

Therefore the trivial and sign conjugation channels each have three reduced
operator-block sources, while the standard channel has five:

```text
(1,sigma), (epsilon,sigma), (sigma,1),
(sigma,epsilon), (sigma,sigma).                        (S3O3)
```

The corresponding reduced multiplicity spaces are the appropriate
`Hom(M_beta,M_alpha)` factors; their dimensions grow with the external
multiplicity.

Consequently the three-by-three Racah matrix `F_sigma` does not by itself
remove the hard-cell gauge.  It changes basis among the three intermediate
**carrier** channels in a triple product of standard tensor operators, but it
acts over the still-present reduced operator multiplicity data in `(S3O3)`.
Before the `F_sigma`, branching, or overlap determinants can decode three
extension coordinates, the literal atlas relations must isolate and
authenticate a three-dimensional extension-labelled subchannel inside this
five-source standard operator channel.
