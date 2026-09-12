---
rg: 2
id: closed-covariant-reynolds-cycle-has-full-overlap
kind: claim
title: Every closed covariant cycle returns the whole conditioned Reynolds projection
distinct_from:
  termwise-finite-reynolds-holonomy-has-zero-rank-gap: that treats one unconditioned edge carrying complete finite-group tables and concludes equality of Reynolds ranks; this treats an arbitrary finite cycle of character-conditioned framed subgroups and concludes full scalar overlap at a closed endpoint.
  finite-edge-reynolds-overlap-follows-character-transport: that identifies the one-edge central-character destination; this composes those transports and shows that closing the character together with the framed subgroup also closes the entire Reynolds projection.
  gauge-symmetrizing-hard-pair-cancels-paired-overlap-gap: that computes cancellation after an equal-multiplicity direct sum over one particular gauge orbit; this needs no multiplicity symmetrization and rules out every finite sequence of honest covariant frame resets.
---

Let `H_0,...,H_r` be finite subgroups of a group `Gamma`, and for
`0<=i<r` let `t_i in Gamma` conjugate `H_i` isomorphically onto `H_(i+1)`.
Let `Z_i<=Z(H_i)` be transported onto `Z_(i+1)`, and choose characters
`chi_i in dual(Z_i)` satisfying

```text
chi_(i+1)=chi_i compose Ad(t_i)^(-1)|_(Z_(i+1)).       (CCR1)
```

In a finite-dimensional unitary representation `rho` of `Gamma`, let
`e_i` be the `chi_i` central-character projection and let `R_i` be the
orthogonal projection on `End(H_rho)` onto the operators supported on
`e_i H_rho` and commuting there with `rho(H_i)`. Put

```text
T_i=Ad_(rho(t_i)),       T=T_(r-1)...T_0.              (CCR2)
```

Then

```text
T_i R_i T_i^*=R_(i+1),       T R_0 T^*=R_r.            (CCR3)
```

Consequently, if the cycle is closed as framed character data,

```text
H_r=H_0,       Z_r=Z_0,       chi_r=chi_0,             (CCR4)
```

then `R_r=R_0` and the return overlap is full:

```text
tr_ad(R_0 T^* R_0 T R_0)=tr_ad(R_0).                   (CCR5)
```

The statement also applies when an edge is called a reset and comes from
an automorphism of a larger finite packet. Such an edge carries the framed
subgroup to its automorphic image and carries its coefficient representation
with it. It cannot reset only the central-character name while leaving
behind the untransported coefficient frame. If a later covariant edge closes
the framed data, `(CCR5)` applies.

For the paired support packet this rules out every finite automorphism repair
of the compulsory `101<->011` escape. The first edge may carry
`R_+(101)` to the matching reverse projection `R_-(011)`. A source-only
packet automorphism can rename `011` as `101`, but its target is the Reynolds
projection of the *automorphically moved* minus frame, still unitarily
conjugate to `R_+(101)`. If one additionally identifies that moved frame
with the original plus frame, the resulting finite covariant cycle has full
overlap by `(CCR5)`. It therefore cannot expose the `1/98` deficit between
the two untransported frames at `101`.

Thus a successful one-overlap actuator cannot be a finite chain of subgroup
isomorphisms and packet automorphisms. It must contain a genuinely
noncovariant operation: an averaged/compressed channel, a proper-corner
coefficient direction, or an infinite one-sided ownership label whose local
frame is not returned as part of a finite covariant cycle.

