---
rg: 2
id: stationary-julia-angle-block-defeats-type-only-cutoff-selection
kind: claim
title: A stationary principal-angle block defeats type-only Julia cutoff selection
distinct_from:
  one-binary-marginal-block-escape: that uses a private block gauge to defeat one decoded binary marginal; this gives an exact Julia pair with arbitrary small overlap while preserving every independent packet multiplicity.
  rectangular-escape: that enlarges the paired label quotient and shrinks its multiplicity; this keeps all packet labels stationary and hides the heat information in principal angles.
  fixed-packet-hall-atlas-has-no-julia-cutoff-gap: that gives the general rational-cone obstruction; this is the elementary local matrix model showing what the missing nonlinear correlation must exclude.
---

For every `0<=lambda<=1` and every `m`, on
`C^m tensor C^2` put

```text
E=I_m tensor [1 0;0 0],
B=sqrt(lambda) I_m,
U_B=[ sqrt(lambda) I_m       sqrt(1-lambda) I_m ;
      sqrt(1-lambda) I_m    -sqrt(lambda) I_m ],
Q=U_B^* E U_B.                                      (SJA1)
```

Then `E,Q` are equal-rank projections and

```text
E Q E=lambda E,
tr(EQ)=lambda/2.                                     (SJA2)
```

If `alpha>lambda`, the high-spectrum cutoff
`1_[alpha,1](EQE)` is zero although `E` has normalized rank `1/2`.

Tensor `(SJA1)` with any exact finite packet representation or any exact
integer-flow realization of a fixed packet atlas.  All packet type counts,
restriction equations and packet Hall capacities are unchanged up to the
common factor `2m`, while `(SJA2)` remains arbitrary.  Thus packet type data
alone cannot distinguish a large marked candidate `P=E` from a vanishing
high-spectrum cutoff.

This is not asserted to be a representation of the full Fanizza group:
relations coupling the heat operator to the marked occurrence may exclude
it.  It is a sharp local countermodel.  Any successful selector must use
such a coupling and cannot be proved from the Julia pair plus independent
finite packet multiplicities.
