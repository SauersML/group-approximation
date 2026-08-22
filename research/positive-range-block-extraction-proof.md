---
rg: 2
id: positive-range-block-extraction-proof
kind: route
title: Normalize a central compression, polar-correct generators, and apply character rigidity
target: positive-range-block-extraction-recreates-maslov-microstate
requires:
  - deligne-maslov-sector-traces-are-central-regular
---

Because `z_n` is central in `B_n`, it commutes with every
`phi_n(u_s)`.  Evaluation of any fixed word therefore commutes with
compression by `z_n`.  If `q` is a defining relation, or one of the two
unitarity relations for a generator, then the fact that `(phi_n(u_s))`
represents `Theta|S_alpha` gives

```text
||q(phi_n(u_s))-1||_(2,d_n) ->_omega 0.
```

After compression and normalization by the trace of `z_n`, the squared
defect is at most the original squared defect divided by `tr_(d_n)(z_n)`.
Condition `(PBE1)` therefore makes every fixed compressed defect tend to
zero.

In particular each compressed generator contraction is asymptotically
unitary.  The singular-value polar decomposition supplies a unitary on
`z_n C^(d_n)` at normalized `2`-distance tending to zero (define the polar
factor arbitrarily on the vanishing kernel).  Replacing the finitely many
generators by these polar factors changes every fixed word defect by `o(1)`.
The corrected tuples hence define `(PBE2)`.

The words representing the order-three covering centre and the remaining
order-two centre converge, before compression, to their prescribed scalars.
The same division by the positive number in `(PBE1)` preserves those scalar
relations after compression.  Thus the trace of `(PBE2)` lies in the fixed
full central-character fibre `eta`.  By
`deligne-maslov-sector-traces-are-central-regular`, that fibre has the unique
trace `tau_eta`.  This proves the claim.
