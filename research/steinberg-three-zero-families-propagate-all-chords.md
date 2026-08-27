---
rg: 2
id: steinberg-three-zero-families-propagate-all-chords
kind: claim
title: The forced Steinberg zero families propagate through the two Fox rows to every chord
---

Assume `P=H=0`, both Fox recurrences, the source-slice identities `(SXTS2)`,
and the zero families `(SXTS3)`, `(SYZ1)--(SYZ3)`.  Then every chord value
`f(a,b,c)` is zero.

The known zero sets now include one complete point fiber and three affine
lines transverse to the rational maps.  The remaining task is a propagation
order in which each recurrence has at most one unknown predecessor,
including the exceptional denominators.  A proof closes the second half of
the marginal split; a counterexample would be an explicit residual
circulation satisfying both rows.

The initial zero set is now substantially larger than the three families:
`steinberg-zero-marginal-kills-b-minus-one-plane` kills the full plane
`b=-1` for every odd prime.  Its projective plane-transfer reaches every
nonzero `b` at `p=3,5`, proving the claim at those primes.  The uniform
problem is not merely an uncomputed orbit question:
`steinberg-plane-transfer-stalls-at-large-primes` proves that
the current transfer is a conditioned two-of-three rule and cannot make
its first move from the sole full-plane seed `b=-1` for any `p>=7`.
One more full-plane seed, a direct transfer, or a lemma upgrading one of
the two additional zero lines to a full plane is required.

This is a scoped refutation of single-transfer iteration, not of the
present claim.
