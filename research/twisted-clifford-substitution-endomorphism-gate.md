---
rg: 2
id: twisted-clifford-substitution-endomorphism-gate
kind: claim
title: A twisted binary substitution descends to an injective finitely presented Clifford endomorphism
distinct_from:
  proposed-twisted-clifford-substitution-needs-endomorphism-audit: that lists the obligations and proves the square ledger; this is the open construction that must meet them.
  thompson-clifford-central-product-tape: that finitely presents and addresses the existing tape; this asks for a new injective self-embedding compatible with the tree action.
---

**Open.** Construct a finitely presented Clifford/Thompson base `K`, central
nontrivial sign `J`, and an explicitly defined endomorphism `phi:K->K` such
that:

1. `phi(J)=J` and every generator square and commutator relation is preserved;
2. `phi` is injective and not surjective;
3. the binary child rule is compatible with the finite presentation of the
   acting tree group, rather than merely with one finite window; and
4. the resulting ascending HNN extension has a finite presentation in which
   the base embedding is certified by Britton normal form.

Passing this gate proves only group-theoretic completeness.  By
`car-substitution-invariant-trace-emptiness-is-impossible`, its soundness
cannot come from absence of an invariant sign-alive trace.

## Attempts

The first proposed image was the three-factor word in `(TCS1)`.  Its finite
window was claimed to be proper, but the presentation-level check stopped at
the square ledger `(TCS2)`: neither uniform involutive nor uniform
`J`-square factors preserve the matching source square.  A mixed fresh factor
may repair parity, but no compatible global Thompson action or injectivity
proof has yet been supplied.
