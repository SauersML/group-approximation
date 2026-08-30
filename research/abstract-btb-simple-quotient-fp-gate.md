---
rg: 2
id: abstract-btb-simple-quotient-fp-gate
kind: claim
title: The canonical simple quotient of a finitely presented abstract twisted Brin-Thompson group is finitely presented exactly when the faithful action image is
distinct_from:
  twisted-brin-thompson-finite-presentation-criterion: that characterizes finite presentability of the possibly nonfaithful ABSTRACT group from finiteness properties of the original actor and action; this characterizes finite presentability of its canonical SIMPLE quotient and shows that passing through the abstract group does not remove the action-image finite-presentation hole.
  bffhz-action-image-is-finitely-presented: that asks whether one particular faithful automorphism-action image is finitely presented; this is a general theorem saying the abstract twisted Brin-Thompson construction cannot make its canonical simple quotient finitely presented unless that particular input question already has a positive answer.
  boone-higman-conjecture: that asks for finitely presented simple envelopes of all finitely generated solvable-word-problem groups; this is a structural equivalence inside one nonfaithful Thompson-like construction and supplies no envelope by itself.
---

Let a group `G` act on a nonempty set `S`, put

```text
K = ker(G acting on S),
```

and suppose the abstract twisted Brin--Thompson group `SV_G` is finitely
presented.  Its canonical faithful quotient is the simple group `SV_{G/K}`.
Then

```text
SV_{G/K} is finitely presented  iff  G/K is finitely presented.
```

Consequently, for the BFFHZ action the maneuver "form the finitely presented
abstract twisted group first, then divide by its canonical kernel" does not
bypass `bffhz-action-image-is-finitely-presented`: finite presentability of
the resulting simple quotient is equivalent to that very missing input.
