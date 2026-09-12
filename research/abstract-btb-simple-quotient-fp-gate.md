---
rg: 2
id: abstract-btb-simple-quotient-fp-gate
kind: claim
title: The canonical simple quotient of a finitely presented abstract twisted Brin-Thompson group is finitely presented exactly when the faithful action image is
distinct_from:
  twisted-brin-thompson-finite-presentation-criterion: that characterizes finite presentability of the possibly nonfaithful ABSTRACT group from finiteness properties of the original actor and action; this characterizes finite presentability of its canonical SIMPLE quotient and shows that passing through the abstract group does not remove the action-image finite-presentation hole.
  bffhz-action-image-is-finitely-presented: that universal computable-core upgrade is refuted; this is a general conditional equivalence for a specified action and remains valid independently of that failed upgrade.
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
the resulting simple quotient is equivalent to finite presentation of the
specified action image. The universal computable-core assertion is now
refuted by `bffhz-computable-core-fp-upgrade-is-false`; this conditional
equivalence neither supplies it nor assumes that it holds universally.

The abstract setting matters: `cantor-prefix-subgroup-detects-every-normal-kernel`
shows that a homomorphism from a faithful Cantor homeomorphism group
containing V_m cannot kill a nonidentity homeomorphism while preserving
V_m faithfully. The canonical abstract quotient here should not be
replaced by an unsupported coefficient-forgetting map between faithful
full groups.
