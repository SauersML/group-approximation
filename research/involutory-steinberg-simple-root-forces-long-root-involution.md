---
rg: 2
id: involutory-steinberg-simple-root-forces-long-root-involution
kind: claim
title: One involutory simple root and one Steinberg centrality force the long root to be involutory
distinct_from:
  involutory-opposite-root-face-obeys-projective-transfer: that consumes involutivity of the two opposite long-root variables in the rank-one denominator word; this supplies each such involutivity from a genuine rank-two Steinberg commutator packet.
  root-additivity-eliminates-the-s3-rank-one-leak: that analyzes exact assignments in S3 and uses opposite-root additivity; this is a dimension-free normalized-Hilbert--Schmidt estimate in arbitrary matrices using a shared rank-two root.
  arithmetic-hexagon-decoding-or-conductor-leakage: that must decode and synchronize an entire six-chamber carrier at arbitrary conductor; this closes only the bottom involutory simple-root stratum with one A2 chamber relation.
---

Let `p,q,a` be unitaries in a finite matrix algebra, let

```text
c=[p,q]=p q p^* q^*,
gamma=||a-c||_2,
kappa=||p a p^*-a||_2,
sigma=||p^2-I||_2.                                      (ISR1)
```

Then

```text
||a^2-I||_2 <=4 gamma+kappa+2 sigma.                    (ISR2)
```

Thus the exact Steinberg packet

```text
a=[p,q],       [p,a]=1,       p^2=1                    (ISR3)
```

forces `a^2=1`. Notice that no order relation on `q` is needed.

This is the first genuine rank-two layer beyond the rank-one `S_3` audit.
Apply it in the upper chamber with
`p=x_12(1)`, `q=x_23(1)`, `a=x_13(1)`, and in the opposite chamber for
`b=y_31(1)`. Feeding the two resulting bounds into
`involutory-opposite-root-face-obeys-projective-transfer` gives an explicit
dimension-free cascade from simple-root exponent-two defect, Steinberg-word
defect and shared-root centrality to the target denominator commutator.

The scope is deliberately sharp. Deep dyadic root strata have `p^2` far
from one, so `(ISR2)` does not close them. It proves that a surviving packet
must carry positive deeper-conductor mass in at least one of the two
opposite A2 chambers; that is precisely the mass the open arithmetic
hexagon decoder must synchronize or charge as leakage.

