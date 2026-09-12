---
rg: 2
id: rank-one-no-signaling-pairing-floor
kind: claim
title: Rank-one paired transport has a one-unit contextual failure floor from endpoint marginals alone
artifacts:
  - notes/FALSE_NONSIGNALING_PAIRED_QUOTIENT_SHORTCUT.md
  - notes/TRUE_ROBUST_PAIRED_QUOTIENT_HAMMING_FLOOR.md
distinct_from:
  common-self-map-law: that asks for one common self-map law on the full paired label spaces; this needs only shared endpoint marginals, but applies solely to a one-dimensional binary fiber.
---

Let `mu_00, mu_01, mu_11` be probability laws on `{0,1}^2`.  Think of them
as the three transport contexts on a rank-one perfect binary pairing, where
the two diagonal contexts require output `(1,1)` and the crossed context
forbids `(1,1)`.  Assume only the endpoint no-signaling equalities

```text
Pr_(mu_00)[X=1] = Pr_(mu_01)[X=1] = a,
Pr_(mu_01)[Y=1] = Pr_(mu_11)[Y=1] = b.                (RNS1)
```

Define their failure probabilities by

```text
p_00 = 1 - mu_00(1,1),
p_01 =     mu_01(1,1),
p_11 = 1 - mu_11(1,1).
```

Then

```text
p_00+p_01+p_11 >= 1.                                  (RNS2)
```

If the three context errors `e_ij` are averaged over uniformly random source
labels in `F_2 x F_2`, the nonzero source pair `(1,1)` has weight `1/4`, so

```text
e_00+e_01+e_11 >= 1/4,
max(e_00,e_01,e_11) >= 1/12.                           (RNS3)
```

Thus the exact no-signaling construction in
`perfect-no-signaling-pairing-box` genuinely needs pairing rank at least two.
The limitation is equally important: `(RNS2)` applies only after the group
gadget has exposed one shared rank-one relative coordinate and shown that its
three matrix transport contexts have the endpoint marginals `(RNS1)`.
