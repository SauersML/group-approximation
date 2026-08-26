---
rg: 2
id: signed-l0-does-not-attach-cross-returns-to-order-seven-head
kind: claim
title: Signed L0 conjugacy does not attach the authenticated cross returns to the order-seven head
artifacts:
  - experiments/order_seven_head_return_conjugacy_audit.py
  - research/order-seven-head-return-conjugacy-audit-proof.md
distinct_from:
  cross-whitehead-sandwiches-branch-roots-into-signed-normalizer: that finds exact branch-root returns into the signed normalizer; this tests whether their literal root positions can be conjugated to either factor of the order-seven head.
  native-whitehead-hecke-head-has-order-seven-anchor: that proves `(J_1B_2A_1)^7=1` on the native three-corner packet; this proves the returned occurrences are not the native `A_1,B_2` occurrences and so the order-seven relation cannot be applied to their reservoir gauges.
  fused-authenticated-cross-returns-retain-s3-square-gauge: that fuses the two returned coefficients to a constant normalizer root; this exhausts signed-`L_0` root-position conjugacy to the individual head factors before fusion.
---

**ESTABLISHED ORDER-SEVEN ATTACHMENT NO-GO.**  In source-to-target
notation, the two branch-zero incoming return roots have positions

```text
k->8,       k in {6,9},                                (OHC1)
```

whereas the first order-seven head arm

```text
A_1=x_47(r)                                             (OHC2)
```

has position `7->4`.  Close the ten constant signed-`L_0` generators to
all `8192` matrices and conjugate the two transvections in `(OHC1)` by
every element.  Neither orbit contains `7->4`.  Indeed, among all `42`
elementary transvections, the elementary part of each orbit is

```text
Orb_(L_0)(6->8) intersect Roots={6->8},
Orb_(L_0)(9->8) intersect Roots={9->8}.                 (OHC3)
```

The same exact test on the returned positions gives

```text
Orb_(L_0)(6->7) intersect Roots={6->7},
Orb_(L_0)(9->7) intersect Roots={9->7}.                 (OHC4)
```

Thus coefficient equality with `r` does not identify the occurrence with
`A_1`: no signed-`L_0` word conjugates either authenticated input or output
position to the native arm position.

The depth-two factor

```text
B_2=x_84(b_2),          b_2=s_00t_1                    (OHC5)
```

does not repair the mismatch.  Exhausting the `48` prefix monomials whose
two prefix lengths are at most two, for both `K_i` and both `k`, finds only
four conjugations with a single output coefficient `b_2`:

```text
K_0x_(8,k)(b_2)K_0=x_(8,k)(b_2),
K_0x_(8,k)(s_10t_1)K_0=x_(7,k)(b_2),       k in {6,9}. (OHC6)
```

The first row is position-preserving.  The second is a genuine depth-two
coefficient return, using `p(s_10t_1)=s_00t_1`, but neither its input
position `k->8` nor its output position `k->7` is signed-`L_0` conjugate to
the native `B_2` position `4->8`.  The elementary part of the latter's own
orbit is likewise only `{4->8}`.

Consequently the order-seven relation cannot be combined with the
order-three return gauge by a coprime-order argument: the two relations act
on different, un-identified reservoir factors.  No single gauge is shown
to have both orders three and seven.  A successful attachment must add a
new ordinary word outside signed `L_0` that moves one of the exact return
positions to the native head occurrence while preserving its carrier.

No Property T, Kazhdan input, trace hypothesis, literature theorem, local
computation, or Lean compilation is used.

DERIVATION
order-seven-head-return-conjugacy-audit-proof
