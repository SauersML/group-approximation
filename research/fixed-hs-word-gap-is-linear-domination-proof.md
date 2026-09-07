---
rg: 2
id: fixed-hs-word-gap-is-linear-domination-proof
kind: route
title: Retain scalar phases with two identity blocks and amplify the real trace
target: fixed-hs-word-gap-is-linear-domination
requires: []
artifacts:
  - research/artifacts/hs-word-gap-linearization-2026-09-07.md
  - experiments/hs_word_gap_amplification_check.py
  - research/artifacts/hs-word-gap-amplification-replay-2026-09-07.json
---

For every generator take U_s (+) conjugate(U_s) (+) I_d (+) I_d.
Every word v has normalized trace 1-e_v/4, where
e_v=||v(U)-I||_2^2 in [0,4]. Taking the k-th tensor power gives exactly
e_v'=2[1-(1-e_v/4)^k], hence e_v'<=(k/2)e_v.

When a=e_w>0 choose k=ceil(4/a). Bernoulli gives
(1-a/4)^k<=1/(1+ka/4)<=1/2, so e_w'>=1. The assumed gap applies in
dimension (4d)^k, giving eta^2<=(k/2)delta_R(U)^2. Since ka<=8,
a<=(4/eta^2)delta_R(U)^2, which is the claimed linear estimate.
For a=0 it is immediate. A linear estimate implies a fixed gap directly.

Apply the one-word argument to each generator to obtain the whole-tuple
version. The artifact proves the trace identities, handles endpoints and
the empty relator list, and distinguishes this conditional theorem from
the missing group-specific hypothesis. The finite replay only checks the
amplifier identities; it is not used to establish that hypothesis.
