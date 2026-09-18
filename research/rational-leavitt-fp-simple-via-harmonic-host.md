---
rg: 2
id: rational-leavitt-fp-simple-via-harmonic-host
kind: route
title: If the harmonic Cuntz simple group is finitely presented, it contains the rational Leavitt simple group
target: rational-leavitt-simple-group-embeds-in-fp-simple-group
requires:
  - harmonic-cuntz-el3-is-fg-simple-over-all-gl-n-q
  - harmonic-cuntz-simple-group-is-finitely-presented
---

`Λ = L_Q(1,2)^x / Q^x` embeds in the simple group `Λ_h = EL_3(C_h)/Q^x`
(`harmonic-cuntz-el3-is-fg-simple-over-all-gl-n-q`, part 4). If `Λ_h` is finitely
presented, it is the required host.
