---
rg: 2
id: positive-shift-trivializes-exact-combinatorial-soundness-proof
kind: route
title: Shift every term by a multiple of the identity and read off the combinatorial and rounder quantities
target: positive-shift-trivializes-exact-combinatorial-soundness
requires: [combinatorial-gap-and-rounder-give-energy-gap]
artifacts:
  - research/artifacts/qpcp-positive-shift-audit-2026-09-11.md
---

## Why sufficient

**(PS1)** Identity on the remaining tensor factors does not change the
support. Convexity gives `0<=h'_a<=I`.

**(PS2)** `h'_a>=epsilon I`, so `Tr(h'_a sigma)>=epsilon Tr(sigma)=epsilon`.
Hence the set of terms left unsatisfied must be all of `[m]`, and `s*(H')=m`.

**(PS3)** `H'=(1-epsilon)H+epsilon I`, so the spectrum moves affinely. Identity
(CR4) of `combinatorial-gap-and-rounder-give-energy-gap` with `s*=m` gives the
least rounder constant `m/(m lambda_min(H'))`.

**(PS4)** The map `x -> (1-epsilon)x+epsilon` is increasing.

**(PS5)** `W` is an isometry because the flag register is prepared in a fixed
unit vector. The `B_a` act on distinct flag qubits and commute. `W^*B_aW=I`,
and `I<=(1/epsilon)h'_a` by (PS2). The joint outcome is `[m]` almost surely, so
the cost clause reads `m<=(1/epsilon)sum_a Tr(h'_a rho)`, true by (PS2). For
`S` other than `[m]`, the kernel intersection over `a` outside `S` is zero, and
the joint projector pulls back to zero. (EX) quantifies over no terms.

**(PS6)** Given `sigma`, the set `S_sigma={a:Tr(h_a sigma)>eta}` is admissible,
so `Tr(H sigma)>=eta|S_sigma|/m>=beta eta`. If instead `sigma` is
`eta`-satisfying outside some `S`, then `Tr(H sigma)<=|S|/m+eta`, and
`lambda_min(H)>=b` forces `|S|>=(b-eta)m`.

Written out in Section 2 of the linked artifact.
