---
rg: 2
id: mub-sum-idempotents-have-uniform-cp-distance
kind: claim
title: The sum-minus-scalars idempotent of two orthogonal masas has exact UCP distance one third
distinct_from:
  bistochastic-channel-rounding-fails: That asks for near-idempotent UCP counterexamples; this proves that the proposed non-CP sum-of-masas idempotents cannot even be approximated by UCP maps.
  near-fixed-masas-round-channels-but-exclude-native-heat: That repairs one almost-fixed masa and excludes native heat; this computes the exact distance to all UCP maps for the idempotent associated with two orthogonal masas.
artifacts:
  - research/artifacts/mub-idempotent-exact-cp-distance-2026-09-12.md
---

Let `d>=2`, let `tau=Tr/d`, and let `D,C subset M_d` be maximal
abelian unital subalgebras with `E_D E_C=E_C E_D=E_0`, where
`E_0(x)=tau(x)1`. Equivalently their minimal-projection bases are
mutually unbiased. Set `Q=E_D+E_C-E_0`.

Then, with normalized Hilbert--Schmidt output norm,

```text
inf_(P:M_d->M_d UCP) ||P-Q||_(infinity->2) = 1/3.
```

The infimum is attained by the explicit self-adjoint bistochastic map
`P_*=(id+E_D+E_C)/3`. Thus the same infimum is obtained if the
competitors are required to be self-adjoint and bistochastic.

The lower bound allows arbitrary UCP competitors, without a common
eigenbasis, trace preservation, or self-adjointness. It uses the
nonnegativity of the Kraus mass orthogonal to `D+C`; no small-Choi-
eigenvalue inference is involved.

Consequently this family, even with dimensions and mutually unbiased
bases varying, cannot be the limit in mixed norm of the UCP maps
required by `bistochastic-channel-rounding-fails`. The unrestricted
rounding question remains open.
