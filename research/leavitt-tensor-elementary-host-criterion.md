---
rg: 2
id: leavitt-tensor-elementary-host-criterion
kind: claim
title: A perfect unit subgroup of a finitely presented central simple algebra lies in a finitely presented simple elementary group once one unstable Steinberg kernel is finitely normally generated
distinct_from:
  central-simple-leavitt-tensor-unit-groups-are-simple: that proves simplicity of E_n(B ⊗ L) for n >= 3 and of the whole unit group when K_1 and K_2 vanish; this uses the first part only and adds finite presentation from finite normal generation of the unstable Steinberg kernel, with no K_1 hypothesis at all.
  leavitt-tensor-hosts-acyclic-steinberg-and-fp: that makes the Steinberg map an isomorphism once K_1 and K_2 of B ⊗ L vanish; this asks only that its kernel be finitely normally generated at one rank n >= 4, which that claim's hypothesis implies but does not require.
---

**ESTABLISHED.** Let `B` be a finitely presented central simple unital
`F_2`-algebra, let `L = L_(F_2)(1,2)`, put `R = B ⊗ L`, and let `S <= B^x` be
a perfect subgroup. Fix `n >= 4` and suppose that

    K_(2,n) := ker( St_n(R) -> E_n(R) )

is finitely normally generated in `St_n(R)`. Then `E_n(R)` is a finitely
presented simple group containing an isomorphic copy of `S`.

**What it removes.** Unlike `boone-higman-via-central-simple-leavitt-tensor-host`,
nothing about `K_1(R)` is assumed. The unit group `R^x` is never used as the
host, so `GL_1 = E_1` is irrelevant. The `K_2`-type hypothesis is weakened from
vanishing to finite normal generation of one unstable kernel.

**Scope.** The input must be perfect. For Boone--Higman that is free, because
`boone-higman-iff-infinite-simple-inputs` reduces the conjecture to infinite
simple inputs, and those are perfect.

DERIVATION
leavitt-tensor-elementary-host-criterion-proof
