---
rg: 2
id: free-factor-phase-graph-hnn-is-residually-finite
kind: claim
title: Phase-graph HNNs between free-factor supports are residually finite
artifacts:
  - research/artifacts/signed-hecke-common-type-normalization-2026-08-20.md
distinct_from:
  phase-coordinate-switch-hnn-is-residually-finite: that moves two whole direct-product coordinates; this permits the faithful support to be a proper free factor at both ends.
  partial-phase-graph-hnn-is-residually-finite: that keeps the same ambient faithful coordinate at both ends; this moves between two different ambient free groups and synchronizes their finite free-factor quotients.
  free-phase-context-support-is-a-proper-free-factor: that proves the support arising in the signed-Hecke cell is exactly a proper free factor; this applies residual-finiteness permanence to HNN transports between those natural supports.
---

Let `A,L_0,L_1` be finite-rank free groups and let
`j_nu:A -> L_nu` identify `A` with a free factor of `L_nu`, for `nu=0,1`.
Let `P` be finitely generated and residually finite, and let
`Theta_0,Theta_1:A -> P` be arbitrary.  In

```text
B=L_0 times L_1 times P
```

put

```text
G_0={(j_0(a),1,Theta_0(a)):a in A},
G_1={(1,j_1(a),Theta_1(a)):a in A}.                    (FFG1)
```

Then the HNN extension of `B` identifying `G_0` with `G_1` through the common
parameter `a` is residually finite.

In particular, `(FPS1)--(FPS4)` cannot close a signed-Hecke chord by directly
identifying the natural rank-`D-1` free-factor supports at two endpoints, even
if arbitrary auxiliary phase homomorphisms are attached on both sides.  The
decisive associated subgroup must be embedded non-primitively at least at one
end, mix several faithful coordinates in a way not reducible to one free
factor, or leave the HNN/free-phase framework.
