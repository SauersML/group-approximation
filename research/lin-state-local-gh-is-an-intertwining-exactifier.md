---
rg: 2
id: lin-state-local-gh-is-an-intertwining-exactifier
kind: claim
title: Lin's displayed Gowers--Hatami dilation is a state-local intertwining exactifier
artifacts:
  - research/artifacts/lin-state-local-cross-gram-exactification-2026-08-23.md
distinct_from:
  lin-state-dependent-gh-preserves-the-commutant: that records Lin's stated compression estimate and exact commutant locality; this extracts the uncompressed state-local intertwining and left-carrier commutator identities from the displayed isometry.
  lin-canonical-dilation-twirls-unprotected-left-carriers: that computes the compressed Reynolds map and its no-go consequence; this gives the positive quantitative condition under which a left carrier is protected.
---

Let `K` be finite and let `phi:K->U(A)` be a state-dependent approximate
representation. For Lin's explicit isometry `V` and exact left-regular
representation `Phi`, every state vector `xi` satisfies

```text
E_a||(Phi(a)V-Vphi(a))xi||^2
 =E_(g,a)||(phi(g)phi(a)-phi(ga))xi||^2,               (SLI1)

||((U tensor I)V-VU)xi||^2
 =E_g||[U,phi(g)]xi||^2                                (SLI2)
```

for every `U in A`, while

```text
VB=(B tensor I)V                 for every B in A'.   (SLI3)
```

Consequently an approximately multiplicative finite packet may be
exactified on one Gram-selected state with exactly its original averaged
multiplication error, without moving any reference packet in the opposite
algebra. A left carrier is retained precisely to the extent measured by
its state-dependent commutator energy with the packet.

