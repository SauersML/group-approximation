---
rg: 2
id: anti-central-k0-states-can-be-chosen-transpose-invariant
kind: claim
title: The transpose-inverse automorphism fixes the signed Thompson group and swaps the semidihedral blocks, so K_0 states can be chosen with the lifted-trace split
distinct_from:
  twisted-leavitt-k0-states-can-be-chosen-halving-invariant: that averages a state along the halving map; this averages along the automorphism g -> (g^*)^(-1) as well, which fixes the signed Thompson group pointwise and exchanges the two faithful blocks of the depth-one semidihedral group.
  anti-central-k0-states-equal-lifted-trace-on-signed-thompson: that forces every state on finite subgroups of the signed Thompson group; this normalizes the one split that is not forced there.
artifacts:
  - research/artifacts/hadamard-spectral-conjugacy-and-forced-states-2026-09-12.md
---

**ESTABLISHED** (proof: route `transpose-invariant-k0-states-proof`; verification requested from `w4-vf-linear-b`, forwarded by `w3-vf-linear`).

Let `R = L_(F_3)(1,2)` with involution `s_i^* = t_i`, `G = R^x`, `S_- = eps_- F_3[G]`, and `alpha(g) = (g^*)^(-1)`.

1. `alpha` is an automorphism of `G`. It fixes the signed Thompson group `E x| V` pointwise, fixes `z`, `w`, `d`, and
   commutes with `delta(g) = s0 g t0 + s1 g t1`.
2. On the depth-one semidihedral group `SD = <w, d, h>`, `alpha` is the sign twist `h -> zh`. So `alpha_*` exchanges the
   evaluation block `c_1` and the twisted block `c_2 = -eps_-(1 + [wh] + [dh])` of `eps_- F_3[SD]`.
3. If `(K_0(S_-), [eps_-])` admits a state, it admits one that is invariant under `alpha_*`, satisfies `s o F_* = s/2`
   for the halving map, and has `s(c_1) = s(c_2) = 1/2`.

So the unforced split of `anti-central-k0-states-equal-lifted-trace-on-signed-thompson` can be normalized to its
lifted-trace value. Whether some state extends the lifted trace on every finite subgroup of `G` is open; that would
refute `ternary-anti-invariant-swap-corner-is-full`. Section 3 of the artifact.
