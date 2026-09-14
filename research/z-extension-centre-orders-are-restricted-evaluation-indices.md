---
rg: 2
id: z-extension-centre-orders-are-restricted-evaluation-indices
kind: claim
title: In a central Z-extension, the centre's orders in finite quotients are exactly the indices of the extension class evaluated on images of H_2 of finite-index subgroups
distinct_from:
  ghb7-finite-index-z-extension-center-survives: that is the open survival premise for GHB_2(7); this is the general identity computing survival orders for any central Z-extension of any group
  kazhdan-cover-models-round-iff-kernel-fixed-mass-one: that decides rounding of models pulled back from a Kazhdan cover by the kernel's fixed mass; this computes which orders the central kernel reaches in finite quotients, the input those models need
---

**ESTABLISHED.** Let `1 → Z = <z> → K~ → K → 1` be a central extension of a finitely generated group `K` with class
`c ∈ H^2(K; Z)`. For a finite-index subgroup `N <= K`, let `M <= K~` be its preimage,
`i : N → K` the inclusion, and

```text
e(N) = [ Z : c(i_* H_2(N; Z)) ]  ∈  {1, 2, ...} ∪ {∞}.
```

Then:
1. **Local identity.** The image of `z` in `H_1(M; Z)` has order `e(N)`.
2. **Global identity.** If `c(H_2(K;Z)) != 0`, then `e(N)` is finite for every `N`, and
   `sup { ord(image of z) : K~ → Q finite }` equals `sup_N e(N)`, the supremum over finite-index
   (equivalently, finite-index normal) subgroups `N` of `K`.
3. **Scaling.** For an integer `m != 0`, `e_{mc}(N) = |m|·e_c(N)`. So unboundedness of the centre
   orders depends only on the ray of `c` in `H^2(K;Q)`.

DERIVATION
z-extension-centre-orders-evaluation-index-proof
