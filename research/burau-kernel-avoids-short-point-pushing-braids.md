---
rg: 2
id: burau-kernel-avoids-short-point-pushing-braids
kind: claim
title: No nontrivial 4-strand point-pushing braid of free length at most 24 lies in the Burau kernel
distinct_from:
  four-strand-burau-representation-has-nontrivial-kernel: that claim is the existence of some nontrivial 4-braid with identity Burau matrix; this claim is a finite exclusion, ruling out kernel elements of free length at most 24 in the point-pushing subgroup K_4
  brunnian-four-braids-avoid-burau-kernel: that claim is injectivity of Burau on all of Brun_4; this claim covers only elements of K_4 of free length at most 24, by exhaustive computation
artifacts:
  - research/artifacts/zp-burau-k4-kernel-search-2026-09-13.md
  - research/artifacts/zp-burau-k4-kernel-search-2026-09-13.py
---

Let `K_4 ⊂ B_4` be the point-pushing subgroup of `p_4`, free on
`A_{14} = sigma_3 sigma_2 sigma_1^2 sigma_2^{-1} sigma_3^{-1}`,
`A_{24} = sigma_3 sigma_2^2 sigma_3^{-1}` and `A_{34} = sigma_3^2`.
If `w` is a nontrivial reduced word of length at most 24 in these generators
and their inverses, then `rho_4(w) != I`, where `rho_4` is the Burau
representation.

By Long's theorem
(`burau-faithful-iff-faithful-on-noncentral-normal-subgroup`), any nontrivial
Burau kernel meets `Brun_4 ⊂ K_4`. So this is a lower bound on the free
length of a kernel element in the region that matters.

Proof: exhaustive meet-in-the-middle enumeration with exact re-checking.
See the route `burau-kernel-avoids-short-point-pushing-braids-proof` and the
artifact.
