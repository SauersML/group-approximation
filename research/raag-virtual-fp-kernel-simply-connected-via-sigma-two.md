---
rg: 2
id: raag-virtual-fp-kernel-simply-connected-via-sigma-two
kind: route
title: A finitely presented kernel puts the character in Sigma^2 of the finite-index subgroup, and a nonempty Sigma^2 forces L to be simply connected
target: raag-virtual-fp-kernel-forces-simply-connected-flag-complex
requires:
  - raag-finite-index-sigma-m-forces-connected-flag-complex
artifacts:
  - research/artifacts/zp-raag-virtual-kernels-2026-09-13-part2.md
---

Let `H ≤ A_L` have finite index and `ψ: H → Z` be an epimorphism with finitely presented kernel.
`H` is of type `F` (the finite cover of the Salvetti complex is a finite `K(H,1)`). By the
Bieri--Renz criterion, the kernel of an epimorphism from a group of type `F_2` onto `Z` is
finitely presented iff both `[ψ]` and `[−ψ]` lie in `Σ^2(H)`; in particular `Σ^2(H) ≠ ∅`. By
`raag-finite-index-sigma-m-forces-connected-flag-complex` with `m = 2`, `L` is simply connected.
Artifact part 2, Corollary 10.
