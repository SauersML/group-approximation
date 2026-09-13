---
rg: 2
id: congruence-invisible-ideal-torsion-defect-step-proof
kind: route
title: Radical descent through the congruence kernel, then the absolute torsion-defect statement over the quotient ring
target: congruence-invisible-ideal-torsion-defect-step
requires: [finite-additive-order-one-sided-defects-are-mf-invisible]
artifacts:
  - research/artifacts/un-open-1-hilbert-hotel-radical-2026-09-13.md
---

Write `G = EL_n(R)` and `pi : G -> GL_n(R/J)` for reduction. Its image is `EL_n(R/J)`, since each
`e_ij(xbar)` lifts to `e_ij(x)`, and its kernel is `K = EL_n(R) n GL_n(R,J)`.

**Radical descent.** For a normal `N <= Rad_MF(G)`, `Rad_MF(G)` is the preimage of `Rad_MF(G/N)`.
If `g in Rad_MF(G)` and `th : G/N -> H` with `H` MF, then `th . pi` kills `g`. Conversely, if the
image of `g` lies in `Rad_MF(G/N)` and `th : G -> H` with `H` MF, then `N <= ker th`, so `th`
factors through `G/N` and kills `g`. Apply this with `N = K` and `G/K = EL_n(R/J)`.

**Over the quotient ring.** In `R/J` the pair `(sbar, tbar)` satisfies `tbar sbar = 1`, and its defect
`ebar` has `m ebar = 0`. The required claim gives `e_ij(ebar) in Rad_MF(EL_n(R/J))` for all `i != j`.
The radical is normal, so it contains `[e_ki(a), e_ij(ebar)] = e_kj(a ebar)` and then
`[e_kj(a ebar), e_jl(b)] = e_kl(a ebar b)` for distinct indices (`n >= 4` leaves room), signed
permutations move the index pair, and `e_ij(x+y) = e_ij(x) e_ij(y)` handles sums. So
`EL_n(R/J, (R/J) ebar (R/J)) <= Rad_MF(EL_n(R/J))`.

**Pull back.** `pi` sends the generators `e_ij(a)`, `a in ReR + J`, of `EL_n(R, ReR+J)` to
`e_ij(abar)` with `abar in (R/J) ebar (R/J)`, so `pi(EL_n(R, ReR+J))` lies in `Rad_MF(EL_n(R/J))`.
By descent, `EL_n(R, ReR+J) <= Rad_MF(G)`.
