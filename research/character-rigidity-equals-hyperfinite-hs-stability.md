---
rg: 2
id: character-rigidity-equals-hyperfinite-hs-stability
kind: claim
title: For higher rank lattices with (T;FD), character rigidity, hyperfinite HS stability and robust (T;FD) are the same
artifacts:
  - research/artifacts/two-paper-ingestion-2026-08-19.md
distinct_from:
  el-r-polynomial-robust-spectral-gap: that is the single group EL_r(F_q[x]) having (T;FD)_rob, obtained from property (T) with no lattice input; this is the lattice equivalence of Dogon-Vigdorovich Section 8, which needs charmenability and does not apply to that group.
  steinberg-hyperfinite-hs-stable: that is hyperfinite HS stability of one Leavitt Steinberg cover; this is a general equivalence for higher rank lattices and asserts nothing about that group.
---

**Established by citation.**  Dogon--Vigdorovich, arXiv:2506.20843v2,
Theorem 1.4 (`thm:main_char_rig_INTRO` in the source):

> Let `G` be a center-free connected semisimple Lie group without compact
> factors and with real rank at least 2.  Let `Gamma <= G` be an irreducible
> lattice with property (T;FD).  The following are equivalent:
>
> 1. `Gamma` is hyperfinitely Hilbert--Schmidt stable;
> 2. `Gamma` is character rigid;
> 3. `Gamma` has property (T;FD)_rob;
> 4. characters of `Gamma` are pointwise limits of normalized traces of finite
>    dimensional representations.
>
> In particular, if `Gamma` is Hilbert--Schmidt stable, then it is character
> rigid.

Here character rigid means every character is either induced by a finite
dimensional representation or vanishes off the center, and (T;FD)_rob is the
robust variant of (T;FD), asserting uniform spectral gap across *almost*
representations.

**What it does for the Iwahori lane, which is negative and useful.**  It gives
a would-be refutation of `iwahori-local-global-defect-question`: stability
implies character rigidity, so a lattice failing character rigidity cannot be
Hilbert--Schmidt stable.  That refutation is unavailable for `SL_2(Z[1/2])`,
which is known to be character rigid by Peterson--Thom.  So the lane cannot be
closed cheaply from the negative side, and the equivalence also shows why:
hyperfinite stability is *strictly weaker* than stability and is already
implied by the known character rigidity, so all the remaining content of the
question lives outside the hyperfinite part of the trace simplex -- exactly the
fence that `steinberg-hyperfinite-hs-stable` records for the Leavitt group.

The proof uses charmenability of Bader--Boutonnet--Houdayer--Peterson, a
non-commutative analogue of Schramm's theorem on hyperfinite graph limits, and
a character-theoretic criterion for hyperfinite Hilbert--Schmidt stability.
None of those is separately imported here.
