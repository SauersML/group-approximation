---
rg: 2
id: row29-one-relator-group-is-hyperbolic-and-virtually-special
kind: claim
title: The last length-15 unpeelable one-relator group <a,t | AAttATaTAttaaTT> is hyperbolic and virtually special
distinct_from:
  unpeelable-extreme-one-relator-groups-sofic: that is the open soficity claim for the whole unpeelable class; this settles one member, the census row 29, by Linton's Z-stable hierarchy criterion.
  row29-magnus-subgroups-have-no-intermediate-rank-two-overgroups: that is a subgroup-lattice fact ruling out one amenable-envelope shape for the same group; this proves hyperbolicity and virtual specialness directly.
artifacts:
  - research/artifacts/one-relator-magnus-row29-2026-09-13.md
  - research/artifacts/one-relator-magnus-row29-scripts/lintonstab.py
  - research/artifacts/one-relator-magnus-row29-scripts/monocycles.py
  - research/artifacts/one-relator-magnus-row29-scripts/algext.py
  - research/artifacts/one-relator-magnus-row29-scripts/pb_AB.out
  - research/artifacts/one-relator-magnus-row29-scripts/pb_AA.out
  - research/artifacts/one-relator-magnus-row29-scripts/pb_BB.out
  - research/artifacts/one-relator-magnus-row29-scripts/monocycles.out
  - research/artifacts/one-relator-magnus-row29-scripts/lintontree.v2.out
---

**Claim.** Let `G = <a, t | AAttATaTAttaaTT>`, the one class of the length-15 unpeelable
residue left uncertified by the virtual-fibring census
(`research/artifacts/or-length15-residue-2026-09-13.md`). Then `G` is hyperbolic and virtually
special.

**Normal form.** With `a_h = t^h a t^(-h)`, the Magnus rewriting is
`W_0 = a_0^(-2) a_2^(-1) a_1 a_0^(-1) a_2^2`. So `a_1 = u = y x^2 y^(-2) x` with `x = a_0` and
`y = a_2`, and

    G = F(x, y) *_psi,   A = <x, u>,  B = <u, y>,  psi(x) = u,  psi(u) = y.

This is the one-relator splitting of `G` along the exponent sum of `t`. Its vertex complex has
relator `W_0`, in which `a_1` occurs once, so `W_0` is primitive and the hierarchy has length one
and ends in the free group `F(x,y)` (as in Linton's Examples 1.2 and 6.12).

**Remark (not part of the claim).** Virtually special groups virtually embed in right-angled Artin
groups (Haglund–Wise), so they are linear over `Z` and residually finite, hence sofic. This is quoted
in `hyperbolic-cubulated-rf-citation` and was not re-checked here, so no soficity claim is landed on
top of it. With that import, every class of the length-15 unpeelable residue is sofic: 29 by
virtual-fibring certificates and row 29 by this claim. The umbrella claim
`unpeelable-extreme-one-relator-groups-sofic` covers all lengths and stays OPEN.

No novelty is claimed for the method. The group is one census member.
