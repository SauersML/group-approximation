---
rg: 2
id: wall-models-avoid-norm-microstates
kind: claim
title: Wall models stay flexibly far from the whole norm-microstate sector
distinct_from:
  kazhdan-asymptotic-commutant-transport: That claim is the transport statement itself, for one operator-norm asymptotic representation; this one is its flexible consequence for the wall, namely that a wall family cannot be corner-approximated in normalized Hilbert--Schmidt norm by any operator-norm asymptotic representation even after o(d_n) padding.
artifacts:
  - notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md
---

If `(pi_n,v_n)` is a relative wall, there is no operator-norm asymptotic
representation `rho_n:G->U(D_n)` with `D_n/d_n->1` and
`||p_n rho_n(g) p_n-pi_n(g)||_(2,d_n)->0` for every fixed `g`.

Consequently a wall model must carry multiplicative defect of order one in
**operator** norm on a corner of vanishing normalized trace, and must keep
doing so under every flexible correction.

**Independent confirmation.**  `kun-thom-clifford-extension-not-weak-mf`
proves, by an unrelated route, that the Kun--Thom Clifford extension has no
operator-norm microstates at all.  That is the strongest possible form of the
present claim on that particular group: not merely that a wall model must
avoid the norm sector, but that the sector is empty there.  The two results
are in different categories and neither uses the other, so this is a genuine
cross-check rather than a restatement -- and it coexists with
`kun-thom-clifford-cover-weakly-sofic`, since finite groups with bi-invariant
metrics are not matrix microstates.  This strictly strengthens the
conclusion of
`notes/TRUE_CLIFFORD_HYPERLINEARITY_FORCES_AMBIENT_HS_INSTABILITY.md`, whose
target class is only the exact finite-dimensional representations, i.e. the
zero-defect members of the same sector.
