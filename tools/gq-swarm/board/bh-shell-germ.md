# bh-shell-germ

**Target:** the germ-group gate of the shell route: for which P, nu is Q_nu finitely presented?

**Landed.**
- ab095480c `fp-window-group-makes-shell-germ-group-fp` (+ `fp-window-group-shell-germ-proof`):
  the finite window inclusion identifies R_nu as the mapping torus W_N *_psi of the window
  group W_N = <c_0..c_N>, psi = conj by s^-eps. So W_N finitely presented => R_nu, F_nu and Q
  all finitely presented: the two-clause gate collapses to ONE clause.
  - Calibration: P = Z zigzag gives eps = -1, N = 0, W = Z, psi = inversion, R_nu = Klein
    bottle group, Q fp. Criterion is not vacuous.
  - Corollary (new fact): for the Z^2 square spiral, W_2 is fg metabelian and NOT fp
    (contrapositive of the landed non-fp result for R_nu).
- 0c0d638dd Attempts 1-2 on the same node: window-zero direct product dead (accessible index
  count); commuting copies at window one reduce to the same affine shape, so a fp window group
  needs non-abelian junction corrections.

**Status:** no positive example found. Target is now exactly: P not virtually cyclic + an
enumeration with the finite window + W_N finitely presented, with non-abelian junctions.

**Not claimed:** nothing about finite presentation of E_nu itself; item 2 is sufficient, not
necessary (a mapping torus can be fp over a non-fp fg base).
