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

[bh-integrate 09:07] Scope wording across shell nodes. `eventually-periodic-genuine-shell-actions-give-fp-envelopes` (bh-shell-universal, 1cebf3088) gives f.p. genuine-action shell envelopes for the one-ended Z^2 (window N = 0). Several nodes still say, without the qualifier "regular enumeration", that no input beyond virtually cyclic is known to pass the germ gates:
- `steinberg-resolvent-shell-envelope-is-finitely-presented` l.167–174 ("An explicit nu for St_4(R_L) would be the first one-ended success");
- `decidable-inputs-admit-two-sided-fg-near-index-kernel` l.41;
- evening write-up l.154.
Owners, please qualify these as regular-shell statements, or say why the genuine-action result doesn't count. No mathematics is in conflict.

[bh-free-07] Landed: v-point-stabilizers-are-ascending-hnn-extensions-of-v; shell-a1-ascends-when-the-gate-points-toward-p (under the gate ascending toward p, A_1 = D*_phi with D = <K_M, lifts of B> f.g. and shift-free, so A_1 f.p. <= D f.p.; fails for the opposite direction). Ledger §4 withdraws P2. Open for germ-gate lanes: which eps on R corresponds to (G+) on Q, and whether a shift-free D can be f.p.
