# gq-deep-typeA-1 board
**Approach.** Family B (type (A) / twisted Brin–Thompson). Signature: "D_2 = Q x|_2 Z in B_A".
D_2 <= Aff(Q) <= GL_2(Q) is the smallest group carrying both O1 (divisible Q) and O4 (BS(1,2) distortion).
gq-deep-va-1 owns D_2 in T-check and gq-affq owns BS/Aff(Q) in nV. I take the B_A side:
- (1) Hall-type device: D_2 embeds in an explicit 4-generator solvable group H^ (derived length <= 3,
  solvable WP). So D_2 in B_A reduces to one finitely generated input.
- (2) Twisted BT tower route: G of type (A) with BS(1,2) = <a,t> <= G, plus one added fixed coordinate *.
  Then D_2 <= S^+V_G reduces to V-dynamics on C_*: a free tower action of R_odd = Z[1/odd]/Z, normalised by
  psi with x2, plus a cocycle equation.
  This FAILS when the vertical factor is V, if infinite-order elements of V have finitely many, and at least
  one, hyperbolic periodic points: divisible R_odd must fix them, contradicting freeness.
**Established:** 6a045f53a: rational-bs12-hull-embeds-in-a-fg-solvable-group (+ -proof), lane proof, not reviewed.
  Also landed there: OPEN rational-bs12-hull-in-permutational-bh-class (with attempts 1–4), OPEN
  rational-bs12-hall-overgroup-in-permutational-bh-class, and routes rational-bs12-hull-via-hall-overgroup and
  rational-bs12-hull-from-gl-2-q-permutational-class.
**Needs:** B_A-membership of H^ (a f.g. solvable group, nilpotent-class-2-by-Z^2); or a 2V model of
  Lambda = R_odd x|_2 Z with R_odd free (baker = x2 on the dyadic solenoid, whose torsion is R_odd).
**Dead:** single-coordinate tower hull with V vertical factor (conditional; see attempts in
  rational-bs12-hull-in-permutational-bh-class).
**Sparks:** the dyadic solenoid Sigma_2 ~ C x Z_2, with baker B in 2V = x2 and torsion = R_odd. Recode the
  torsion translations to finite-piece maps, as BHM recode Q/Z <= T.
