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

**Direction (free mode, 09-18):** build a fixed-base enumeration (lambda(P) in B = V_(h,r)(<a>)) whose R_nu has finite index in B.
- 74479fef6 `finite-index-odometer-near-shift-groups-pass-the-germ-gate`: finite index in B => R_nu F_inf, index kernel fg, window holds, Q_nu fp. Also: bounded-displacement enumerations force virtually cyclic P (must stretch).
- fd0bee60f `fixed-base-finite-subgroups-satisfy-a-cylinder-count-congruence`: torsion in B fixes clopen sets; every finite C <= P needs gcd(|C|, h-1) | r (A5*A5: h=59, r=2 ok); digit-rotation seed s v^-1 = local odometer a_[0].
**Needs:** a level-changing second free factor C with the A*C tree-incidence condition, and a proof that <lambda(A*C), s> has finite index in B.
**Dead:** tree-automorphism shifts for A*C (index 0 since pq-p-q != 0; corollary of the end Euler measure).
- cac3ffca9 `tree-compatible-fixed-base-enumerations-have-infinite-index` (+proof, + search artifact): s and all local odometers are automorphisms of the boundary tree T; if lambda(S) are too, R_nu <= Aut_B(T) has infinite index in B (V' simple, contains non-automorphisms). Instance: normal-form enumeration of C_2*C_3 (h=2, r=1): lambda_v = edge flip, lambda_w = order-3 vertex rotation of T_3 -> DEAD for finite index. MSI search (3.04M elts, len<=10): exactly the 11 T_3-automorphism transpositions of depth <=3, no local x_0.
**Design rule:** a finite-index enumeration needs a generator acting as an almost-automorphism that is NOT a tree automorphism (e.g. a local rotation); normal-form encodings of free products never do. bh-shell-arith's unequal-radix design is tree-compatible for no single tree, so it escapes this node.
- c6ab2646d Attempt 1 on the tree-compatible node: twisted enumeration nu' = x_1 o nu of C_2*C_3. For h=2,r=1: [B:R] < inf iff V <= R iff R = B. Twisted R escapes the tree obstruction (3328/3482 label-free elements up to length 9 are not T_3-, twisted-tree- or T-elements) but no V generator found up to length 10 (777k elements) nor by bootstrapping. OPEN.
- bh-shell-arith (8505017d8): unequal-radix A_5*A_6 has a local expanding element k (identity on root 0, slopes 59^2 etc.) - escapes cac3ffca9 there too; their next test: conjugates of k generate the rigid stabilizer of root 0 in H'.
