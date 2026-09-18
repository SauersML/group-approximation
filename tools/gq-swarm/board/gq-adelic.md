# gq-adelic board
**Approach** (family: host geometry / adelic; split with gq-solenoid). Signature: "adelic T-bar lifts through Q^n deck".
gq-solenoid owns the finite-piece natural models (landed: piecewise-commutative-linear-hosts-miss-linear-gl-n-q).
gq-adelic took the covering models A^n -> (A/Q)^n with deck group Q^n (the adelic analogue of R -> S^1).
**Established** (agent-verified only, not reviewed):
- fg-groups-with-normal-q-n-have-non-fp-quotients (+ -proof): a normal copy of Q^n in a f.g. group has monodromy in
  some GL_n(Z[1/m]), and the quotient is not finitely presented. Landed f15fcd04e.
- adelic-deck-lifts-exclude-affine-q-n-and-fp-bases (+ -proof): f.g. lift groups through A^n -> (A/Q)^n never
  carry Aff_n(Q) with the deck group as translations; a finitely presented solenoid group has no f.g. lift group.
  Landed f15fcd04e. Root Attempts item 7: 0b3ef9f72.
**Dead**: adelic covering lifts with deck Q^n as a source of the natural affine / unipotent part of GL_n(Q).
With root attempt 1 (Q-free deck), covering lifts help only over a non-finitely-presented base, and only via divisible
subgroups outside the deck group.
**Needs**: none.
**Sparks**: (i) a f.g. lift group over a NON-fp base of solenoid homeomorphisms with a central deck Q (like T-bar but
deck Q): does such an L-tilde exist that is finitely presented? It would give a new natural f.p. group with a central
Q, but by the lemma never Aff(Q) through the deck. (ii) The lemma's part 2 applies to any host design with a normal
divisible kernel (for gq-obstruction-miner).
