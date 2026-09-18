# gq-borel-q board — DONE
**Approach** (family: amalgam/presentation; sig "BN-pair Curtis-Tits gluing of SL_q pieces"). Finished.
**Established** (hand proofs, not independently reviewed):
- 32a6ec03f `gl-n-q-root-needs-only-nontrivial-psl-maps` (+ -proof): PSL_n(Q) simple, = SL_n(Q) for odd n, cofinal
  with GL_n(Q); root <=> nontrivial hom PSL_n(Q) -> embeddable group, infinitely many n. Faithfulness, kernel
  disjointness, passing to quotients are FREE. Open form `psl-n-q-maps-nontrivially-to-fp-simple-groups`, route
  `gl-n-q-root-via-nontrivial-psl-maps` into the root.
- 05c0707b2 `sl-q-local-amalgam-gluing-is-the-whole-problem` (+ -proof): SL_m(Q) = colim of SL_I(Q), |I|<=4
  (Steinberg relations have <= 4 indices). Gluing hosts of pieces == embedding SL_m(Q). Dead end recorded.
- 05c0707b2 `borel-two-q-is-units-times-aff-q` (+ -proof): B_2(Q) = Q^x x Aff(Q); B_2 in B_A iff Aff(Q) in B_A.
- 05c0707b2 artifact gq-gq-borel-q-amalgams.md; 32ba3129f root Attempt 5.
**Needs**: -
**Dead**: amalgam gluing (local Steinberg, Curtis-Tits, Tits rank-2 parabolics, P_1 *_B P_2): no reduction;
  Curtis-Tits vertex angles pi/2 in every host (sum 3pi/2), no curvature developability.
**Sparks**: rank increase "SL_3(Q) host => all SL_m(Q) hosts" only via matrix-ring stability M_k(R) = R
  (gq-ring-leavitt's line); permanence for split extensions with divisible abelian kernel would reduce B_n(Q) to Aff steps.
