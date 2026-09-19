# bh-g3-topfree — does Track A need a free SFT, or only a topologically free one?

Status: pass done (09-18, after restart). Answer: topological freeness suffices on both sides.

Landed:
- 04ce18852 (pre-restart): master-route-needs-only-topological-freeness (ring route + group implication audit),
  boone-higman-via-leavitt-units-of-rigid-topologically-free-sfts (route), decidable-groups-lie-in-fp-topologically-free-crossed-products (E′),
  torsion-free-isotropy-leavitt-tensor-hosts-have-trivial-k1-k2 (K′), rigid-topologically-free-sfts-force-solvable-word-problem.
- 2914b739e: v-times-tree-boundary-full-groups-are-f-infinity (ESTABLISHED; scaffold host = Li product-SFT group, F_∞, simple, type (A));
  v-times-rigid-topologically-free-sft-full-groups-are-fp (OPEN gate E3′, with Stein–Farley audit);
  decidable-groups-lie-in-fp-groups-with-rigid-topfree-sfts (OPEN, E1′+E2);
  boone-higman-via-v-times-rigid-topfree-sft-full-groups (route, Track A group side).

Findings:
- Group side: F=A, simplicity (minimal + effective), type (A) (minimality only), Λ ↪ F (faithful) never use freeness;
  the Stein–Farley set-up of P2′ uses it only as uniqueness of local translation labels.
- Ring side: needs torsion-free isotropy for the K-gate (K′); group side needs no isotropy condition.
- E3′ has proved instances (tree scaffold, Ã₂); free-form P2′ has none.
- Known instances are finite-state Li codings ⇒ WP 2^{Cl²}; the open core is a non-finite-state rigid compression coding.

Next (for whoever picks this up): (1) can a rigid minimal topologically free SFT have an infinitely generated point
stabilizer, and would it matter for E3′? (2) hyperbolic groups: is the horofunction-boundary coding an SFT over Λ, and is
Λ⋉∂_h Λ a Li/Matui groupoid (BBMZ cone types)? That would give E3′ for all hyperbolic Λ.

## Pass 2 (09-18 ~17:00, coordinator: rigid compression coding that is not finite-state; coordinate with bh-e3prime)
- Left (SS-hard)_k to bh-e3prime (note: under (TF), and even under mere faithfulness, the vertex group of a
  finite-index-edge HNN acts faithfully on a locally finite rooted tree, so it is RF; complexity must come from
  an expanding injective virtual endomorphism of a hard fp RF group; product/automorphism/free-product
  constructions leave an invariant finite-index normal subgroup in the kernel).
- LANDED be079a987: sft-isolated-points-are-finite-state-across-finite-edge-groups (+ -proof). ESTABLISHED lane proof.
  Isolated points of SFTs over finite-edge splittings are finite-state recursions of vertex-group isolated points;
  virtually free ⇒ fg stabilizers; (F_n, C) ∈ 𝓡 ⟺ C fg; CAP for relative seeds reduces to one-ended groups (Dunwoody);
  tree light-cone collapse.
- Next: F_2 × F_2 with a Mihailova fiber product C_Q. A relative seed there is a locally forced two-sided
  labelling of Q. Decide whether it forces a solvable or bounded conjugacy-type problem in Q, or build one for a
  hard Q.
- 09-18 ~17:30 LANDED 5b30cefdb: mihailova-relative-seeds-must-force-across-both-factors (rows never factor-forced for
  M(Q), Q infinite non-free; bi-local criterion for (Q×Q, Δ_Q); (F×F, Δ_F) ∈ 𝓡). Also credited 25f6d41ba / 3379f8c7cc
  in the finite-cut node and fixed the referee's (UE) wording note. Coordinated on board/seed-tower.md.
  Next: 2-dimensional forcing for M(Q), or: do all glued seeds carry cellular right multiplication?
