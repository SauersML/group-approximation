# bh-relhyp board
**Landed (lane proofs, not reviewed):**
- `rel-hyperbolic-groups-embed-with-fp-simple-peripherals` (+ `-proof` route): G relhyp ↪ Ĝ relhyp relative to chosen f.g. overgroups S_i ⊇ P_i (Dahmani Thm 0.1(2), read at source); Ĝ fp if S_i fp and G fp relative to P_i.
- `rel-hyperbolic-bh-permanence-implies-free-product-closure`: permanence ⇒ free-product closure of 𝓑 (⇒ JE ∧ FZ, open).
- `rel-hyperbolic-groups-with-bh-peripherals-satisfy-bh` OPEN, Attempt 1 with gate (RB).
- artifact gq-bh-bh-relhyp-attack.md.
**Needs:** (RB) — relative analogue of BBMZ Thm 4.1: G hyperbolic relative to fp simple S_i inside a finite germ extension of a full contracting RSG, singular set = parabolic points, germ groups (B)_p × S_i, BHM finiteness + simplicity hypotheses.
**For bh-permanence / bh-3manifold / bh-hhg:** relhyp permanence is at least as hard as free-product closure; relhyp 3-manifold groups left to bh-3manifold.
Status: stalled per stall rule after one real attempt.

**Free mode (09-18 ~09:40), direction:** build hosts myself; found an algebraic one (amalgams over centralizers inside relative holomorphs).
**Landed (lane proofs, not reviewed, no priority claimed):**
- 5f58f288e: `centralizer-amalgams-are-free-permutational-wreaths`, `centralizer-amalgams-embed-in-relative-holomorphs` (any G, finite F, P ≤ G: G *_{C_G(F)} (C_G(F) × P) ≤ (G*Z) ⋊ Aut_G(G*Z)), `pbh-class-closed-under-centralizer-amalgams` (B_A closed under M *_{C_M(F)} (C_M(F) × P); extensions of centralizers), `cusp-extensions-of-torsion-free-hyperbolic-groups-satisfy-pbh`.
- 66b7fa58e: second route via BFFHZ Thms C+E only (Aut_G(G*F_2)).
- b333f574f: `limit-groups-over-hyperbolic-groups-satisfy-boone-higman` (all f.g. subgroups of Γ^{Z[t]}, Γ torsion-free hyperbolic or KM class 𝒢 ∩ B_A; KM JEMS 2012 Thm C read at source).
- 7656daa3d: Attempt 2 on the OPEN relhyp permanence node.
**For bh-3manifold / bh-permanence / bh-free-extensions:** centralizer amalgams are now a B_A closure; twisted version G *_C (K ⋊ C) sketched in artifact (unlanded) for graph-manifold gluings — blocked by non-primitive leaf boundary curves.

**Round 3 (09-18 ~10:20), per coordinator:**
- 47de9b954: `pbh-coset-condition-passes-to-finite-index-overgroups` (finite set-stabilizers of G/C are good; item 2 = bh-openq-papers' closure part 1, found independently) and `cusp-extensions-of-rel-hyperbolic-groups-satisfy-pbh` (any rel hyp G ∈ B_A, TORSION allowed, cusps E(g_i)×K_i along non-commensurable loxodromics ⇒ B_A + rel hyp).
- a9eb99a8b: `pbh-graphs-of-groups-over-realized-good-edges` (vertex groups in one D ∈ B_A, edges realized by conjugation, edge images good ⇒ π_1 ∈ B_A; generalizes bh-free-10 parts 4–5 to infinite good edges, whole graphs) and `rel-hyperbolic-permanence-implies-finite-edge-amalgams` (both forms of relhyp permanence ⇒ finite-edge amalgam/HNN closure; B_A form ⇒ bh-free-10's open conjugacy step).
- bbf0d7d43: Attempt 4 (Dehn filling ⇒ free permutational product over finite P̄): the naive map fails on Z²*_{a=w}F_2.
**For bh-3manifold:** product ambient groups D = ∏F_v realize only flip gluings; see artifact "Graph manifolds" (route: normalizers of tori in linear reps of an NPC model).
Status: done for this round.
