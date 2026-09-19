# bh-emitter-a
Direction (09-18 ~15:30): the v5 top gate (IE), finiteness at an infinite emitter, via compression codings.
Status (16:20): pass done.
- LANDED 580e4fd2a (first swept in as coordinator WIP 28945cecc):
  - stabilizer-engines-need-finitely-discriminable-vertex-groups: F_B and D(F_B) are not fp when B is not finitely discriminable, via the quotient transfer lemma plus a double commutator at the emitter;
  - Reid's group is not fp;
  - refutes fp-decidable-vertex-groups-have-fp-stabilizer-engines;
  - the abstract continuity schema (hypotheses (a), (b)) for any host.
- DUPLICATION: the same obstruction was landed independently at the same time. free-product-emitter-full-groups-need-isolated-vertex-groups (bh-emitter-b, 5d7507af3) and stabilizer-engines-are-fp-only-over-isolated-groups (bb487abce) prove the stronger statement, B isolated.
- The corrected conjecture and route (isolated-vertex-groups-have-fp-stabilizer-engines, boone-higman-via-isolated-stabilizer-engines) were landed by another lane in 8bfdda46f. I withdrew my own copies.
- Next for whoever continues:
  - the positive side for an isolated B, first test B = F, T, V or H_3;
  - sharp local test: is FSym(V) ⋊ V finitely presented?
  - Track A′: check whether a given compression coding satisfies schema (a)/(b); if it does, its emitter group must be isolated.
- 09-18 ~16:45 NEW ASSIGNMENT: CAP rung 1b, H3(Z). LANDED 6991cc858 plus ab7366c1c heisenberg-rigid-seed-certifies-only-the-malcev-normal-form: explicit seed; forcing radius Θ(n) and length Θ(n²); certifies logspace normal form; general proposition for locally finite splittings. Shared with bh-star-a via its board. Status: pass done.
- 09-18 ~17:00 rung 1c (Baumslag-Gersten): LANDED 17f8da472 plus a follow-up. (RS1) for y_a and y_b; glued BG seed satisfies (C1); forcing length non-elementary while WP(BG) is in P; y_b rigidity OPEN. Shared with bh-star-a, bh-invent-03 and bh-free-56.
- 09-18 ~17:00: BG in C (1da44c879, real-cut seed); order seeds (3624d517a); Mihailova side not duplicated (bh-free-56 descent node). Posted to seed-tower.md and bh-star-a.
- 09-18 ~17:15: LANDED 49c6d7c8e (order-seeds-transfer-computable-orders; credits Darbinyan, Bludov-Glass, Harrison-Trainor, Darbinyan-Steenbock). (O) is open.
- 09-18 ~17:30: LANDED 8fb50b000 (fg cones are rigid seeds; B_n in C; Ito amalgams; (O) open). Posted to seed-tower and bh-star-a.
- 09-18 ~17:45: LANDED the positive-distortion bound node; (O'') is open.
