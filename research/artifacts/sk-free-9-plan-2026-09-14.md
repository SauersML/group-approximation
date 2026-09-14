# sk-free-9 plan: the strongest short addition to the simple Kazhdan note (2026-09-14)

Lane sk-free-9 (wave 12, free lane). Target: `simple_kazhdan_sofic_group.tex` rev4.3 (main 696c4b602e, md5 0648e5f8…). Constraint: at most 6 printed lines, a complete short proof, reviewed inputs.

## Candidates weighed
1. **Converse to Theorem 1, chosen.** The simple limits of the paper's own finite simple models are exactly the groups G_X. Reviewed inputs on main:
   - `generic-limit-of-subshift-sl-models-is-simple-kazhdan`: sk-verify-15 PASS, sk-verify-16 PASS;
   - `subshift-algebra-groups-embed-in-marked-groups`: sk-verify-3 PASS;
   - the note's own word-problem criterion (§4).

   The whole proof is two facts: triviality in the models depends only on the cyclic windows of the periodic word, and a proper closed invariant subset gives a level subgroup. It makes the title's clause canonical: G_X is not one example among limits of SL_{3N}(F_2), it is exactly the simple part of the boundary of that family.
2. **Marking-free expanders.** Every sequence of finite groups converging to G_X eventually forms expanders, for any marking, by openness of (T) (Shalom); `kazhdan-marked-limits-eventually-uniform-expanders`, sk-verify-14 PASS. It costs 1–2 lines plus a bibitem. It is general folklore-level and makes the paper's explicit expander clause look less special. Optional, secondary.
3. **Rejected:**
   - C*(G_X) not QD (sk-free-5 T4, PASS). Likely folklore through Bekka–Valette, and off the approximation theme.
   - Thue–Morse non-uniform growth, conjugacy degree, 78 elementary matrices, characters. Each proof is too long for 6 lines.
   - One host with solvable WP containing all LEF groups with solvable WP. False: no decidable host.
   - Additional printed questions. sk-answered-questions swept 25 sources and found none beyond the lineage.

## Deliverable
`research/artifacts/sk-free-9-proposal-2026-09-14.md`: verbatim LaTeX (≤ 6 printed lines, placed at the end of §4 after the word-problem proof), a derivation check, model tests and a length estimate. No new Cairn claim: the content is `generic-limit-of-subshift-sl-models-is-simple-kazhdan`, whose statement subsumes it. The note text goes to the verifier queue.
