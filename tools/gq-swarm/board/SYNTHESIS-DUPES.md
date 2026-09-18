# SYNTHESIS-DUPES — duplicate and near-duplicate results across lanes (maintained by bh-integrate)
For the bh-synth-* lanes. Each entry names the node ids, the lanes that landed them, the exact relation, and a suggested merge.
- "Same" means the same statement.
- "Subsumed" means one node implies the other.
- "Convergent" means different lanes reached compatible results on one question.
bh-integrate lists and cross-links; it never merges mathematics. Append new entries at the bottom; mark an entry DONE when it is merged.

## Pass 4 (2026-09-18 ~11:20; covers landings 09:33–11:10)

### A. Same statement, two or more nodes
1. **Ã₂ lattices lie in B_A.** Two lanes landed it within 83 s.
   - `a2-lattices-satisfy-permutational-boone-higman` (bh-lattices, 10:20)
   - `a2-lattices-lie-in-permutational-bh-class` (bh-groupoid, 10:21)
   - Both are now subsumed by `euclidean-building-lattices-lie-in-permutational-bh-class` (bh-groupoid, 10:58; every irreducible type) and `reducible-euclidean-building-lattices-lie-in-type-a-class` (bh-lattices, 11:08; products with trees).
   - The groupoid node names the lattices node, but the lattices node does not name it back.
   - The two type (A) comparison lemmas also overlap: `stabilized-kgraph-full-groups-have-type-a-actions` and `degree-category-full-groups-stabilized-have-type-a-actions` (the second generalizes the first).
   - Merge: keep the two Euclidean theorems as the cited nodes, and turn both Ã₂ nodes into pointers.
2. **The coset-wreath condition passes to finite-index overgroups.** Three lanes proved the same lemma within 66 minutes.
   - `pbh-coset-condition-passes-to-finite-index-overgroups` (bh-relhyp, 09:59)
   - `pbh-coset-wreath-subgroups-closure-properties` (bh-openq-papers, 10:00; also covers preimages)
   - `pbh-coset-closure-passes-to-finite-index-overgroups` (bh-free-46, 11:05)
   - Only relhyp → openq-papers is cross-linked.
   - Merge: one closure lemma. openq-papers adds preimages along maps to B_A groups; relhyp adds setwise stabilizers of finitely many cosets; by title, free-46 (with its virtual-retract corollary, which is also `virtual-retracts-satisfy-pbh-coset-wreath-closure` of openq-papers) is covered by these two; not checked line by line.
3. **BS(1,m) ≤ 3V for odd m.**
   - `bs-1-m-embeds-in-brin-thompson-3v-for-odd-m` (bh-free-18, 09:43)
   - `bs1m-embeds-in-3v-for-every-odd-m` (gq-affq, 09:54; it declares itself a pointer with an independent machine family)
   - The older `bs13-embeds-in-brin-thompson-3v` (m = 3) is a special case and names neither.
   - Merge: done in substance. Add a special-case route into the m = 3 node.
4. **Kourovka 21.75.** Two proofs of one theorem. Reconciled by the lanes, so nothing is left to merge.
   - `ct-p1-and-ct-p2-always-generate-ct-p1-union-p2` (bh-free-37) is the primary. Its top line lacks an ESTABLISHED marker; posted to bh-free-37.
   - `ct-p1-and-ct-p2-generate-ct-of-the-union` (bh-artin) is marked DUPLICATE.
5. **Kourovka 17.59.** Two proofs, by design.
   - `ct-z-is-the-rcwa-group-fixing-the-nonnegative-integers` (bh-kourovka, groupoid input)
   - `piecewise-canonical-permutations-are-transposition-products` (bh-pal-kourovka59, elementary)
   - They are cross-linked, so nothing needs merging. Keep the elementary one for Palomar.

### B. Convergent results; each should cite the other
6. **Amir–Lazarovich torsion.** The two results are compatible, and together they answer AL's question for d ≥ 9. Neither node names the other.
   - `amir-lazarovich-simple-lattice-has-torsion-iff-index-four` (bh-free-42, 10:27) reduces "does Λ have torsion" to "is Λ'^+ simple".
   - `amir-lazarovich-simple-lattices-have-torsion` (bh-free-extensions, 11:00) proves that the simple lattices are exactly the index-4 colour-preserving subgroups, so they have torsion.
   - Lesson: AL lattices give no torsion-free fp simple group of cd 3 (Kourovka 21.46).
   - Merge: bh-free-42's node should cite bh-free-extensions' as its answer.
7. **Closure of B_A under amalgams and HNN extensions.** Four theorems from four lanes, with no cross-references at all. This is one mechanism, a B_A overgroup that realizes the edge map (see bh-one-relator's LESSONS line).
   - `pbh-class-closed-under-common-retract-amalgams` (09-16 swarm; re-checked by bh-verify-artin and bh-free-11)
   - `pbh-class-closed-under-centralizer-amalgams` (bh-relhyp)
   - `pbh-amalgams-over-centralizer-separated-edges` (bh-free-49, 11:00)
   - `pbh-closed-under-finite-edge-graphs-of-groups` (bh-free-10; OPEN), with `pbh-finite-edge-closure-equivalences`
   - Merge: one master closure theorem that states the edge-realization criterion once, with the four as corollaries or open cases.
8. **Lagrangian Brin–Thompson hosts for Deligne's lattice.** Two lanes, both targets OPEN; the nodes are cross-named.
   - `lagrangian-thompson-group-is-finitely-presented` (bh-free-14, odometer form)
   - `lagrangian-brin-thompson-group-is-finitely-presented` (bh-free-55, Maslov Cantorization form)
   - Merge: one gate node.
9. **PBH via Cantor actions.** Two equivalences that name neither the other (flagged in pass 2, still open).
   - `permutational-boone-higman-iff-dense-cantor-actors` (bh-typeA-oligomorphic)
   - `permutational-boone-higman-iff-full-cantor-hosts` (bh-typeA-universal)
   - Synthesis should state how they relate.
10. **Three universal-envelope targets.** They are parallel forms of one gate.
    - `decidable-inputs-have-fp-shell-envelopes`
    - `decidable-inputs-have-fp-genuine-action-shell-envelopes`
    - `decidable-inputs-have-fp-houghton-like-shift-envelopes`
    - Only partly cross-linked.

### C. Consequences that change the synthesis (INSIGHT FIRST)
11. **The Titz Mite–Witzel lattices and kernels are now in B_A.** Wired by bh-integrate in de3934873: `titz-witzel-lattices-pbh-via-euclidean-building-lattices` makes `titz-witzel-lattices-satisfy-permutational-boone-higman` ESTABLISHED, as a lane proof and unreviewed.
    - Row S3 of SYNTHESIS.md ("Titz Mite–Witzel kernels MIF", bh-testcases) is no longer needed for PBH. It still matters for MIF.
    - Two nodes say the five TW kernels are "the only recorded fp simple groups not known in B_A": `fp-simple-groups-have-the-joint-embedding-property` (Attempt, l.~72–82) and `boone-higman-closed-under-finite-direct-products` (l.~160–170). If the Euclidean theorem holds, every recorded fp simple group is in B_A, and the (JE) and product test cases move.
    - Highest-value verification target: `euclidean-building-lattices-lie-in-permutational-bh-class` (bh-groupoid; unreviewed; it rests on Ciobotaru–Le Bars 2601.13092 and Li's thm:deg). bh-refute has so far verified only the vertex-free Ã₂ case (11d8fa37b, PASS).
12. **MO 412219 is answered negatively.** `fp-decidable-group-whose-e-is-not-recursively-presented` (bh-free-08; bh-refute PASS, 4067f5db5).
    - Three ESTABLISHED nodes still `require` the REFUTED `e-of-finitely-presented-group-is-recursively-presented` for its reformulation E(G) = (G*Z)/J_1(G).
    - Merge: split that reformulation into its own established node, and repoint the three nodes' requires. Owners: bh-free-41, bh-free-08, bh-openq-lists.
