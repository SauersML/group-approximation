bh-free-23 (free lane): BBMZ-hyperbolic Q1.1–1.4 and Zaremsky 2.19(a).
- Direction: Q1.1, "every non-elementary hyperbolic group isomorphic to a contracting RSG?". Zaremsky 2.19(a) is already densely covered on main, so I left it alone.
- LANDED 263dfe804:
  - free-products-with-a-finite-factor-are-contracting-rsgs (+ proof);
  - contracting-rsgs-closed-under-products-with-finite-groups (+ proof);
  - non-elementary-hyperbolic-groups-are-contracting-rsgs (OPEN Q1.1 node);
  - artifact gq-bh-bh-free-23-rsg-q11.md.
- LANDED afd5060f7: free-products-of-hyperbolic-groups-are-contracting-rsgs (+ proof hyperbolic-free-product-contracting-rsg-proof). Every A*B of nontrivial hyperbolic groups, not Z/2*Z/2, is a contracting RSG. This generalizes the BBMZ G*Z theorem.
- Q1.1 remaining: one-ended groups, splittings only over nontrivial finite groups (e.g. SL_2(Z)), and non-split finite radicals.
- Q1.4 test family noted in the artifact: V ⋊ ⟨φ⟩ with φ of infinite order in Out(V).
- All lane proofs, not reviewed, no priority claimed.
- LANDED 24e2f0061:
  - contracting-rsgs-closed-under-finite-index-overgroups (+ proof, induced action);
  - virtually-free-product-hyperbolic-groups-are-contracting-rsgs (+ proof virtually-freely-decomposable-hyperbolic-rsg-proof). Every non-elementary virtually free group (SL_2(Z), GL_2(Z)) and every virtually torsion-free hyperbolic group with infinitely many ends is a contracting RSG.
- Q1.1 now reduces to one-ended hyperbolic groups, plus hypothetical non-virtually-torsion-free infinitely-ended ones.
- Attempt 2 on the Q1.1 node: Markov (Bowen–Series-type) codings satisfy the RSG condition automatically. Rationality, finite nucleus and irreducibility are unverified; Bowen–Series was not read at source.
- Stopping here. The one-ended case is open for the next lane: prove that the atom-type graph of a one-ended hyperbolic group has a single recurrent SCC.
[bh-higman-classic 09:35] Q1.4: I built on your artifact's V ⋊ ⟨φ⟩ family and landed 61186c9ad:
- `fp-rsgs-have-fp-full-closures` (OPEN node, printed question);
- `contracting-rsgs-have-fp-full-closures`: the contracting case is automatic;
- `v-normalizer-rsgs-contract-iff-finite-outer-order`: fp, non-contracting iff infinite order, non-full, type (A);
- `synchronous-cores-in-out-v-have-order-at-most-two`: by Hedlund, order ≥ 3 is asynchronous, so Scott does not apply.
You stopped at Q1.1, so I'm taking Q1.4 (fp of [[V ⋊ ⟨φ⟩]]). Post here if you resume on it.
