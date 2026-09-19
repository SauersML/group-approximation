# bh-invent-03 (groupoid Higman embedding) — 2026-09-18
Landed 4c74c3eff:
- boolean-inverse-monoid-finite-presentation-is-finite-type (+ -proof): B(Λ⋉X) and B(G_V×(Λ⋉X)) are fp iff X is SFT (Λ fp). ESTABLISHED lane proof.
- fp-boolean-inverse-monoids-need-not-have-fp-full-groups: A^Λ×Y_0 has fp B(T) but non-fp F(T) = A(T). ESTABLISHED lane proof.
- rigid-boolean-inverse-monoid-presentations-have-fp-full-groups: OPEN transfer conjecture (F(G_V×𝒢) fp ⟺ Steinberg algebras fp); rigid GHE + transfer ⇒ BH.
- artifact gq-bh-bh-invent-03-groupoid-higman: cocycle-lifting lemma (proved); the quotient-vs-embedding lesson; renormalization sketch (PLAUSIBLE).
For G2 lanes: fp of the renormalized Labbé host ⇒ Labbé quantum rigidity (sketch §5); the obstacle is codim-1 faults.

## Pass 2 (after restart, 09-18 afternoon). Landed 2e79547615:
- steinberg-fp-is-a-kakutani-invariant (+ -proof): full corners of fp algebras are fp. So fp of A_k(𝒢) is a Kakutani invariant; Z² rigidity is invariant under orbit-equivalence recodings; (E′) is a groupoid property. ESTABLISHED lane proof.
- outer-extensions-of-fp-steinberg-groupoids-need-no-rigidity: A ⋊ Γ is fp and central simple for Γ fp acting outer-topologically-freely on ℋ with fp A = A_k(ℋ); ceiling WP(Γ) ≤ WP(A)∘exp. So rigidity = carrier gate. ESTABLISHED lane proof.
Next: a rigidity certificate for a groupoid with complex language, tested on its most convenient Kakutani model. Candidate: Bowditch-boundary-type groupoids of Λ = P*Z with P ⊇ G, where compression pays for the tree directions and properness pays near the parabolic points.
- Pass 2b, landed 1465be6650: locally-finite-splittings-preserve-rigid-sft-compactifications (+ -rigid-compactification-proof). 𝒞 is closed under finite graphs of groups with finite-index edge groups, needing only ONE vertex group in 𝒞. This answers bh-g2-buildings' (★𝒞) test cases BS(1,2) and H_3. Aligned with bf61de7d0 (tree gluing) and 4a734659e (centrality (C) is automatic for tree-pointer bases).
Next: relative seeds, i.e. SFTs on A whose seed-forced point has stabilizer C (orbit A/C). These would bring HNN extensions over infinite-index C into 𝒞, which is the Higman-embedding step.
- Pass 2c, landed 5deee01840: relative-seeds-glue-graphs-of-groups-into-class-c (+ -proof). Relative seeds glue along any graph of groups (vertex-marked and transitive) and survive finite-index induction; free and free abelian subgroups have them; graphs of free/free abelian groups are in 𝒞; the forced point is a membership oracle. CAP reduces to rigid relative seeds for hard-membership subgroups (K_M's R_0-type subgroups). For bh-free-56 (HNN tower rung) and bh-star-a (CAP): the tree here is locally INFINITE, so bh-star-a's locally-finite death does not apply.
Next: a rigid relative seed for (K_M, R_0) with M trivial, or a cap theorem stating that rigid relative seeds have finite-state stabilizers.

- Note from bh-emitter-a (09-18): CAP rung 1c with Baumslag-Gersten, landed 17f8da472 as baumslag-gersten-seed-forcing-length-is-non-elementary. Relative seeds y_a and y_b on BS(1,2) both satisfy (RS1), and the glued BG seed satisfies (C1). Its forcing length is at least tower(log n - 3), yet WP(BG) is in P. BG is in class C once y_b satisfies (RS2) and (RS3), which is OPEN. Consequence: forcing length is NOT the CAP invariant; evaluation or membership complexity is. A real rung-1c test needs hard-membership relative seeds.
- Pass 3 (SEED TOWER lead), landed ceaf3f6e96: every-decidable-set-has-a-mortal-decider, plus a correction of 5deee0184 (c) that cites 0d6bf2845 for K_M ∈ 𝒞. Team plan v1 is on board/seed-tower.md (LEAD). My duplicate rung-1 node is shelved in superseded/. Next: prove Kurosh (core-marked) gluing.
