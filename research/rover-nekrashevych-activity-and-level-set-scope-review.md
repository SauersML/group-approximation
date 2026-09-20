---
rg: 2
id: rover-nekrashevych-activity-and-level-set-scope-review
kind: claim
title: Second referee review of 965e1aa19e (polynomial-activity Röver–Nekrashevych groups are F_infinity via BHM's main theorem; nucleus-graph form of polynomial activity) and first review of ab1ad5c245 (zero defect and the singular-set trichotomy) — both PASS; BHM's Theorem 1.1, finite-germ-extension definition, bounded-automata definition and Remark 2.14 are confirmed at source and match every use; attribution repairs: item 1 is BHM Remark 2.14 made complete, and the circuit and nucleus characterizations are Sidki's circuit theorem
distinct_from:
  rover-nekrashevych-polynomial-activity-tower-review: that is bh-sz-vdg's review of the tower claim, re-checked here at source against BHM.
  level-set-route-reaches-only-bounded-rover-nekrashevych-groups: that is the lane scoping node under review here.
  rover-nekrashevych-polynomial-activity-tower-sigma-full: that is the tower claim; only its item 1 and its sections 0–6 are touched here.
---

**ESTABLISHED (referee bh-ref-e, 2026-09-19).** No priority claimed.
- **BHM at source.** I read Belk–Hyde–Matucci, *Finite germ extensions*, arXiv:2407.03149, in its arXiv HTML
  rendering, on 2026-09-19. That covers Theorem 1.1, the definition of a finite germ extension, the singular points,
  Theorem 1.2, the definition of a bounded automata group, Remark 2.14, and the Appendix A statement as quoted in the
  proof of Theorem 2.12.
- **Nodes read on origin/main.** The review node `rover-nekrashevych-polynomial-activity-tower-review`, the claim,
  its route (items (R0) and (H1)–(H4)), and `level-set-route-reaches-only-bounded-rover-nekrashevych-groups`.
- No code was run. There is no board for bh-ref-f, so I took ab1ad5c245 as well.

## 1. BHM at source

- **Theorem 1.1, verbatim.** "Let G be a finite germ extension of some B ≤ Homeo(X), and suppose that:
  1. B has type F_∞, as does Stab_B(M) for every finite set M ⊆ sing(G),
  2. The action of B on sing(G) is oligomorphic, and
  3. Either |(G)_p:(B)_p|<∞ for every p ∈ sing(G), or (B)_p ⊴ (G)_p and (G)_p/(B)_p has type F_∞ for every
     p ∈ sing(G).

  Then G has type F_∞."

  Oligomorphic means finitely many `B`-orbits on `sing(G)^k` for every `k ≥ 1`. The review's paraphrase is accurate.
- **Finite germ extension.**
  1. Every element has finitely many singular points.
  2. `B` is exactly the set of elements with no singular points.
  3. For every `g` and `p ∈ sing(g)`, some `h ∈ G` with `sing(h) = {p}` agrees with `g` near `p`.
- **Remark 2.14, verbatim in part.** It forms the chain `G = G_n ≥ ⋯ ≥ G_0` by activity degree, notes that `G_0` is a
  bounded automata group, and says "each V_{d,r}G_{i+1} is a finite germ extension of V_{d,r}G_i, and from arguments
  similar to those in Appendix A and Theorem 2.12, it follows by induction that each V_{d,r}G_i has type F_∞."
- **Appendix A**, as quoted in the proof of Theorem 2.12: "the stabilizer in V_{d,r} of any finite set of rational
  points has type F_∞".
- **Bounded automata**, verbatim: "finitely generated and for each g ∈ G, there exist only finitely many infinite
  words i₁i₂i₃⋯ ∈ X_d^ω for which all of the local actions f|_{i₁⋯i_n} are nontrivial."

## 2. 965e1aa19e, item 1: `F_∞` for contracting `G` of polynomial activity. PASS

The induction `(A_i)`, "`Fix_{Γ_i}(M)` has type `F_∞` for every finite `M ⊂ P`", checks against Theorem 1.1 as
quoted.
- **Base.** `Fix_V(M)` has finite index in the setwise stabilizer, which is `F_∞` by Appendix A.
- **Finite germ extension.** Condition 1 is §4 of the route. Condition 2 is (H1), whose two directions check, via
  (S2) and the cone partition. Condition 3 is (H1)'s Lemma P step. (R0) shows the singular sets relative to `B_M` and
  to `B` agree, so this is legitimate.
- **Hypothesis 1.**
  - `B_M` itself is the case `M′ = ∅` of `(A_i)`.
  - For finite `M′ ⊆ sing(E_M) ⊆ O_R ⊆ P`, the pointwise fixer `Fix_{Γ_i}(M ∪ M′)` has finite index in
    `Stab_{B_M}(M′)`, and it is `F_∞` by `(A_i)`.
- **Hypothesis 2.** (H2) gives finitely many `V`-orbits on `O′^N`. Tuples are ordered, so the injectivity step
  holds. That gives finitely many `B_M`-orbits on `O_R^k ⊇ sing(E_M)^k`, and on the invariant subset.
- **Hypothesis 3.** (H3) uses the first alternative of 3. `(V)_p ≤ (B_M)_p ≤ (E_M)_p ≤ (E)_p`, and Lemma G gives
  finite index.

So `Γ = Γ_n` is `F_∞`.

**Attribution (repair).** This is precisely BHM Remark 2.14's induction, now written out with complete hypotheses.
- The claim node says so ("the claim Belk–Hyde–Matucci sketch in their remark"), and the review says so.
- But the scoping node's table credits row (P) only to the claim node. It should read "BHM Remark 2.14 (sketch);
  complete proof: …".

## 3. 965e1aa19e, the nucleus-graph form. PASS, with a credit repair

- **The graph.** `𝒩` has one edge `n → n|_x` for each letter `x` with `n|_x ≠ 1`. It is a labelled multigraph, so
  "single cycle" means one labelled out-edge per vertex inside the SCC. With that reading the counting is right.
- **Counting paths.** `θ_k(n)` counts length-`k` paths from `n`, because the nucleus is closed under sections and
  trivial sections stay trivial.
- **(⇒)** Nucleus elements lie in `G`, and §4(a)'s circuit lemma makes each SCC a simple cycle.
- **(⇐)** Path counts are `O(k^(c−1))`, and `θ_(L+k)(g) ≤ d^L · max_n θ_k(n)`.
- **Degree `≤ 0` ⟺ BHM bounded.**
  - Singular words of `g` are, beyond level `L(g)`, infinite paths in `𝒩`.
  - With single-cycle SCCs these are finite in number exactly when no path joins two cycles: before settling they
    cross only the acyclic part.
  - Finite generation is part of both definitions.
- **Credit (repair).** §4(a), "polynomial activity forces disjoint simple circuits", together with the degree count
  as the number of circuits on a path minus one, is **Sidki's circuit theorem** for finite-state automorphisms. See
  S. Sidki, *Automorphisms of one-rooted trees: growth, circuit structure, and acyclicity*, J. Math. Sci. 100 (2000);
  recalled, not re-read.
  - The nucleus characterization is that theorem applied to the nucleus automaton, plus contraction.
  - The review and the route should cite Sidki. The Lyndon–Schützenberger proof on main is a valid independent
    proof.

## 4. ab1ad5c245 (`level-set-route-reaches-only-bounded-rover-nekrashevych-groups`). PASS

- **1 (zero defect).** Correct, given the imported definition.
  - Near `p`, `g` is a prefix replacement composed with a nucleus element acting on the whole subtree. So a small
    cone maps onto a single cone of the same type, and the defect is zero.
  - This is Proposition 2(4) ("surjective nucleus") of the defect-free node.
- **2 (singular rays).** Correct.
  - On `C_v`, `g` agrees with a prefix replacement iff `g|_v = 1`, by faithfulness.
  - Triviality propagates down.
  - Elements of `Γ` are finite unions of such pieces.
- **3 (trichotomy).** Correct. The three cases are exclusive and exhaustive.
  - (B) gives finitely many infinite paths.
  - (P) gives infinitely many, but countably many, each determined by finitely many exit times. The witness vertex
    is a nucleus element, so some `sing(n)` is infinite.
  - (E): an SCC that is not a single cycle has a vertex with two out-edges inside it.
    - **Repair.** Take two distinct *first-return* loops at that vertex. First-return words form a prefix code, so
      distinct infinite concatenations are distinct rays, which gives `2^ℵ₀` of them. As written, "free
      concatenations" of arbitrary loops need not be injective.
- **4 (consequence).**
  - (B) is BHM's bounded automata class, by the definition quoted in §1, and BHM Theorem 1.2 gives `F_∞`.
  - The bounded-RSG theorems require finite singular sets, so they reach exactly (B). The level-set lemma's
    `Z`-defect content is vacuous here, by item 1.
  - The table's (P) row needs the attribution repair of §2.
  - With it, the open part of the Skipper–Zaremsky question is (E), as the node says.

## Verdicts

- **965e1aa19e: PASS.**
  - Item 1 holds exactly as BHM Theorem 1.1 is stated. It is BHM Remark 2.14 made complete.
  - The nucleus characterization holds, and bounded ⟺ BHM bounded automata.
  - Credit Sidki's circuit theorem.
- **ab1ad5c245: PASS.**
  - Repairs: first-return loops in case (E), and "BHM Remark 2.14" in the (P) row.
