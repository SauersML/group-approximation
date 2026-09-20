---
rg: 2
id: rover-nekrashevych-polynomial-activity-tower-review
kind: claim
title: Referee review of rover-nekrashevych-polynomial-activity-tower-sigma-full — item 1 (V_{d,r}G is F_infinity for contracting G of polynomial activity) PASSES, by applying Belk-Hyde-Matucci's main finiteness theorem at each step of the activity tower to the point-fixers, with the route's sections 0-6 supplying its hypotheses; the Sigma items 2-3 rest on the unreviewed heredity node and are not reviewed here; polynomial activity is equivalent to the nucleus graph having only single-cycle strongly connected components
distinct_from:
  rover-nekrashevych-polynomial-activity-tower-sigma-full: that is the claim under review; this checks its proof and gives a shorter derivation of its item 1 that avoids the Sigma-heredity machinery.
  level-set-route-reaches-only-bounded-rover-nekrashevych-groups: that scopes the bounded-RSG machinery for the Skipper-Zaremsky question; this firms up the polynomial row of its table.
---

**ESTABLISHED (referee bh-sz-vdg, 2026-09-19).** It reviews `rover-nekrashevych-polynomial-activity-tower-sigma-full`
and its route `rover-nekrashevych-polynomial-activity-tower-sigma-full-proof`, landed in b9320bf381, 8866d29a50 and
01632836e3. The reviewer did not write either of them.

Read for this review:
- **Belk–Hyde–Matucci** arXiv:2407.03149. Theorem 1.1 and the definition of a finite germ extension come through the
  arXiv HTML. They agree with the LaTeX quotes of `thm:MainFinitenessTheorem`, (FGE) and Appendix A `thm:Stabilizers`
  in `germ-complex-and-bux-gonzalez-morse-inputs-citation` and `higman-thompson-rational-point-fixers-are-f-infinity-citation`.
- **The route, in full.**

## Verdicts

| Item | Verdict |
|---|---|
| 1: `V_{d,r}G` has type `F_∞` | **PASS**, via the shorter derivation below |
| 2: `Σ^m(Γ) = S(Γ)` | **Not reviewed.** It rests on `germ-extension-point-fixer-sigma-heredity`, which is unreviewed, and on that node's two inputs |
| 3: co-abelian normal subgroups are `F_∞` | **Not reviewed**, for the same reason |

## Item 1 without the Σ machinery

BHM `thm:MainFinitenessTheorem` (Theorem 1.1) says the following. Let `G` be a finite germ extension of
`B ≤ Homeo(X)` such that:
1. `B`, and `Stab_B(M)` for every finite `M ⊆ sing(G)`, have type `F_∞`;
2. `B` is oligomorphic on `sing(G)`;
3. `|(G)_p : (B)_p| < ∞` for every `p ∈ sing(G)`.

Then `G` has type `F_∞`.

**Induction.** Let `P` be the set of rational points. The statement is
`(A_i)`: `Fix_{Γ_i}(M)` has type `F_∞` for every finite `M ⊂ P`, including `M = ∅`.
- **Base `(A_{−1})`.** `Γ_{−1} = V_{d,r}`, and `Fix_V(M)` has type `F_∞` by BHM Appendix A `thm:Stabilizers`.
- **Step.** Fix a finite `M ⊂ P`, with `B_M = Fix_{Γ_i}(M)` and `E_M = Fix_{Γ_{i+1}}(M)`.
  - **Finite germ extension.** (H1) of the route makes `E_M` a finite germ extension of `B_M` with
    `sing(E_M) ⊆ O_R ⊆ P`.
  - **Hypothesis 1.** `Stab_{B_M}(M')` has type `F_∞` for every finite `M' ⊆ sing(E_M)`. It contains
    `Fix_{Γ_i}(M ∪ M')` with finite index, since `B_M` permutes the finite set `M'`, and that group is `F_∞` by `(A_i)`.
  - **Hypothesis 2.** (H2) of the route, for every `m`, is oligomorphicity.
  - **Hypothesis 3.** (H3) of the route.
  - So `E_M` has type `F_∞`, which is `(A_{i+1})`.

At `i = n` and `M = ∅`, `Γ` has type `F_∞`. This is exactly the induction BHM's remark after `thm:RoverNek` sketches.
It needs no localization (Lemma L) and no (H4).

## Line-by-line check of what item 1 uses

- **§0, cones, and Lemma P.** Correct. The count mod `d − 1` is standard. Lemma P needs `C ∖ (E ∪ N)` nonempty,
  and step 1 secures that.
- **(S1).** Correct. `θ_k(gh) ≤ θ_k(g) + θ_k(h)` holds because `h` permutes level `k`, and the section inequality
  holds because distinct `u` give distinct `wu`. `Γ_{−1} = V`, since finitary elements are piecewise prefix
  replacements.
- **(S2).** Correct. In step 2, comparing prefix lengths uses only that `h` is onto, and the equality of sections
  uses faithfulness of `G`.
- **§4(a).** Correct.
  - Lyndon–Schützenberger gives `a ≠ b`. The `2^j` block words are distinct because the blocks have equal length.
  - The consequence (every SCC of the automaton on `Q ∖ {1}` containing an edge is a simple cycle) follows from
    out-degree 1.
- **§4(b).** Correct; all four steps check.
  - The words are distinct at position `sab + 1`.
  - The count gives `θ_k(q') ≥ (L+1)θ_{m_0}(q)`.
  - With `L = m_0` and `k ≤ (2+ab)m_0` this contradicts `q' ∈ G_{i+1}`.
  - In case `i = −1`, `θ_m(q) ≥ 1` actually holds for every `m`.
- **§4(c).** Correct. Repair: step 2 should say that the `D`-component containing the tail lies in an SCC of the
  automaton on `Q ∖ {1}` that contains an edge, which is a circuit by (a).
- **§4(d).** Correct. `λ_q` is intrinsic to `q`, since the closed walks at `q` are the words `w` with `q|_w = q`.
- **Lemma G.** Correct. Repair: step 1 should say `|γ_{k+1}| = |γ_k| + |β|`, which gives `|γ_k| ≥ |α|` for large
  `k`. It also should say the coset is a right coset of `(V)_p`.
- **(R0), (H1), (H2), (H3).** Correct.
  - In (H3) the index inequality needs `(V)_p ≤ (B_M)_p`, and steps 1–2 give it.
  - The injectivity step in (H2) holds because tuples are ordered, so `v` fixes `M` pointwise.

Lemma L and (H4) are also correct as written, but item 1 does not need them.

## Polynomial activity in terms of the nucleus graph

Let `G` be finitely generated and contracting with nucleus `N`, and let `𝒩` be the graph on `N ∖ {1}` with edges
`n → n|_x ≠ 1`, as in `level-set-route-reaches-only-bounded-rover-nekrashevych-groups`. Then:
- `G` has polynomial activity growth, in the claim's sense (one degree `n` for all elements), exactly when every SCC
  of `𝒩` is a single cycle or trivial.
- `G` has degree `≤ 0` exactly when, in addition, no path joins two distinct cycles. Equivalently, `G` is a bounded
  automata group in BHM's sense ("only finitely many infinite words … for which all of the local actions … are
  nontrivial").

**Proof.**
- **Counting paths.** `n|_v ≠ 1` holds exactly when the path of `v` from `n` stays in `𝒩`, since `N` is closed under
  sections and a trivial section stays trivial. So `θ_k(n)` counts paths of length `k` from `n` in `𝒩`.
- **(⇒)** Every nucleus element lies in `G`. An SCC of `𝒩` through `n` lies in `n`'s automaton on nontrivial states,
  so §4(a) of the route makes it a single cycle.
- **(⇐)** In a finite graph whose nontrivial SCCs are single cycles, the number of paths of length `k` is
  `O(k^{c−1})`. Here `c` is the largest number of cycles on one path, and `c ≤ |N|`.
  - Every `g` has all sections in `N` below level `L(g)`, so `θ_{L+k}(g) ≤ d^L max_{n ∈ N} θ_k(n)`.
  - So the degree is uniform, `≤ c − 1`.
- **Degree 0.** Degree `≤ 0` means `c ≤ 1`, i.e. no path through two cycles. A path from cycle `C_1` to cycle `C_2`
  gives linearly many nontrivial words by looping around `C_1`.
- **Singular words.** An infinite path from `n` is a singular word of `n`, and there are finitely many exactly when
  `c ≤ 1`. ∎

So the two identifications that `level-set-route-reaches-only-bounded-rover-nekrashevych-groups` recorded as recalled
are proved:
- its case (B) is BHM's bounded automata class, by definition;
- its case (B) ∪ (P) is the hypothesis of the node reviewed here.
