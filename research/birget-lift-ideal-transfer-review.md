---
rg: 2
id: birget-lift-ideal-transfer-review
kind: claim
title: Referee review of the new parts of 2222dfd660 — the Zaremsky transfer lemma is correct (the regrouped recursion has the same word-level sections and the same trivial-root-permutation condition, so it has the same lift ideals and the same relator kernel, and Zaremsky uses finite presentation only through Scott's theorem); so Birget's cap question reduces, negatively, to (a) plus (c) for a single machine; the contracting calibration and the non-contraction of the increment loop check by hand; (c) fails for the Theorem A″ machine, even without the transfer
distinct_from:
  birget-question-via-decidable-bartholdi-mitrofanov-hosts: that is the lane node under review; this checks its transfer lemma and its three tests on (c).
  elliptic-marker-mismatch-review: that reviews bh-q12-kazhdan's elliptic criterion; this reviews bh-birget's Zaremsky transfer.
---

**ESTABLISHED (referee bh-ref-c, 2026-09-19; review of the parts of 2222dfd660 added after bh-ref-e's review).**
Verdict: **PASS**, with two minor citation repairs.

Read at source: Zaremsky, arXiv:2405.09722v1 (arXiv HTML):
- Theorem 1.1;
- Citations 2.3 (Scott) and 2.4 (Nekrashevych), and Proposition 2.5;
- the regrouping `g ↔ σ^(⊕m)(g_1, …, g_d, …, g_1, …, g_d)`;
- the abelianization step;
- the remark on contracting groups.

## The transfer lemma: PASS

**Where Zaremsky uses finite presentation.** The simple group is `[V_(md)(G), V_(md)(G)]`. It is finitely presented
because it has finite index in `V_(md)(G)`, which is finitely presented "by Citation 2.3" (Scott: `G` finitely
presented ⇒ `V_d(G)` finitely presented). That is the only use. The other ingredients hold for every finitely
generated self-similar `G` with a finite wreath recursion:
- **Citation 2.4** (simplicity of `[V_d(G), V_d(G)]`) and **Proposition 2.5** (`F ≀ [V,V] ↪ [V,V]`) are stated
  for any self-similar `G`.
- **The abelianization step is Zaremsky's own computation, not a citation.** It is the relation
  `ḡ = m(ḡ_1 + ⋯ + ḡ_d)` in the abelianization of `V_(md)(G)`, plus the choice of an even `m` with `1/m` not an
  eigenvalue of the integer matrix `A` of abelianized sections of the generators.
  - It uses only the generators and their word-level sections.
  - `det(I − mA) ≠ 0` makes every image of a generator torsion. Since `V_(md)(G)` is finitely generated, its
    abelianization is finite.
- **Kaloujnine–Krasner.** `G ↪ (G/H) ≀ H` with `H = G ∩ [V,V]`. This needs `G/H` finite, which it is, because
  `G/H ↪ V^(ab)`.
- Zaremsky's own remark supports this: "It is not difficult to adapt our proof for finitely presented self-similar
  groups to also handle finitely generated self-similar groups that are 'contracting'".

**Regrouping preserves lift ideals.** Blocks are indexed by `j ≤ m`.
- Under `ψ_m`, every `h ∈ G` sends `(j, x)` to `(j, h(x))`, preserving the block. So the product rule
  `(gh)|_y = g|_(h(y)) h|_y` gives `w|_(j,x) = w|_x` for every word `w`.
- The root permutation of `w` is `σ_w^(⊕m)`, which is trivial iff `σ_w` is.
- So "`w` has trivial root permutation and every section lies in `M`" is the same condition for `ψ_m` and for `ψ`.
  A normal subgroup of `F_S` is lift-closed for one iff it is for the other, and `⟨⟨R⟩⟩_lift` is the same set.
- **Same kernel.** Deleting block indices, `(j_1,x_1)(j_2,x_2)⋯ ↦ x_1x_2⋯`, is `G`-equivariant from `T_(md)` onto
  `T_d`, and the blocks are fixed. So `w` acts trivially on `T_(md)` iff it acts trivially on `T_d`.
- **Hypotheses of the criterion.** `ψ_m` is a faithful self-similar action with word-level sections in `S^(±1)`,
  which is what item 1 of `lift-ideal-criterion-sufficiency-holds-for-infinite-state` requires. So
  `V_(md)(G)` is finitely presented, and Zaremsky's argument goes through.

**The payoff is right.** `G ≤ Σ` finitely generated with `Σ` finitely presented and simple. An algorithm for
`WP(Σ)` in time `T′` decides `WP(G)` in time `T′(C·l) + O(l)`. So (a), in its `C·T(C·l) + C·l + C` form, rules
out every recursive bound for `Σ`. Birget's question then **reduces to (a) plus (c) for a single hard machine**,
with a negative answer (no cap), as the node says.

**Repairs (citation only).**
- The node attributes "Nekrashevych's abelianization formula" to Citation 2.4. Citation 2.4 is the simplicity of
  the commutator subgroup (Nekrashevych 2018). The abelianization relation is computed inside Zaremsky's proof.
- List simplicity (2.4) and the abelianization step separately, with those attributions.

## Test 1, the contracting calibration: PASS

I checked it by hand.
- **Wreath recursions.** `u = (0 1)(u,u,u,u)`, `t = (†₁ †₂)(t,t,1,1)` and `s_† = (0 †₁)(1,s,1,1)` follow from the
  quoted rules and the default convention. `x` and `y` have only default rules, so they act trivially.
- **The element `s′`.** `s′ = usu = (1 †₁)(s′,1,1,1)`, and `u` is an involution. `u` commutes with `t`, since
  `utu` satisfies `t`'s recursion.
- **A letter dies.** A letter has a nontrivial section only where it fixes the letter read: `s` at `1`, `s′` at
  `0`, `t` at `0` and `1`. So a word containing both `s` and `s′` loses a letter at every first-level vertex.
- **The survivors form finite groups.** `⟨s,t⟩` acts on the pair (first non-`1` letter, first `†` after it), which
  has at most 9 states, and is closed under sections. Likewise `⟨s′,t⟩`.
- **Conclusion.** Contracting, hence finite-state. So Nekrashevych's FP2 and the necessity half of Theorem A give
  (c). `x, y ∈ R` is forced, since `x|_v` is a power of `x` for every `v`, so `x ∉ K_∞`.

## Test 2, the increment loop: PASS; (c) correctly left open

- `s_* = (0 𝐢₁)(s_*, s_*, 1, s_*, s_*)`, with sections listed at `0, 1, 𝐢₁, †₁, †₂`. It is an adding machine on the
  `{0, 𝐢₁}` letters, so it has infinite order.
- `s_*^k|_1 = s_*^k`, so the nucleus is infinite and `G` is not contracting.
- `x` and `y` act trivially, because every section is a power of `x` or `y` and every root permutation is trivial.
- `G` is still finite-state, so Theorem A (both directions) applies, and `K_∞` is decidable (item 4 there). A
  direct test of `N = ⟨⟨K_∞ ∪ {x, y}⟩⟩_lift` is the natural next computation.

## Test 3, the Theorem A″ machine: PASS

The argument through the transfer lemma and Kuznetsov is correct. It also holds **without** the transfer lemma:
- (c) plus item 1 of the criterion makes `V_d(G)` finitely presented. Then triviality in `G ≤ V_d(G)` is
  recursively enumerable.
- Triviality in `G` is also co-recursively enumerable, since a nontrivial element moves some vertex. So `WP(G)`
  would be decidable, contradicting Theorem A″.
- So its relator kernel is not a finitely generated lift ideal. Any proof of (c) must use decidability of `M`, as
  the node says.

## Bottom line

The transfer is sound. Birget's question now has a clean sufficient condition: (c) for one Bartholdi–Mitrofanov
group whose machine is hard in the sense of (a). The first informative case is the increment loop of Test 2, which
is finite-state and not contracting, so Theorem A decides it.
