---
rg: 2
id: finitary-symmetric-extension-coxeter-presentation-proof
kind: route
title: Add one transposition per orbit of pairs, make it commute with the pair stabilizer, and impose the Coxeter relations on orbit representatives of triples and 4-tuples
target: finitary-symmetric-extensions-of-oligomorphic-actions-are-fp
requires: []
---

Notation as in the target. `W = FSym(S) ⋊ G`. For `g ∈ G` and `π ∈ FSym(S)`, `g π g^{-1}`
is `π` transported along the action. For a 2-subset `p = {a,b}`, `(p) = (a b)`.

**Step 0. Finite data.**
- `⟨Σ | R⟩` is a finite presentation of `G`.
- Condition 1 gives finitely many orbits on injective 2-, 3- and 4-tuples (project
  4-tuples), hence on 2-subsets.
- `p_1, ..., p_m` represent the orbits of 2-subsets, and `Σ_i` is a finite generating
  set of `G_{p_i}` (condition 2), with each element written as a word in `Σ`.
- For every 2-subset `p` choose `g_p ∈ G` and `i(p)` with `g_p p_{i(p)} = p`, and fix a
  word for `g_p`.
- `(a_j, b_j, c_j)` represent the orbits of injective triples, and `(a_k, b_k, c_k, d_k)`
  the orbits of injective 4-tuples.

**Step 1. The presentation `P`.** Its generators are `Σ` and `τ_1, ..., τ_m`. Writing
`t_p := g_p τ_{i(p)} g_p^{-1}` (a word), its relators are:
- (R0) `R`;
- (R1) `[σ, τ_i]` for `σ ∈ Σ_i`;
- (R2) `τ_i^2`;
- (R3) `(t_{ab} t_{bc})^3` and `t_{ab} t_{bc} t_{ab} t_{ac}^{-1}` for each triple
  representative `(a,b,c)`;
- (R4) `[t_{ab}, t_{cd}]` for each 4-tuple representative `(a,b,c,d)`.
This is finite.

**Step 2. The map to `W`.** Define `φ : P → W` by `σ ↦ σ` and `τ_i ↦ (p_i)`.
- (R0) holds in `G ≤ W`.
- (R1): `σ (p_i) σ^{-1} = (σ p_i) = (p_i)`.
- (R2)–(R4) hold because `φ(t_p) = g_p (p_i) g_p^{-1} = (p)`, and transpositions satisfy
  `((a b)(b c))^3 = 1`, `(a b)(b c)(a b) = (a c)` and `[(a b), (c d)] = 1` for distinct
  points.
- `φ` is surjective: its image contains `G` and every transposition.

**Step 3. Equivariance inside `P`.** Let `ι : G → P` be induced by (R0).
- For `g ∈ G` with `g p_i = p`: `g^{-1} g_p ∈ G_{p_i}` commutes with `τ_i` by (R1), so
  `ι(g) τ_i ι(g)^{-1} = t_p`. Hence `ι(x) t_p ι(x)^{-1} = t_{xp}` for all `x ∈ G` and all
  2-subsets `p`.
- Conjugating (R2)–(R4) by `ι(x)` shows that for *all* 2-subsets `p` and all injective
  triples and 4-tuples:
  `t_p^2 = 1`, `(t_{ab} t_{bc})^3 = 1`, `t_{ab} t_{bc} t_{ab} = t_{ac}`, `[t_{ab}, t_{cd}] = 1`.

**Step 4. The kernel side.** Let `N = ⟨t_p : p⟩ ≤ P`.
- `N` is normal: it is normalized by `ι(G)` (Step 3) and contains every `τ_i = t_{p_i}`
  (choose `g_{p_i} = 1`, or use Step 3).
- `P/N` is presented by `Σ ∪ {τ_i}` with all relators and `τ_i = 1`; that is `⟨Σ | R⟩`.
  So `P/N ≅ G`, and `φ` induces the identity `P/N → W/FSym(S) = G`.
- `φ(N) = FSym(S)`.

**Step 5. `φ|_N` is injective.** Let `C` be the group with generators `t_p`, one for each
2-subset `p`, and the relations of Step 3. There are surjections `C → N → FSym(S)`
sending `t_p ↦ t_p ↦ (p)`.
- For finite `F ⊆ S` with `|F| = n ≥ 2`, let `C_F` use only `p ⊆ F` and relations among
  them. Order `F = {1, ..., n}` and set `s_i = t_{i,i+1}`.
  - The `s_i` satisfy the Coxeter relations of type `A_{n−1}`: `s_i^2`,
    `(s_i s_{i+1})^3` and `[s_i, s_j]` for `|i − j| ≥ 2`.
  - Every `t_{ik}` with `i < k` is a word in the `s_j`, by `t_{ik} = t_{i,k−1} t_{k−1,k}
    t_{i,k−1}` and induction.
  - So `C_F` is a quotient of the Coxeter group `Sym(n)`. It maps onto `Sym(F)`, so
    `|C_F| = n!` and `C_F → Sym(F)` is an isomorphism.
- Every relation of `C` involves finitely many points, so `C = colim_F C_F`. The
  isomorphisms `C_F ≅ Sym(F)` are compatible, so `C → colim Sym(F) = FSym(S)` is an
  isomorphism.
- `C → FSym(S)` factors through `N`, so `N → FSym(S)` is injective.

**Step 6. Conclusion.** `φ` restricts to an isomorphism `N → FSym(S)` and induces an
isomorphism `P/N → G`. By the five lemma, `φ : P → W` is an isomorphism, so `W` is
finitely presented.

**Where the hypotheses enter.** Finite presentation of `G` gives (R0), condition 2 gives
(R1), and condition 1 makes (R3)–(R4) finite. Freeness of an infinite action violates
condition 1, which is why this does not contradict `lampshuffler-groups-are-not-fp2-over-q`.
