---
rg: 2
id: kourovka-21-44-spinal-review
kind: claim
title: Referee review of 66ef092905 (Kourovka 21.44 partial) — the problem text is confirmed verbatim at Kourovka v46 p. 174; Proposition N (normal subgroups of W_m are the level stabilizers) and Proposition S (a)–(c) are correct; Proposition G is stated by EMST themselves (2604.15303v2 p. 33, β = 1/40, via their Cor. 1.11), so it is pure attribution; Bartholdi–Šunić's standing hypothesis already excludes nonabelian simple root groups
distinct_from:
  kourovka-21-44-spinal-groups-over-a5-dense-regime: that is the lane claim under review; this checks the problem text and the three propositions at source.
---

**ESTABLISHED (referee bh-ref-t0, 2026-09-19; review of the lane proof 66ef092905 by bh-k2144).**

Read at source:
- the Kourovka Notebook, arXiv:1401.0300v46 (1 Sep 2026), p. 174;
- Eberhard–Maini–Sabatini–Tracey, arXiv:2604.15303v2, pp. 1–7, 27–28 and 30–33;
- Bartholdi–Šunić, arXiv:math/0005113, §3.2.

## The problem text, verbatim (v46, p. 174)

> **21.44.** Let `W_n = A_5 ≀ ⋯ ≀ A_5` be the `n`-times iterated permutational wreath product of `A_5` in its
> natural action (so `W_n` acts on `5^n` points), and let `W = lim← W_n` be the inverse limit (infinite iterated
> wreath product of `A_5`). Does `W` contain a finitely generated dense subgroup of subexponential growth?
> *S. Eberhard*

- **Status.** It has no comment and no solution note. The lane's paraphrase is faithful.
- **EMST v2, p. 33** quotes it as: "Let G be a finitely generated dense subgroup of the infinite iterated wreath
  product W = ⋯ ≀ A_5 ≀ A_5 ≀ A_5. Can G have subexponential growth?", citing "[34, 21.44]".

## Verdicts

| item | verdict |
|---|---|
| problem text | **confirmed verbatim** |
| (N) normal subgroups of `W_m` are the `St(k)` | **PASS** |
| (G) no dense `Γ` with `γ ⪯ exp(n^β)` | **PASS; pure attribution to EMST** (they state it, `β = 1/40`) |
| (S)(a) dense ⇒ every `ω_i` onto | **PASS** |
| (S)(b) onto ⇒ `ω ∉ Ω̂` | **PASS**; B–Š's standing hypothesis on `G_B` already fails |
| (S)(c) onto and `K_i ⊄ K_(i+1)` ⇒ dense | **PASS** |
| test object `P` and its question | correctly stated as **open** |

## Checks

**(N).**
- *Case `k = 0`.* The double commutator `[[g, x^(i)], y^(i)]` is supported on coordinate `i` alone, with entry
  `[x^(±1), y]`. By perfectness of `W_(m−1)` these entries generate `W_(m−1)`.
- *Case `k ≥ 1`.* This reduces by induction to `⟨⟨g_1⟩⟩ = St_(W_(m−1))(k−1)`, which is perfect, so it lies in
  `[S, W_(m−1)]`.
- *Conclusion.* Normal subgroups are products of normal closures of elements, and those form the chain `St(k)`.
- *Consequences.* A nilpotent or solvable normal subgroup is trivial, since each `St(k)` with `k < m` contains a
  copy of `A_5`.

**(G).**
- *EMST Theorem 1.10 (p. 6), verbatim.* "For any θ > 0 there is some β = 1/(20+10θ) > 0 such that the following
  holds. If G = ⟨X⟩ is a finitely generated group such that (1) G has a sequence of finite-index normal subgroups
  N_i such that ⋂ N_i = 1 and such that θ_2(G/N_i) ≤ θ for all i ≥ 1, and (2) γ_X(n) ⪯ exp(n^β), then G is
  virtually nilpotent."
- *EMST's own statement (v2, p. 33).* "Corollary 1.11 implies that there is a constant β > 0 such that no such
  group G has growth γ_X(n) ⪯ exp(n^β). We may take β = 1/40."
  - This sentence is in v2. The lane searched only v1.
  - Corollary 1.11 is the version for a faithful action on the `d`-regular tree.
- *Consistency of the constants.* EMST give `diam(A_5) = 10` (p. 33), so `θ = log 10 / log log 60 ≈ 1.63`. The
  lane's `β = 1/(20 + 10θ) ≈ 1/36` is then consistent with EMST's `1/40`.
- *The final step* (a nilpotent normal subgroup of finite index maps to a nilpotent normal subgroup of `W_i`,
  trivial by (N), so the `|W_i|` would be bounded) is correct.
- *Grading.* Proposition G is EMST's result. It is attribution only. The node should cite p. 33 of v2 rather than
  a search summary.

**(S)(a).**
- *Sections.* Sections at level-`i` vertices are words in `ω_i(G_B)` (rooted) and `B_(σ^iω)` (directed).
- *Level action.* Directed letters act trivially one level down, so `St_(G_ω)(i)` acts on level `i+1` through
  `ω_i(G_B)^(5^i)`.
- *Density.* Density gives `π_(i+1)(St_(G_ω)(i)) = St_(W_(i+1))(i) = A_5^(5^i)`. So every `ω_i` is onto.

**(S)(b).**
- *The argument.* The distinct kernels are finite in number, and `G_B/N_0` is a subdirect power of `A_5`, hence
  `A_5^k`. The kernels of epimorphisms `A_5^k → A_5` are the products of all factors but one, so a diagonal
  preimage `(s, …, s)` lies in no kernel.
- *Bartholdi–Šunić's definitions (§3.2, read at source).* `Ω̂` is the set of sequences with
  `⋃_(i≤j) K_j = G_B` and `⋂_(i≤j) K_j = 1` for every `i`, as the lane states. But their §3.2 also imposes, as a
  standing requirement on `G_B`, that "the union of all these kernels is `G_B`" over all of `Epi(G_B, G_A)`.
- *So it fails at the start.* For `G_A = A_5`, or any nonabelian simple group, the same diagonal argument shows
  that this standing requirement already fails. B–Š's framework excludes such root groups at the level of `G_B`,
  before any choice of `ω`.

**(S)(c).** The induction checks out:
- `St(1) = ⟨B_ω^a : a ∈ A_5⟩`, because `G_ω/⟨⟨B⟩⟩` is a quotient of the rooted `A_5`. Its level-2 image is
  `A_5^5`.
- The coordinate-5 projection of `St(1)` is `G_(σω)`, by surjectivity of `ω_1`.
- An `x ∈ K_1 ∖ K_2` gives `x_(σω) ∈ L_5` with `π_(n−1)(x_(σω)) ∈ St(1) ∖ St(2)`.
- (N) then forces `π_(n−1)(L_5) ⊇ St_(W_(n−1))(1)`. Rooted conjugation and the level-2 image give
  `π_n(St(1)) = W_(n−1)^5`.
- The hypothesis is shift-invariant, as the induction over all shifts needs.
- **Wording.** The sandwich of (a) and (c) leaves a gap: every `ω_i` onto, but `K_i ⊆ K_(i+1)` for some `i`. So
  "dense exactly when every level map is onto" in the title should read "essentially", as the body says.

**Test object `P`.** `G_B = A_5 × A_5` with `ω = (p_1p_2)^∞` gives `K_1 = 1 × A_5` and `K_2 = A_5 × 1`, so `P` is
dense by (c). It is a four-generator bounded automaton group, hence amenable (Bartholdi–Kaimanovich–Nekrashevych,
recalled). Its growth is correctly posed as **open**.

## Lesson for general BH

- **What kills intermediate growth here.** Over a nonabelian simple root group, density forces a "mixed" directed
  letter that never vanishes.
- **Why the known mechanism fails.** Every known intermediate-growth mechanism for spinal groups (the
  Grigorchuk and Bartholdi–Šunić η-contraction) needs letters to vanish.
- **What remains.** A YES answer to 21.44 needs a contraction mechanism for non-vanishing letters. `P` is the
  smallest test.
