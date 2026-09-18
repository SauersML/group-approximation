---
rg: 2
id: gjs-guided-blueprints-are-computable-over-decidable-groups-proof
kind: route
title: Decidable ball growth sequence, greedy shortlex selection in the GJS Theorem 5.3.3 construction, Lemma 5.3.5 for the Delta test, maximal disjointness for the recurrence set
target: gjs-guided-blueprints-are-computable-over-decidable-groups
requires: []
---

**Route. COMPLETE.** This is a hand proof. The literature inputs are quoted
verbatim below, from the arXiv:1201.0513 PDF text read on 2026-09-17. Line
breaks are normalised, and sub- and superscripts are written `D^n_k`.

## Imports (GJS, arXiv:1201.0513)

- **Definition 5.3.2.** "A growth sequence is a sequence (Hn)n∈N of finite
  subsets of G satisfying: (i) 1G ∈ H0; (ii) ⋃n∈N Hn = G; (iii)
  Hn−1(H0^−1 H0)(H1^−1 H1) · · · (Hn−1^−1 Hn−1) ⊆ Hn for each n ≥ 1; (iv) for
  each n ≥ 1, if ∆ ⊆ Hn has the property that gHn−1 ∩ ∆Hn−1 ≠ ∅ whenever
  gHn−1 ⊆ Hn, then |∆| ≥ 3."
- **Theorem 5.3.3.** "Let G be a countably infinite group and let (Hn)n∈N be a
  growth sequence. Then there is a maximally disjoint, centered, directed
  blueprint (∆n, Fn)n∈N satisfying (i) F0 = H0; (ii) Fn ⊆ Hn for all n ≥ 1;
  (iii) for all n ≥ 1 the D^n_{n−1}-translates of Fn−1 are contained and
  maximally disjoint within Hn; (iv) for all n ≥ 1 and 0 ≤ k < n the
  D^n_k-translates of Fk are maximally disjoint within Hn−1."
  - Its proof, in part: "Choose δ^n_{n−1} so that 1G ∈ δ^n_{n−1} and the
    δ^n_{n−1}-translates of Fn−1 are contained and maximally disjoint within
    Hn. [...] let δ^n_k be such that the δ^n_k-translates of Fk are contained
    and maximally disjoint within B^n_k − ⋃_{k<m<n} δ^n_m Fm where
    B^n_k = {g ∈ G : {g}(F_{k+1}^−1 F_{k+1})(F_{k+2}^−1 F_{k+2}) · · ·
    (F_{n−1}^−1 F_{n−1}) ⊆ Hn}. [...] Finally, define Fn = ⋃_{0≤k<n} δ^n_k Fk.
    [...] The Fn's and δ^n_k's satisfy the assumptions of Lemma 5.3.1. So if
    (∆n)n∈N is as defined in the proof of that lemma, then (∆n, Fn)n∈N is a
    centered and directed pre-blueprint."
  - The proof uses no property of the sets δ^n_k other than those stated in
    the quoted choice. So every choice of δ^n_k with those properties gives
    the conclusion of Theorem 5.3.3.
- **Proof of Lemma 5.3.1.** "define D^k_k = {1G}, D^{k+1}_k = δ^{k+1}_k, and in
  general for n > k D^n_k = ⋃_{k≤m<n} δ^n_m D^m_k." Also "For k ∈ N we define
  ∆k = ⋃_{n≥k} D^n_k". And from (Uniform): "∆k ∩ γFn = γD^n_k for k < n and
  γ ∈ ∆n".
- **Lemma 5.3.5.** "Let G be a countably infinite group and let (∆n, Fn)n∈N be
  a blueprint guided by a growth sequence (Hn)n∈N. Then (i) If (∆n, Fn)n∈N is
  centered, then it is directed and maximally disjoint within G; (ii)
  Hn ⊆ Fn+2 F0^−1 for all n ∈ N; (iii) ψFk ∩ γHn ≠ ∅ =⇒ ψFk ⊆ γHn+1 =⇒
  ψFk ⊆ γFn+2, for all n ≥ k, [...]"
- **Lemma 2.4.5.** "Let G be a countable group and x ∈ k^G. Then [x] is a
  minimal subflow iff for every finite A ⊆ G there exists a finite T ⊆ G such
  that ∀g ∈ G ∃t ∈ T ∀a ∈ A x(gta) = x(a)."
- **Definition 5.1.1.** "We say that the ∆-translates of A are maximally
  disjoint within B if the following properties hold: (i) for all γ, ψ ∈ ∆, if
  γ ≠ ψ then γA ∩ ψA = ∅; (ii) for every g ∈ G, if gA ⊆ B then there exists
  γ ∈ ∆ with gA ∩ γA ≠ ∅. [...] we say that the ∆-translates of A are
  contained and maximally disjoint within B if the ∆-translates of A are
  maximally disjoint within B and ∆A ⊆ B."
- **Identity elements.** In the construction below, `1 ∈ Delta_n` and `1 ∈ F_n` for all `n`.
  Both hold here: `1 ∈ F_0 = H_0`, and `1 ∈ δ^n_{n-1}` gives
  `F_{n-1} ⊆ F_n`.

## Proof

**Step 0: conventions.** Fix a finite symmetric generating set.
- The normal form of an element is the shortlex least word representing it,
  and it is found by enumerating words and testing equality with the word
  problem.
- Every finite set below is a finite list of normal forms. `B(R)`, products
  `XY`, inverses and inclusion tests `X ⊆ Y` are computable from these lists.
- "Computable" means uniformly in all indices.

**Step 1: a computable growth sequence.**
- Put `H_0 = {1}`.
- For `n >= 1`, given `H_0, ..., H_{n-1}`, let
  `P_n = H_{n-1}(H_0^-1 H_0) ··· (H_{n-1}^-1 H_{n-1})`, a computable finite set.
- For `R >= n`, put `K_R = P_n ∪ B(R)`. Let `H_n = K_R` for the least `R >= n`
  such that `K_R` satisfies clause (iv) of Definition 5.3.2.

*Clause (iv) is decidable for a finite candidate `K`.*
- By induction, `1 ∈ H_{n-1}`, since `1 ∈ P_{n-1} ⊆ H_{n-1}`.
- So `gH_{n-1} ⊆ K` forces `g ∈ K`, and the set
  `{g ∈ K : gH_{n-1} ⊆ K}` is a computable finite list.
- A set `Δ` with `|Δ| <= 2` violates (iv) iff it meets all these translates in
  the stated sense. The number of such `Δ ⊆ K` is finite, and each test is a
  finite computation.
- So (iv) holds iff no `Δ ⊆ K` with `|Δ| <= 2` passes the test.

*Some `R` works, so the search halts.*
- Put `S = H_{n-1} H_{n-1}^-1`.
- Suppose `δ ∈ Δ` witnesses `g_i H_{n-1} ∩ δ H_{n-1} ≠ ∅` and
  `g_j H_{n-1} ∩ δ H_{n-1} ≠ ∅`. Then `g_i, g_j ∈ δ S`, so `g_j ∈ g_i S^-1 S`.
- `G` is infinite and `S^-1 S` is finite. So there are `g_1, g_2, g_3` with
  `g_j ∉ g_i S^-1 S` for `i ≠ j`, chosen one at a time outside a finite union
  of translates.
- For `R >= max |g_i h|` over `i` and `h ∈ H_{n-1}`, each `g_i H_{n-1}` lies in
  `K_R`.
- A `Δ` meeting all translates must then use a different `δ` for each `g_i`.
  So `|Δ| >= 3`, and (iv) holds for `K_R`. The search tests each `R` in turn
  and halts at the first success.

*The other clauses.*
- (i) holds because `H_0 = {1}`.
- (iii) holds because `P_n ⊆ H_n`.
- (ii) holds because `B(n) ⊆ H_n`.

So `(H_n)` is a growth sequence, and `n ↦ H_n` is computable.

**Step 2: a computable blueprint (item 1).** Run the construction quoted from
the proof of Theorem 5.3.3 on `(H_n)`. Make every choice of a `δ^n_k` by the
greedy procedure below.

*Greedy procedure `Greedy(X, F, seed)`.* The inputs are a finite list `X`, a
finite `F ∋ 1`, and optionally `seed = 1` when `F ⊆ X`.
- Start with `Kept = [seed]`, or `Kept = []` if there is no seed.
- Scan the elements `g ∈ X` in shortlex order. Append `g` to `Kept` iff
  `gF ⊆ X` and `gF` is disjoint from `dF` for every `d` already in `Kept`.
- Output `Kept`.

*Correctness.*
- Every kept `g` has `gF ⊆ X`, and kept translates are pairwise disjoint.
- Let `gF ⊆ X`. Since `1 ∈ F`, `g ∈ X`, so `g` was scanned. It was kept, or
  it was rejected because `gF` meets a kept translate.
- So the `Kept`-translates of `F` are contained and maximally disjoint within
  `X` (Definition 5.1.1).
- The procedure is a finite computation.

*The construction.*
- `F_0 = H_0`.
- Given `F_0, ..., F_{n-1}`, put
  `δ^n_{n-1} = Greedy(H_n, F_{n-1}, 1)`. The seed is allowed because
  `F_{n-1} ⊆ H_{n-1} ⊆ P_n ⊆ H_n`.
- Then, for `k = n-2, ..., 0`:
  - `B^n_k = {g ∈ H_n : g Q^n_k ⊆ H_n}`, where
    `Q^n_k = (F_{k+1}^-1 F_{k+1}) ··· (F_{n-1}^-1 F_{n-1})`.
  - This equals the quoted `B^n_k`, because `1 ∈ Q^n_k` forces `g ∈ H_n`.
  - `δ^n_k = Greedy(B^n_k − ⋃_{k<m<n} δ^n_m F_m, F_k, none)`.
- `F_n = ⋃_{0<=k<n} δ^n_k F_k`.
- `D^n_k` is given by the quoted recursion.

All of these are computable finite lists. The chosen `δ^n_k` have exactly the
properties required in the quoted proof. So Theorem 5.3.3 and its proof apply
verbatim: `(Delta_n, F_n)`, with `Delta_k = ⋃_{n>=k} D^n_k`, is a maximally
disjoint, centered, directed blueprint satisfying (i)–(iv) of Theorem 5.3.3,
that is, guided by `(H_n)` (Definition 5.3.4).

**Step 3: decidable Delta (item 2).** Let `n >= k` and `g ∈ H_n`.
- (`<=`) `D^{n+2}_k ⊆ Delta_k` by definition of `Delta_k`.
- (`=>`) Let `g ∈ Delta_k`.
  - Since `1 ∈ F_k`, `g ∈ gF_k ∩ H_n`. So `gF_k ∩ 1·H_n ≠ ∅`.
  - Lemma 5.3.5(iii), with `ψ = g` and `γ = 1`, gives `gF_k ⊆ F_{n+2}`. So
    `g ∈ Delta_k ∩ F_{n+2}`.
  - The quoted (Uniform) identity, with `γ = 1 ∈ Delta_{n+2}` (centered) and
    `k < n+2`, gives `Delta_k ∩ F_{n+2} = D^{n+2}_k`. So `g ∈ D^{n+2}_k`.
- *Decision procedure.* Given `(g,k)`, compute `H_0, H_1, ...` until the
  first `n >= k` with `g ∈ H_n`, which exists by (ii). Then test
  `g ∈ D^{n+2}_k`.

**Step 4: recurrence set (item 3).**
- Let `x`, `A` and `n` be as in item 3, and let `g ∈ G`.
- The blueprint is centered and guided, so by Lemma 5.3.5(i) the
  `Delta_n`-translates of `F_n` are maximally disjoint within `G`.
- Since `gF_n ⊆ G`, clause (ii) of Definition 5.1.1 gives `γ ∈ Delta_n` and
  `f, f' ∈ F_n` with `gf = γf'`.
- Put `t = f f'^-1 ∈ F_n F_n^-1`. Then `gt = γ`, and `x(gta) = x(γa) = x(a)`
  for all `a ∈ A`.
- If `A ↦ n(A)` is computable, then `T(A) = F_{n(A)} F_{n(A)}^-1` is a
  computable finite set satisfying the condition of Lemma 2.4.5. So `[x]` is
  minimal.

**Closing.** Items 1–3 are established. Nothing in this route depends on
finite presentability. Solvable word problem and infinitude are the only
hypotheses used, in Steps 0 and 1.
