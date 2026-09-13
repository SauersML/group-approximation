# Juschenko--Nagnibeda Question 6(1) through Thom: source check

Lane `jn-simple-gap-via-thom`, 2026-09-12. This backs the claim `fpbs-simple-generating-set-with-gap-exists`
and the route `fpbs-simple-generating-set-with-gap-exists-citation`. **Verdict:** the claim is Thom's
Corollary 8 with the identity removed from the set. It answers Juschenko--Nagnibeda (JN)
Question 6(1) exactly as posed. It is a literature import and contains nothing new.

## 1. Sources
- A. Thom, *A remark about the spectral radius*, arXiv:1306.1767v1 (7 Jun 2013).
- K. Juschenko, T. Nagnibeda, *Small spectral radius and percolation constants on
  non-amenable Cayley graphs*, arXiv:1206.2183v3 (13 Mar 2015).

Both were fetched by curl on MSI into `/projects/standard/hsiehph/sauer354/jnt/`,
copied back with `msi get`, and read page by page (Thom pp.1--5, JN in full). Not re-read, and
used only through JN's quotations: Pak--Smirnova-Nagnibeda (PSN), C. R. Acad. Sci. Paris 330
(2000) 495--500, not on arXiv; and Benjamini--Schramm (BS), Electron. Comm. Probab. 1 (1996)
71--82, whose MSI fetch returned HTML. In JN's bibliography, [4] is BS, [17] PSN, [19] Thom.

## 2. Exact statements
- **JN pp.1--2.** `S` is "a finite symmetric generating set".
  `rho(Gamma,S) = |S|^{-1} ||sum_{g in S} lambda(g)||` and `phi(Gamma,S) = inf_F |d_E F|/|F|`.
  Their (1) reads `|S|(1-rho)/(|S|-1) <= h(Gamma,S) = phi(Gamma,S)/|S|`.
- **JN abstract.** "does there exist a generating set S such that the Cayley graph (Γ,S),
  without loops and multiple edges, has non-unique percolation, i.e., p_c(Γ,S) < p_u(Γ,S)?"
- **JN p.3.** `p_c(Gamma,S) <= 1/(phi(Gamma,S)+1)` ([4]). Theorem 2 ([4]): "If
  ρ(Γ,S)p_c(Γ,S)|S| < 1, then p_c(Γ,S) < p_u(Γ,S)." Proposition 3 ([17]): "If
  ρ(Γ,S) < 1/2, then p_c(Γ,S) < p_u(Γ,S)."
- **JN p.4, "simple".** "S^(k) stands here for the k-th power of the set S ∪ {e_G}
  understood as a multiset, so that the corresponding Cayley graph has lots of multiple
  edges. [...] Here simple means that the corresponding Cayley graph is a graph without
  loop or multiple edge. [...] From now on, by generating set we will only mean simple
  generating set."
- **JN Definition 5 (p.4).** "there exists a sequence of finite generating sets
  {A_l}_{l≥1} ⊂ Γ such that ρ(Γ,A_l) → 0, as l → ∞. We then say that Γ has
  infinitesimally small spectral radius with respect to the family of generating sets {A_l}_{l≥1}."
- **JN Question 6 (p.4).** "(1) Does every non-amenable group have infinitesimally small
  spectral radius with respect to some family of generating sets? (2) With respect to
  some family of the form {S^k}_{k≥1}? (3) With respect to {S^k}_{k≥1} for any generating set S?"
- **JN p.6.** "One year after this work first appeared on Arxiv, Andreas Thom proved [19]
  that the spectral radius of any non-amenable group can be arbitrarily small, thus
  answering our Question 6 (1)."
- **Thom p.1.** "a set is called symmetric if S^{-1} = S". He defines
  `m(S) = |S|^{-1} sum_{s in S} s` and `rho(S) = ||m(S)||`, the same number as JN's `rho(Gamma,S)`.
  Theorem 1 (p.2) is quoted verbatim in the route.
- **Thom p.5, §3.2.** "We can improve on [7, Theorem 1] and can get around the implicit use
  of multi-sets in the statement of the theorem." Corollary 8: "Let Γ be a finitely generated
  non-amenable group. Then there exists a finite symmetric set of generators S in Γ such
  that p_c(Γ,S) < p_u(Γ,S)." Proof: "Having Theorem 1 at hand, the proof proceeds as in [7]."

## 3. Check of Thom's proof (pp.2--4)
- **Lemma 2.** Put `alpha = 1/(-4 ln I) <= 1/4` and suppose `x f(x) < alpha I` for every `x`.
  1. Then `f <= min{1, alpha I/x}`, and his (2) gives `3/(4 alpha) <= -ln(alpha I)`.
  2. Since `ln t < t/2` for `t > 0`, this forces `1/(4 alpha) < -ln I`.
  3. That contradicts the definition, which gives `1/(4 alpha) = -ln I`.
- **Corollary 4.** Let `b` be `a_{g_N}` times the indicator of `{g : a_g >= a_{g_N}}`. It is
  symmetric, satisfies `0 <= b <= a`, and has `||b||_1 >= ||a||_1/(4 ln size(a))`.
- **Theorem 1, first part.** Apply (1) to `0 <= b_k <= m(Sigma)^k` and use
  `|Sigma^k| <= |Sigma|^k`. Corollary 4 needs `size(m(Sigma)^k) >= 3`. That holds:
  right multiplication by one `s` maps `Sigma^{k-1}` injectively into `Sigma^k`, so
  `|Sigma^k| >= |Sigma| >= 3`.
- **Slip, second part.** For `S'_n = S_n ∪ Sigma`, the printed triangle inequality puts
  `rho(Sigma)` on the second term. That term is `|Sigma \ S_n| ||m(Sigma \ S_n)||`, and
  the only available bound is `||m(Sigma \ S_n)|| <= 1`. The correct estimate is
  `rho(S'_n) <= rho(S_n) + |Sigma| rho(S_n)^2`. This is still `O(n rho(Sigma)^n)`, so the
  conclusion stands. `S'_n` is symmetric and generating, and it may contain `e`.

## 4. Proposition 3 from Theorem 2
1. By JN (1), `phi = |S| h >= |S|^2 (1-rho)/(|S|-1) >= |S|(1-rho)`.
2. With `p_c <= 1/(phi+1)`, this gives `rho p_c |S| <= rho|S|/(|S|(1-rho)+1) < rho/(1-rho)`.
3. The right side is below 1 when `rho < 1/2`, and Theorem 2 gives `p_c < p_u`.

## 5. Removing the identity
Let `rho(S_0) < epsilon <= 1/4` and `n = |S_0|`.
1. `tau(m(S_0)^2) = 1/n` gives `n > epsilon^{-2}`.
2. Then `rho(S_0 \ {e}) <= (epsilon n + 1)/(n-1)`.
3. This is at most `(4/3) epsilon` iff `n >= 3/epsilon + 4`.
4. `epsilon^{-2} >= 3/epsilon + 4` iff `(4 epsilon - 1)(epsilon + 1) <= 0`, which holds.

So `A_l = S_0(epsilon_l) \ {e}` with `epsilon_l -> 0` are simple symmetric generating sets
with `rho(Gamma,A_l) -> 0`, as Definition 5 requires.

## 6. Gap analysis
- **Finite and symmetric.** JN assume symmetry on p.1, and the claim asks for it. Thom's sets are both.
- **Set, not multiset.** Thom's `supp(b_k)` and `S_n ∪ Sigma` are subsets of `Gamma`, so no
  multiple edges arise. §3.2 names this improvement.
- **No loops.** `S_n ⊂ Sigma^n` contains `e` for even `n`. §5 removes it at a cost of a factor `4/3`.
- **Spectral radius.** JN's `rho(Gamma,S)` and Thom's `rho(S)` are the same norm.

**Outcome: no gap.** Question 6(1) has a positive answer, as JN v3 p.6 records. Theorem 1
does not answer Questions 6(2) and 6(3), about the full powers `S^k`, and the claim does not need them.

## 7. Credit and graph effect
Credit: Thom for Theorem 1 and Corollary 8; PSN for Proposition 3; BS for Theorem 2 and the
bound on `p_c`; JN for the question and the exposition used here. Removing `e` is a routine
remark, and no novelty is claimed.

`fpbs-bs-via-generating-set-invariance` also needs the open
`fpbs-nonuniqueness-phase-is-a-group-invariant`, so `fpbs-benjamini-schramm-universal` stays open.
