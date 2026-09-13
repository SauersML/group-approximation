---
rg: 2
id: fpbs-simple-generating-set-with-gap-exists-citation
kind: route
title: Import Thom's small spectral radius theorem and the Pak--Smirnova-Nagnibeda gap criterion
target: fpbs-simple-generating-set-with-gap-exists
requires: []
---

This imports two results. Both PDFs were fetched on MSI on 2026-09-12 into
`/projects/standard/hsiehph/sauer354/jnt/` (`thom-v1.pdf`, `jn-v3.pdf`) and read
page by page.
- **Thom, *A remark about the spectral radius*, arXiv:1306.1767v1, Theorem 1
  (p.2):** "Let Γ be a finitely generated non-amenable group and Σ be a finite
  symmetric generating set. For every k ∈ ℕ there exists a symmetric set
  S_k ⊂ Σ^k such that ρ(S_k) ≤ 4k·ln(|Σ|)·ρ(Σ)^k. Moreover, for every ε > 0,
  there exists a finite symmetric generating set S ⊂ Γ such that ρ(S) < ε."
  Here `S` is a subset of `Gamma` with `S^{-1} = S`, and
  `rho(S) = || |S|^{-1} sum_{s in S} lambda(s) ||` on `l^2(Gamma)` (p.1). Lemma 2,
  Corollary 4 and the proof of Theorem 1 (pp.2--4) were checked line by line. The
  one harmless slip is recorded in
  `research/artifacts/jn-simple-gap-via-thom-2026-09-12.md` §3.
- **Juschenko--Nagnibeda, *Small spectral radius and percolation constants on
  non-amenable Cayley graphs*, arXiv:1206.2183v3, Proposition 3 (p.3):** "If
  ρ(Γ,S) < 1/2, then p_c(Γ,S) < p_u(Γ,S)." They credit it to Pak--Smirnova-Nagnibeda,
  C. R. Acad. Sci. Paris 330 (2000) 495--500, as a corollary of their Theorem 2
  (Benjamini--Schramm, ECP 1 (1996) 71--82): "If ρ(Γ,S)p_c(Γ,S)|S| < 1, then
  p_c(Γ,S) < p_u(Γ,S)." Artifact §4 re-derives Proposition 3 from Theorem 2 and
  the Benjamini--Schramm bound `p_c <= 1/(phi+1)` quoted on the same page.
  Neither the 1996 paper nor the 2000 paper was re-read.

Thom states the percolation consequence himself, as Corollary 8 (p.5): "there
exists a finite symmetric set of generators S in Γ such that
p_c(Γ,S) < p_u(Γ,S)." Juschenko--Nagnibeda v3 p.6: "Andreas Thom proved [19]
that the spectral radius of any non-amenable group can be arbitrarily small,
thus answering our Question 6 (1)."

**Removing the identity.** Thom's set may contain `e`, which puts a loop at every
vertex. Take `S_0` from Theorem 1 with `rho(S_0) < 1/4`, and put `S = S_0 \ {e}`.
1. `S_0` is symmetric, so `rho(S_0)^2 >= tau(m(S_0)^2) = 1/|S_0|`, and
   `|S_0| > 16`.
2. If `e` is not in `S_0`, then `S = S_0`. Otherwise the two sums
   `sum_{s in S} lambda(s)` and `sum_{s in S_0} lambda(s)` differ by
   `lambda(e) = I`. Either way `rho(S) <= (|S_0|/4 + 1)/(|S_0| - 1) <= 1/3`.
   The bound decreases in `|S_0|` and equals `1/3` at `|S_0| = 16`.
3. `S` is symmetric, still generates `Gamma`, and has no loops. As a set it has no
   multiple edges. Proposition 3 gives `p_c < p_u` on its Cayley graph.
