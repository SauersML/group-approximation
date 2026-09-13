---
rg: 2
id: hls-ghost-projection-breaks-k-exactness
kind: claim
title: Higson--Lafforgue--Skandalis - an expander's kernel projection in l^inf(N; c_0(G)) x|_r G has rank one at every level and dies modulo c_0(N x G), so K-theory is not exact at the middle
distinct_from:
  monster-bc-detector-lives-on-a-proper-orbit-ideal: that imports Finn-Sell's groupoid recasting at C_0(Omega_(beta X)); this imports HLS's own Section 7 group-action construction, their Lemma 1, and Yu's remark.
  reduced-group-algebras-contain-no-nonzero-ghosts: that says a reduced group algebra has no nonzero ghosts, which kills ghost classes with trivial coefficients; this is the coefficient-level non-exactness HLS prove with a ghost projection over l^inf(N; c_0(G)).
---

**ESTABLISHED (citation)** by `hls-ghost-projection-breaks-k-exactness-citation`. Read verbatim from N. Higson,
V. Lafforgue, G. Skandalis, *Counterexamples to the Baum--Connes conjecture*, GAFA 12 (2002) 330--354.

**Section 7 (pp. 350--352).**
- **Setup.** `G` is finitely generated, `(X_n)` is a sequence of `(k, ε)` expanding graphs, and `ϕ_n : X_n^0 -> G` are
  uniformly Lipschitz with maximal fibre fraction tending to `0`. Let `A = ℓ^∞(N; c_0(G))`.
- **The projection.**
  - `D_n = θ_n^* ∆_n θ_n + (1 - θ_n^* θ_n)` has a one-dimensional kernel and is bounded below by `min(ε, 1)` off it.
  - The kernel projection `p` of `D = ⊕ D_n` lies in `A ⋊_r G`.
- **Results.**
  - `π_n([p]) = 1` for every `n`, so `[p]` does not come from `K_0(c_0(N × G) ⋊_r G) = ⊕_n Z`.
  - The image of `p` in `(A / c_0(N × G)) ⋊_r G` is `0`, by HLS Lemma 9.
  - Hence `K_0(c_0(N×G) ⋊_r G) -> K_0(A ⋊_r G) -> K_0((A/c_0(N×G)) ⋊_r G)` is not exact at the middle.
  - A direct-limit argument then gives a compact metrizable `G`-space for which Baum--Connes fails.

**Lemma 1 (p. 335).** Suppose the reduced K_0 sequence of a closed saturated decomposition is not exact at the middle.
1. If Baum--Connes for the closed part is injective, Baum--Connes for the whole fails to be surjective.
2. If `K_0` max-to-reduced for the closed part is injective, then `K_0` max-to-reduced for the whole fails to be
   surjective, and so does Baum--Connes.

**Remark 12 (p. 352).** "Guoliang Yu has pointed out that ... the Baum–Connes map for the crossed-product A ⋊_r G ... is
never surjective."

**Section 6 (pp. 348--349).** The same projection in the Roe algebra of a coarse disjoint union of expanders:
- its blocks have all entries `|X_n|^(-1)`;
- its class does not come from `K(ℓ^2(X))`, because its image in `K_0(∏ K / ⊕ K)` is `(1, 1, ...)`.
