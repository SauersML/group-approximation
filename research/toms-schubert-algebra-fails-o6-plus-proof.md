---
rg: 2
id: toms-schubert-algebra-fails-o6-plus-proof
kind: route
title: Common lower bounds give an approximate 2-norm equivalence, which Toms's degeneracy point and atom forbid
target: toms-schubert-algebra-fails-o6-plus
requires: []
artifacts:
  - research/artifacts/toms-schubert-o6-plus-failure-2026-09-12.md
---

Full proof: Sections 1–4 of the artifact. Imports, all read from the sources
named there:
- Toms arXiv:2606.12188v2: total degeneracy of `(p_i, q_i)` at every stage (end of
  Section 5), and Proposition 4 (3), (4) and the `E_(n,m)` estimate in its proof.
- Thiel CMP 377 (2020): 2.12 (Rørdam's lemma), 2.13, 2.14, Theorem 4.7,
  Theorem 6.4, Remark 6.5, Theorem 7.5.

1. **Near projections.** Suppose the support gap `G` is below `delta^2/8` for some
   `eps`. Rørdam's lemma applied to `c <~ p_m` gives `x` with `xx* = (c - eps)_+` and
   `x*x in p_m M_k(B) p_m`. Rescaling by `g_2((c - eps)_+)` gives `x'` with
   `x'x'* = h_eps(c) =: e` and `z_P = x'*x' = g(x*x) <= p_m`.
   - Trace identities for `xx*` versus `x*x`, together with `h_eps >= h_(2 eps)` and
     `h_eps^2 >= h_(2 eps)`, give `k tau^(k)(p_m - z_P) <= G` and
     `k tau^(k)(z_P - z_P^2) <= G`.
   - The same holds for `q̂_m`, with `y'` and `z_Q`.
2. **Approximate equivalence.** `b = y'* x' in q̂_m M_k(B) p_m` satisfies `b*b = z_P^2`
   and `bb* = z_Q^2`. Hence `||p_m - b*b||_(2,u)^2 <= 2G/k < delta^2/(4k)`, and the same
   for `q̂_m - bb*`.
3. **Toms's estimate.** Approximate `b` in norm by a contraction `b_n` at a late stage
   and compress to `c_n = q̂_n b_n p_n`.
   - The branch projection `E_(n,m)` bounds the error:
     `||p_n - c_n* c_n||_(2,u) <= ||p_m - b*b||_(2,u) + 2||b - b_n|| + sqrt(eta_m)`.
   - By total degeneracy, `c_n(x) = 0` at some `x in X_n`.
   - The trace `tau_x` with `mu_x({x}) >= delta` and the fibre bound
     `tr(p_n(x)) >= delta/k` give `||p_n - c_n* c_n||_(2,u) >= delta/sqrt(k)`.
   - These bounds contradict each other, since `sqrt(eta_m) <= delta/(2 sqrt k)`.
4. **Corollaries.**
   - Dini's theorem turns a continuous rank into support gaps tending to
     `sup (d(p_m) - d(c))`, which gives B.
   - Thiel's Theorem 7.5 with the constant infimum `d(p_m) ∧ d(q̂_m) = d(p_m)` gives C.
   - Theorem 6.4 and Remark 6.5 give D.
