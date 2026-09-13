---
rg: 2
id: o6-plus-tracial-equivalence-proof
kind: route
title: Thiel's attained infimum below both projections, Dini's theorem, and Rørdam rescaling give an approximate partial isometry
target: o6-plus-forces-tracial-equivalence-of-equal-trace-projections
requires: []
artifacts:
  - research/artifacts/toms-schubert-o6-plus-failure-2026-09-12.md
---

Imports, read from arXiv:1711.04721v3 on 2026-09-12:
- Paragraph 2.12, Rørdam's lemma;
- Proposition 2.13, (O5) and (O6) for every C*-algebra;
- Paragraph 2.14, the correspondence between quasitraces and functionals;
- Theorem 4.7, Edwards' condition for unital algebras;
- Theorem 7.5, attained functional infima under (O5), (O6+) and Edwards.

Exactness gives `QT(A) = T(A)` (Haagerup).

1. **An attained meet.** `Cu(A)` is countably based, simple and stably finite, and
   `u = [1]` is compact and full. By Theorem 7.5, with `a = [p]`, `b = [q]`, there is
   `c in (A tensor K)_+` with `c <~ p`, `c <~ q` and `d(c) = d(p) ∧ d(q)`. Since
   `d(p) = d(q)`, `d(c) = d(p) = tau tensor Tr(p)`, which is continuous and finite.
2. **Dini.** Put `h_eps(t) = min(1, max(0, (t - eps)/eps))`. By Rørdam's lemma
   `(c - eps)_+ = xx*` with `x*x in p M_k(A) p`. So
   `tau -> tau tensor Tr(h_(2 eps)(c))` equals `tau tensor Tr(g'(x*x))` for a
   continuous `g'` vanishing near `0`. It is therefore continuous, and it increases
   to `d(c)` as `eps` decreases. Dini's theorem on the compact `T(A)` gives
   `G_eps := sup_tau (d_tau(p) - tau tensor Tr(h_(2 eps)(c))) -> 0`.
3. **Near projections and the partial isometry.** This is Steps 1–2 of Section 3 of
   the artifact, which use only `c <~ p, q` and the definition of `G_eps`.
   - Put `g(t) = min(1, t/eps)`, `g_2(t) = (g(t)/t)^(1/2)` (bounded, equal to
     `eps^(-1/2)` on `[0, eps]`), and `x' = g_2((c - eps)_+) x`.
   - Since `x* F(xx*) x = (tF)(x*x)`, we get `x'x'* = h_eps(c)` and
     `z_P = x'*x' = g(x*x) <= p`.
   - Trace identities between `xx*` and `x*x`, with `h_eps >= h_(2 eps)` and
     `h_eps^2 >= h_(2 eps)`, give `k tau^(k)(p - z_P) <= G_eps` and
     `k tau^(k)(z_P - z_P^2) <= G_eps`.
   - Similarly `y'` and `z_Q` for `q`.
   - `b = y'* x' in q M_k(A) p` has `b*b = z_P^2` and `bb* = z_Q^2`. So
     `||p - b*b||_(2,u)^2 <= 2 G_eps / k`, and the same for `q - bb*`.
4. Choose `eps` with `2 G_eps / k < eps_0^2`. Along `eps_n -> 0` the contractions
   `b_n` define `b in M_k(A^omega)` with `b*b = p` and `bb* = q`. Square.
