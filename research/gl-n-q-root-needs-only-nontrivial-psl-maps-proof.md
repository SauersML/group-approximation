---
rg: 2
id: gl-n-q-root-needs-only-nontrivial-psl-maps-proof
kind: route
title: Simplicity of PSL_n(Q) plus block embeddings turn nontrivial homomorphisms into embeddings of every GL_n(Q)
target: gl-n-q-root-needs-only-nontrivial-psl-maps
requires:
  - gl-n-q-targets-are-cofinal-in-n
---

**Simplicity.** `PSL_n(K)` is simple for every field `K` and `n >= 2`, except
`n = 2` with `|K| <= 3` (Jordan--Dickson; e.g. E. Artin, *Geometric Algebra*,
1957, Ch. IV, Theorem 4.9; theorem number not re-checked at the source). For
`K = Q` there is no exception. The centre of `SL_n(Q)` is `{λI : λ in Q,
λ^n = 1}`, which is `{I}` for odd `n` and `{±I}` for even `n`. So `SL_n(Q)` is
simple for odd `n`.

**Cofinality.** `PSL_n(Q) -> PGL_n(Q)` is injective, because
`SL_n(Q) ∩ Q^x I` is the centre of `SL_n(Q)`. `PGL_n(Q) <= GL_(n^2)(Q)` and
`GL_n(Q) <= SL_(n+1)(Q)` are in `gl-n-q-targets-are-cofinal-in-n`. For
`k >= n + 2`, `h ↦ diag(h, 1, ..., 1)` maps `SL_(n+1)(Q)` injectively into
`PSL_k(Q)`: an element with a trailing diagonal entry `1` is a scalar only if
it is `I`.

**Equivalence.** A nontrivial homomorphism from a simple group is injective.
- (a) ⇒ (b): `PSL_n(Q) <= GL_(n^2)(Q)`, so `P(PSL_n(Q))`; take `X = PSL_n(Q)`.
- (b) ⇒ (a): `P(PSL_n(Q))` holds for infinitely many `n`. Given `n_0 >= 2`,
  pick such an `n >= n_0 + 2`; then `GL_(n_0)(Q) <= PSL_n(Q)`, so
  `P(GL_(n_0)(Q))`.
- (a) ⇒ (c): `SL_m(Q) <= GL_m(Q)`. (c) ⇒ (b): `SL_m(Q) = PSL_m(Q)` for odd `m`.

**Consequences.** The quotient remark: `N ∩ PSL_n(Q)` is normal in the simple
group `PSL_n(Q)`, so it is trivial when `N` does not contain `PSL_n(Q)`. The Zorn
remark: an increasing union of normal subgroups each meeting `PSL_n(Q)`
trivially meets it trivially, so a maximal `M` exists; if `1 != L/M` is normal in
`Γ/M` then `L` meets `PSL_n(Q)` nontrivially by maximality, hence contains it.
