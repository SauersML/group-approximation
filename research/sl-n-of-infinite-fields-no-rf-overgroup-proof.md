---
rg: 2
id: sl-n-of-infinite-fields-no-rf-overgroup-proof
kind: route
title: Simplicity and perfectness of SL_n over an infinite field kill every finite quotient, hence every residually finite overgroup
target: sl-n-of-infinite-fields-lie-in-no-residually-finite-group
requires: []
---

**Classical inputs** (Jordan, Dickson; see for example Lang, *Algebra*, GTM
211, Chapter XIII, sections 8 and 9; cited without re-reading at the source).
For a field `K` and `n >= 2` with `(n, |K|)` not `(2,2)` or `(2,3)`, in
particular for every infinite `K`:
- (a) `SL_n(K)` is perfect;
- (b) `PSL_n(K) = SL_n(K)/Z` is simple, where `Z` is the centre, the scalar
  matrices `lambda I` with `lambda^n = 1`.

Since the polynomial `x^n - 1` has at most `n` roots, `Z` is finite.

**Normal subgroups.** Let `N` be normal in `S = SL_n(K)`. Its image in
`PSL_n(K)` is normal, so by (b) it is trivial or everything.
- If it is trivial, `N <= Z`, so `N` is finite.
- Otherwise `NZ = S`. Since `Z` is central, `[NZ, NZ] = [N, N] <= N`, and by (a)
  `S = [S, S] = [NZ, NZ] <= N`. So `N = S`.

**Clause 1.** Let `S -> F` be a surjection onto a finite group with kernel `N`.
If `N <= Z` then `F = S/N` is infinite, because `S` is infinite (it contains the
elementary matrices `I + a e_12`, `a in K`) and `N` is finite. This is
impossible, so `N = S` and `F` is trivial.

**Clause 2.** Let `G >= S` be residually finite and `1 != g in S`. Some finite
quotient `q: G -> F` has `q(g) != 1`. But `q` restricted to `S` has finite image,
which is a finite quotient of `S`, so it is trivial by clause 1. Then `q(g) = 1`,
a contradiction. Since `SL_n(K) <= GL_n(K)`, no group containing `GL_n(K)` is
residually finite.

**The listed consequences.**
- Finitely generated linear groups are residually finite (Mal'cev).
- A group acting faithfully on a locally finite rooted tree is residually
  finite, since the level stabilizers have finite index and intersect trivially.
- A profinite group is residually finite as an abstract group, since its open
  normal subgroups intersect trivially.
`∎`
