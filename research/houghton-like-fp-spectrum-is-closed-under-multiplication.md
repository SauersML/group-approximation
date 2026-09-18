---
rg: 2
id: houghton-like-fp-spectrum-is-closed-under-multiplication
kind: claim
title: For every infinite shift-similar G the set of n with H_n(G) finitely presented is closed under multiplication by positive integers, and it is all n >= 1 when G is finitely presented and strongly shift-similar
distinct_from:
  fp-strongly-shift-similar-groups-have-fp-houghton-like-groups: that is the case where G itself is finitely presented; this applies it to the strongly shift-similar groups H_n(G) and turns it into a statement about the whole set of admissible n.
  houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group: that is the germ-level gate for each n; this is the finite-presentation spectrum itself.
  decidable-inputs-have-fp-houghton-like-shift-envelopes: that asks for one admissible n per input; this shows that one admissible n gives all its multiples.
---

**ESTABLISHED** (lane proof, written inline, elementary given the cited nodes and Mallery--Zaremsky
Proposition `prop:HnG_shift_sim` read at source; not independently reviewed; no priority claimed).

**Statement.** For an infinite shift-similar `G <= Sym(N)` put `F(G) = { n >= 1 : H_n(G) is finitely presented }`.
1. If `n ∈ F(G)` and `m >= 1`, then `mn ∈ F(G)`.
2. If `G` is strongly shift-similar and finitely presented, then `F(G) = {1, 2, 3, ...}`.
3. `F(G) = F(H_1(G))`.

**Proof.**
- Mallery--Zaremsky (arXiv:2202.00822, Proposition `prop:HnG_shift_sim`, read in the source TeX) state two things.
  For every `n`, the group `H_n(G)` has a strongly shift-similar representation `G_n <= Sym(N)`, namely
  `ω^-1(H_n(G))` for the bijection `ξ(k,i) = k + (i-1)n`. They also give an isomorphism `H_m(G_n) ≅ H_(mn)(G)`
  for every `m`. `G_n` is infinite, since it contains `FSym(N)`.
- (1) Suppose `H_n(G)` is finitely presented. Then `G_n` is a finitely presented strongly shift-similar group. So
  `H_m(G_n)` is finitely presented for every `m >= 1` by
  `fp-strongly-shift-similar-groups-have-fp-houghton-like-groups`, and `H_m(G_n) ≅ H_(mn)(G)`.
- (2) For strongly shift-similar `G`, `H_1(G) = G` (Proposition `prop:H1_equal`). So `1 ∈ F(G)`, and (1) applies.
- (3) This is the case `n = 1` of the isomorphism: `H_m(H_1(G)) ≅ H_m(G)`. ∎

**Calibrations.** All three are read off the isomorphism above and Brown's theorem, which is recalled here, not
re-read: `H_k` is finitely presented iff `k >= 3`.
- `G = FSym(N)`. The proof of Observation `obs:finite_boring` uses only `G <= FSym(N)`, so it gives
  `H_n(FSym(N)) = H_n`. Hence `F = {n >= 3}`.
- `G = H_k` (Houghton). `H_n(H_k) ≅ H_(nk)`, so `F(H_k) = {n : nk >= 3}`: `{n >= 2}` for `k = 2`, and every `n`
  for `k >= 3`.
- `G = E_k`. `H_n(E_k)` contains `H_n(H_k)` with finite index (the source remark after Question 5.13). So
  `F(E_k) = F(H_k)`; in particular `F(E_2) = {n >= 2}`.

So spectra `{n >= 3}`, `{n >= 2}` and "everything" all occur. It is not known whether `F(G)` is always of the
form `{n >= n_0}`. The first unknown step is whether `n ∈ F(G)` implies `n+1 ∈ F(G)`.

**Reading for the Houghton-like route.** This concerns `boone-higman-via-houghton-like-shift-envelopes` and
`decidable-inputs-have-fp-houghton-like-shift-envelopes`.
- One admissible `n` for an enumeration `nu` gives all its multiples.
- If `E_nu(P)` itself is finitely presented, then every `n` is admissible; `E_nu(P)` is strongly shift-similar by
  `half-finite-generators-with-e2-are-strongly-shift-similar`.
- So passing to `n >= 2` can only help through enumerations with `E_nu(P)` not finitely presented. The help is of
  Houghton type, as in `F(E_2) = {n >= 2}`.
- At the germ level, the gain is dropping the two-sided window
  (`houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group`). At the finitary level, the
  free-shift enumerations show that no gain occurs (`free-shift-houghton-like-envelopes-are-not-fp`).
