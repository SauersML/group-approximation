---
rg: 2
id: sl-odd-q-in-fp-simple-iff-fp-overgroup-maps-nontrivially-proof
kind: route
title: The kernel meets the simple subgroup in a proper normal subgroup; a finitely presented simple host is its own overgroup
target: sl-odd-q-in-fp-simple-iff-fp-overgroup-maps-nontrivially
requires: [sl-odd-q-simple-inputs-for-gl-n-q-root, fg-groups-have-simple-kazhdan-hosts-of-same-wp-degree]
---

**Clause 1.** `ker(φ) ∩ SL_m(Q)` is normal in `SL_m(Q)`, and it does not contain
`s`. `SL_m(Q)` is simple (`sl-odd-q-simple-inputs-for-gl-n-q-root`, clause 1), so
the intersection is trivial.

**Clause 2.**
- (⇐) By clause 1 the homomorphism is injective on `SL_m(Q)`, so `SL_m(Q)`
  embeds in `K`.
- (⇒) If `ι : SL_m(Q) -> K` embeds `SL_m(Q)` in a finitely presented simple `K`,
  take `P = K`, identify `SL_m(Q)` with `ι(SL_m(Q))`, and take the identity map
  `K -> K`. It does not kill `s`.
- A homomorphism from `<x | r(x)>` to `K` is the same as a tuple `k` in `K` with
  `r(k) = 1`, and it does not kill `s` iff `w_s(k) ≠ 1`. This is the sentence
  `Σ_(P,s)`.

**Clause 3.** This is the (⇐) half of clause 2 for the given `P`, together with
clause 2 of `sl-odd-q-simple-inputs-for-gl-n-q-root`.

**Clause 4.**
- **Overgroup.** The survey's Proposition 3.3 states: "Every countable group
  with a solvable word problem embeds into a finitely presented group with
  solvable word problem. Furthermore, the following groups can be embedded into
  finitely presented groups with solvable word problem: ... (2) The group
  GL_n(Q) for all n ≥ 2." Its proof goes through Higman–Neumann–Neumann and
  Clapham.
- **Kazhdan host.** `P_m` is finitely generated, so
  `fg-groups-have-simple-kazhdan-hosts-of-same-wp-degree` applies. Its clause 1
  gives an infinite finitely generated simple Kazhdan `H_m` containing `P_m`,
  and its clause 3 says `WP(H_m) ≤_T WP(P_m)`, so `H_m` is decidable.
- **The chain.** Boone–Higman gives an embedding of `H_m`. An embedding of `H_m`
  restricts to one of `P_m`. An embedding of `P_m` in a finitely presented
  simple `K` gives `Σ_(P_m,s)` in `K`. That gives the root by clause 3.

**Clause 5.** This is the contrapositive of clause 3, for every admissible
`(m, P, s)`. ∎
