---
rg: 2
id: sl-odd-q-in-fp-simple-iff-fp-overgroup-maps-nontrivially
kind: claim
title: For odd m, SL_m(Q) embeds in a finitely presented simple group iff some finitely presented overgroup maps to one without killing a single fixed element
distinct_from:
  local-boone-higman-iff-boone-higman: that is the class-level host principle for finitely generated decidable inputs; this is the per-input one-inequation criterion for the non-finitely-generated simple input SL_m(Q) and an arbitrary finitely presented overgroup.
  boone-higman-iff-isolated-hosts-and-local-boone-higman: that uses an isolated overgroup and a finite discriminating set; this needs no isolation, since the simplicity of SL_m(Q) makes one element discriminating for it.
  simple-group-in-fp-simple-iff-fp-just-infinite-host: that relaxes the host to a just-infinite one; this keeps a simple target but relaxes the embedding of the countable group to one homomorphism of a finitely presented group.
---

**ESTABLISHED** by `sl-odd-q-in-fp-simple-iff-fp-overgroup-maps-nontrivially-proof`
(elementary; not independently reviewed; no novelty claimed).

## Statement

Let `m >= 3` be odd and fix `s in SL_m(Q)`, `s ≠ 1`.

1. **One element discriminates.** Let `P` be any group containing `SL_m(Q)`. Then
   every homomorphism `φ : P -> K` with `φ(s) ≠ 1` is injective on `SL_m(Q)`.
2. **Criterion.** `SL_m(Q)` embeds in a finitely presented simple group iff there
   are a finitely presented `P ⊇ SL_m(Q)`, a finitely presented simple `K` and a
   homomorphism `P -> K` not killing `s`. For a finite presentation
   `P = <x | r(x)>` and a word `w_s(x)` for `s`, this says that the existential
   sentence `Σ_(P,s) = ∃x (r(x) = 1 ∧ w_s(x) ≠ 1)` holds in `K`.
3. **Any fixed overgroup suffices one way.** For a *fixed* finitely presented
   `P ⊇ SL_m(Q)`, `Σ_(P,s)` in one finitely presented simple group `K` embeds
   `SL_m(Q)` in `K`, and so `GL_n(Q)` for every `n < m`
   (`sl-odd-q-simple-inputs-for-gl-n-q-root`).
4. **Decidable overgroups exist.** Survey arXiv:2306.16356v3, Proposition 3.3(2),
   gives a finitely presented `P_m ⊇ GL_m(Q) ⊇ SL_m(Q)` with solvable word problem.
   By `fg-groups-have-simple-kazhdan-hosts-of-same-wp-degree`, `P_m` lies in an
   infinite finitely generated simple group `H_m` with property (T) and solvable
   word problem. So the root for `GL_n(Q)`, `n < m`, follows from any of these,
   each weaker than the one before:
   - the full Boone–Higman conjecture;
   - Boone–Higman for the single finitely generated group `H_m`;
   - Boone–Higman for the single finitely presented group `P_m`;
   - the single sentence `Σ_(P_m,s)` in some finitely presented simple group.
5. **Counterexample certificate.** If `GL_n(Q)` embeds in no finitely presented
   simple group, then for every odd `m >= n + 1`, every finitely presented
   `P ⊇ SL_m(Q)` and every `s ≠ 1`, the universal sentence
   `∀x (r(x) = 1 → w_s(x) = 1)` holds in *every* finitely presented simple group.

## Why it matters for the swarm

Any finitely presented overgroup of `SL_m(Q)` built for Problem 2.7 turns the
root into one homomorphism problem: map that overgroup to a finitely presented
simple group without killing `s`. This applies to a natural overgroup, and to
Mikaelian's announced explicit one (arXiv:2507.04347, §1.4). In particular, if
such an overgroup satisfies Boone–Higman, or is itself simple, the root follows
for all `n < m`. For the non-finitely-generated input, embedding is thereby
reduced to a finite, first-order condition about one finitely presented group.
