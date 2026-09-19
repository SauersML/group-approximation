---
rg: 2
id: fpbs-letter-contact-words-have-relative-cayley-cost-one-proof
kind: route
title: Pick a small section of the contact subgroup, cross one letter only there, and slide the other crossings through the contact
target: fpbs-letter-contact-words-have-relative-cayley-cost-one
requires:
  - fpbs-small-marker-induction-input
  - fpbs-amen2-betti-cost-input
  - one-relator-group-cost-equals-first-l2-betti-plus-one
artifacts:
  - research/artifacts/fpbs-relative-cayley-cost-letter-saturation-2026-09-18.md
  - experiments/fpbs-relative-cayley-cost-2026-09-17/witnesses.py
---

Written derivation. The details are in Sections 1–3 of the artifact.

1. **Lemma 1.** Let `I = H cap t^{-1} H t`, which is infinite. Its action is free, so `E_{a|I}` is aperiodic. By
   `fpbs-small-marker-induction-input` (Gaboriau lecture Exercise 1.17) it has a complete section `M` with
   `mu(M) < eps`. For `x`, pick `i in I` with `i x in M`. Then:
   - `x ~_H i x`;
   - `(i x, t i x)` is a kept edge;
   - `t i x = (t i t^{-1}) t x`, with `t i t^{-1} in H`.

   So `(x, t x)` lies in `<R_H cup Phi_t|_M>`.
2. **Theorem A.** A nontrivial subgroup of `F_2` is infinite. `Phi_s cup S_v` generates `R_{H_s}`, so
   `Phi_s cup Phi_t|_M` is admissible, of cost `< 1 + eps`. For the bound `RC >= 1`: `F cup S_v` graphs the orbit
   relation of a free `F_2`-action. Gaboriau's lecture notes, Corollary 2.25, verbatim: "The following groups are
   strongly treeable and have fixed price: C∗(Fn) = C∗(Fn) = n for the free group of rank n."
3. **Corollary A'.**
   - *Upper bound.* `Phi_{a_1} cup ... cup Phi_{a_n}` generates `R_A`, which contains `Phi_u = Phi_v`. Theorem A
     applies to the free action `a|_{F(c,d)}`. Together these generate `R_G`, at cost `n + 1 + eps`.
   - *Lower bound.* `C_sub^a(S) >= C(a) >= 1 + beta_1^(2)(G)`, by `fpbs-amen2-betti-cost-input` (Gaboriau lecture
     Theorem 2.64).
   - *Betti number.* `u v^{-1}` has cyclic syllable length 2 in `F_n * F(c,d)`, so it is not a proper power. `G` is
     infinite. So `one-relator-group-cost-equals-first-l2-betti-plus-one`, with `m = 1` and `|S| = n + 2`, gives
     `beta_1^(2)(G) = n`. Only the Betti value is used.
4. **Computations.** The census scripts in `experiments/fpbs-relative-cayley-cost-2026-09-17/` list the contact words.
   The proof does not depend on them. The examples used in the claim are checked by hand in Section 3 of the artifact,
   for instance `ddd in <c, ddd> cap d^{-1} <c, ddd> d`.
