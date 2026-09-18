---
rg: 2
id: loop-braid-pair-twist-push-mutual-link-proof
kind: route
title: "Check the commutation on the three generator families of the triple-cable subgroup, then read off the mutual link through the Link Lemma; exclude types by a clasp homomorphism"
target: loop-braid-pair-twist-push-mutual-link
requires:
  - pure-loop-braid-group-is-colimit-of-cabling-stabilizers
artifacts:
  - research/artifacts/zp-loop-braid-bfmwz-push-decomposition-2026-09-17.md
  - research/artifacts/zp-loop-braid-forbidden-ring-push-reduction-2026-09-17.md
  - experiments/loop-braid-bfmwz-push-2026-09-17/mutual_link.py
---

The complete hand proof is artifact §§1–2 (Lemma 2.1, Lemma 2.1′, Prop. 2.2, Lemma 2.3).
Unreviewed. The inputs are:
- the cabling-subgroup description and strict fundamental domain, from
  `pure-loop-braid-group-is-colimit-of-cabling-stabilizers`;
- the Link Lemma `lk_{X_n(F)}(σ) = P_σ · lk_Q(σ) ≅ X_{n−m}(F' ∪ Fus_σ)`, proved in the w8 artifact
  (`zp-loop-braid-forbidden-ring-push-reduction-2026-09-17.md`, Lemma 2.1) from the same inputs.

1. **Commutation (Lemma 2.1).** Take `g = τ_br`, `P = x_a x_b x_r`. g fixes `x_a` and the word
   `x_b x_r`, so `g(P) = P`. Check each generator family of `T(a,b,r)`:
   - `A_ij`, `i, j ∉ {a,b,r}`: disjoint supports.
   - `x_k ↦ P x_k P^{-1}`: both composites send `x_k ↦ g(P) x_k g(P)^{-1} = P x_k P^{-1}`.
   - `x_s ↦ x_q x_s x_q^{-1}` (`s = a, b, r`): the conjugation by `x_q` commutes with the
     conjugation of `x_b, x_r` by `x_b x_r`.

   The order `(r, a, b)` with `τ_ra` is symmetric.
2. **The push moves u_0 (Lemma 2.1′).** Elements of `P_u` conjugate `x_a` and `x_b` by one common
   element U. For `τ_br` the cosets `⟨x_a⟩` and `x_b x_r ⟨x_b⟩` forced on U are disjoint.
3. **Containment (Prop. 2.2).** For `p ∈ T ⊆ P_u` and `σ ∈ Q_abr`: `pσ ∈ lk(u_0)`. Also
   `g ∈ P_σ`, so `g^{-1} p σ = p g^{-1} σ = pσ`, hence `pσ ∈ lk(g u_0)`. Through the Link Lemma,
   `L` corresponds to `lk_{X_{n−1}(F')}(e)` for the level-`(n−1)` vertex `e = (f, r)` or `(r, f)`,
   which is `≅ X_{n−2}(F'' ∪ {t})`.
4. **Type exclusion (Lemma 2.3).** If a common neighbour had type `z ∋ r`, then
   `s^{-1} g s' ∈ P_z` for some `s, s' ∈ P_u`. But `χ_{u,z} = e_ca − e_da − e_cb + e_db`
   vanishes on `P_u` and `P_z` and takes the value ±1 on g.

The script `mutual_link.py` (n = 5, 6, 7, all ordered triples in {1..4}) confirms items 1, 2 and 4
and the failure of the one-ring pushes. It uses a necessary condition for membership in `P_u`, so it
certifies non-membership only; the positive statements are proved by hand.
