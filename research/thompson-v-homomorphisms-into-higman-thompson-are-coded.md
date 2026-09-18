---
rg: 2
id: thompson-v-homomorphisms-into-higman-thompson-are-coded
kind: claim
title: "Matte Bon: every non-trivial homomorphism from Thompson's V to a Higman-Thompson group V_{n,1} is given by an Omega_2-system, with an equivariant coding map to Cantor space"
distinct_from:
  nonamenable-rigid-stabilizers-give-cstar-simplicity: that is the Le Boudec--Matte Bon C*-simplicity criterion through rigid stabilizers; this is Matte Bon's classification of homomorphisms between full groups of one-sided shifts of finite type.
  cone-diagonal-roots-miss-a-kl-word-over-thompson-v: that handles only the explicit cone-diagonal endomorphisms of V; this imports the description of all homomorphisms V -> V_{n,1}.
artifacts:
  - research/artifacts/kl-thompson-v-internal-roots-2026-09-17.md
---

**ESTABLISHED (import)** through
`thompson-v-homomorphisms-into-higman-thompson-are-coded-citation`.

Let `n >= 2`. Let `X_n = {1..n}^N` be the one-sided full shift, and let
`V_{n,1}` be the group of homeomorphisms of `X_n` that are locally prefix
replacements. So `V = V_{2,1}`. For a finite word `w`, `C_w` is the cone of
sequences starting with `w`.

`V` is simple (Example 11.13: "since V is simple, we do not need to pass to
the derived subgroup"), so `D(G_{Omega_2}) = A(G_{Omega_2}) = V`.

Let `rho : V -> V_{n,1}` be a non-trivial homomorphism.

1. **Support.** Let `Z` be the support of `rho(V)`. Then `Z` is clopen, and
   `rho(g)` is the identity on `X_n \ Z` for every `g in V`.
2. **The system.** There are partial homeomorphisms `T_0`, `T_1` (an
   `Omega_2`-system with domain `Z`) with the following property. Put
   `T_w = T_{e_k} ... T_{e_1}` for a binary word `w = e_1 ... e_k`, and let
   `g` be represented by a finite table `{(v_i, w_i)}`, a prefix
   replacement between two complete prefix codes. Then
   `rho(g) = ⊔_i T_{v_i}^(-1) T_{w_i}`.
3. **The coding map.** There is a continuous map `q : Z -> X_2 = C` that
   intertwines the `rho`-action of `V` on `Z` with the natural action on `C`.
   For every binary word `w`, the domain of `T_w` is `s(T_w) = q^(-1)(C_w)`.

**Consequence used downstream.**
- Take a binary word `p` and a table of `g` that contains the pair `(p, p)`.
  Then `rho(g)` contains `T_p^(-1) T_p`, which is the identity on
  `s(T_p) = q^(-1)(C_p)`.
- So if `g` is the identity on the cone `C_p`, then `rho(g)` is the identity
  on `q^(-1)(C_p)`.

**Scope.**
- These are statements of N. Matte Bon, *Rigidity properties of full groups
  of pseudogroups over the Cantor set*, arXiv:1801.10133v2: Theorem 11.12,
  Example 11.13, Example 11.1, Definition 11.5, Proposition 11.6, Lemma 11.8
  and Theorem 11.11.
- The citation route quotes them verbatim. The proofs were not re-checked.
- Item 1 is Theorem 11.11, and items 2 and 3 are Theorem 11.12 with
  Lemma 11.8. The "consequence" is two lines from those statements, using
  only that `F^(-1) F` is the identity on the domain of a partial
  homeomorphism `F`.
