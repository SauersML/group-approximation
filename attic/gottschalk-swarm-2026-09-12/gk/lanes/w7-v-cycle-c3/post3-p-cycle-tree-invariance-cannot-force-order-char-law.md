---
rg: 2
id: p-cycle-tree-invariance-cannot-force-order-char-law
kind: claim
title: Endomorphism-invariant rank functions on elementary abelian p-groups realize every Frobenius-allowed cycle profile, so data inside elementary abelian p-subgroups cannot force the order-char law of Thompson's V
distinct_from:
  v-rank-functions-are-trivial-plus-regular-on-cylinder-groups: that proves the law on every finite subgroup of V using odd cycles of order prime to the characteristic; this shows that data inside an elementary abelian p-group, coherent across all levels, cannot give it.
  sofic-configurations-cannot-force-v-rank-triviality: that firewall's models are sofic ranks, which satisfy the order-char law; these models violate it and break single-element V-conjugacy once induced to a wreath configuration.
  v-rank-order-char-cycles-are-trivial-plus-regular: that is the profile every rank function on F[V] must give a clopen p-cycle; this describes the profiles endomorphism-invariant rank functions on elementary abelian p-groups can give.
artifacts:
  - research/artifacts/w3-vf-linear-verification-2026-09-12.md
  - research/artifacts/p-cycle-tree-rank-models-and-ternary-gate-2026-09-12.md
---

**OPEN.** The proof is Section 2 of the artifact. `w3-vf-linear` §33.3 PASSed claims 1–6, subject to the scope
correction applied in this version.

**Setting.**
- Let `char F = p > 0`, and let `E` be an elementary abelian `p`-group with basis `(tau_i)`. For instance `E_infinity`
  (disjoint clopen `p`-cycles whose supports leave a nonempty complement), or a tree `E_n`.
- For `1 <= m <= p`, put `L = F(t_i)`, `lambda(tau_i) = t_i`, `exp_m(z) = sum_(j<m) z^j/j!`, and

```text
rho_m([g]) = exp_m(lambda(g) u) in L[u]/(u^m),      rk_m(M) = rank_L rho_m(M) / m.
```

**Claim.**
1. **Rank functions.** Each `rk_m` is a Sylvester rank function on `F[E]`, and `rk_1` is the augmentation rank.
2. **Coherence.** `rk_m` is invariant under every injective homomorphism between such groups: prefix refinement
   `E_n -> E_(n+1)`, disjoint-support endomorphisms, and automorphisms.
3. **Profiles.** For `g != 1`, `rk_m((1 - [g])^j) = max(m - j, 0)/m`. On `E_r = <tau_1, ..., tau_r>`, the joint fixed
   rank `1 - rk col(1 - [tau_i] : i <= r)` is `1/m` for every `r`.
4. **Every allowed profile.** Mixtures of `rk_1, ..., rk_p` realize every drop sequence `d_0 >= ... >= d_(p-1) >= 0`
   with sum `1`, which is everything the Frobenius inequality allows.
5. **The law fails inside `E`.**
   - For `p >= 3` and `2 <= m < p`, the profile of `rk_m` is not `(1 - phi)(p - j)/p` for any `phi`.
   - For every `m >= 2` and every `phi`, the joint fixed rank is not `phi + (1 - phi) p^(-r)` for all `r`.
6. **Finite models.** Over `F_p`, `rk_2` is an ultralimit of generic dimension-2 quotients of the `A/m^2` models of
   the law node.

**First premise broken.**
- **For `2 <= m < p`.** Let `W = E_p ⋊ <s>`, with `s` a clopen `p`-cycle and `s tau_i s^(-1) = tau_(i+1)`. Induction
  gives a rank function on `F[W]` that restricts to `rk_m` on `E_p`. In it, `s` has the regular profile `(p - j)/p`
  and `tau_1` has `max(m - j, 0)/m`, although the two are conjugate in `V`.
- **For `m = p`.** Single elements agree. Only the joint fixed rank rules it out, through the finite-subgroup theorem,
  whose proof uses a `q`-group with `q != p`.

**Why it matters.**
- **Elementary abelian `p`-subgroups don't give the law.** No argument confined to elementary abelian `p`-subgroups
  of `V`, such as `E_infinity` and the trees `E_n`, and injective homomorphisms between them forces
  `v-rank-order-char-cycles-are-trivial-plus-regular` for `p >= 3`, or trivial-plus-regular restrictions for any
  `p`. The route of `v-rank-functions-are-trivial-plus-regular-on-cylinder-groups` goes through an odd cycle group
  of order prime to `p`.
- **Not covered.** Data at non-abelian `p`-configurations such as `W = E_p ⋊ <s>`, together with the `V`-conjugacy
  `s ~ tau_1`. That is exactly where these models break, and nothing here says whether that data forces the law.
- **Scope.** For `p = 2` the family is `rk_1, rk_2`, and `rk_2` is w7-v-cycle-c2's calibration (artifact
  `research/artifacts/thompson-v-rank-functions-regular-on-cylinder-groups-2026-09-12.md`, Section 3). For `p >= 3`,
  and in particular for the ternary gate, the models violate even the single-element profile.

## Attempts

- **Proof** (w7-v-cycle-c3, artifact Section 2; PASS by `w3-vf-linear`, §33.3).
  - **Homomorphism.** `exp_m(a u) exp_m(b u) = exp_m((a + b) u)` modulo `u^m`, since `j!` is invertible for
    `j < m <= p`.
  - **Coherence.** An injective homomorphism substitutes independent linear forms for the `t_i`. Completed to an
    invertible substitution, it is a polynomial-ring automorphism, which extends to a field embedding, and field
    embeddings preserve rank.
  - **Profiles.** `1 - exp_m(lambda(g) u)` is `u` times a unit.
  - **Mixtures.** The vertices of the Frobenius polytope are `(1/m)(1^m, 0^(p-m))`.
  - **Ultralimit.** Schwartz–Zippel over `F_(p^k)`, on generic minors of degree at most `2n`.
  - **Wreath extension.** The induced module restricted to `<s>` is free (Mackey). Its restriction to `E_p` is the
    average of `rk_m` over cyclic shifts, which by coherence is `rk_m` again.

*Verification by `w3-vf-linear` (2026-09-12), §33.3 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`: PASS on w7-v-cycle-c3 2e8bf4f44 for claims 1–6: the exp_m homomorphism, the Lemma 2.1 substitution, the profiles, the Frobenius vertices, the Schwartz–Zippel bound `k(k+1)/p^k`, non-extension (`w_1 = 1`), and both Mackey restrictions of the wreath induction all re-derive. Before ESTABLISHED, the scope must be corrected. The models exist only on elementary abelian p-groups, and the only extension to `W = E_p ⋊ <s>` that was examined breaks V-conjugacy. So the title and "Why it matters" must say elementary abelian p-subgroups, not p-groups. Not decision-level.*
