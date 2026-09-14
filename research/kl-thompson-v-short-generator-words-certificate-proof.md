---
rg: 2
id: kl-thompson-v-short-generator-words-certificate-proof
kind: route
title: Certify the length-six and length-seven generator words over V by localization, curvature, powers and retractions
target: kl-thompson-v-short-generator-words-certified-injective
requires:
  - kl-failure-localizes-to-the-coefficient-subgroup
  - kervaire-laudenbach-holds-for-hyperlinear
  - kl-four-same-sign-corner-words-inject
  - kl-length-at-most-five-equations-are-solvable
artifacts:
  - research/artifacts/kl-thompson-v-generator-census-2026-09-13.md
---

Notation as in the target. The scripts, their md5 sums and the MSI job ids are
in the artifact. Every group computation is exact tree-pair arithmetic in V
(`experiments/kl-thompson-v-census/vgroup.py`). Its generators satisfy the nine
Bleak--Quick relators exactly.

**Symmetries.** Rotation replaces `w` by a conjugate, and `w -> sigma(w^(-1))`
applies an automorphism of `V * <t>` fixing V. Neither changes whether
`V -> V_w` is injective, so a certificate for one representative covers its class.

**FINITE.** The coefficient support lies in `<a,b>`, `<a,c>` or `<b,c>`. Closure
in V gives these groups orders `24`, `6` and `60`. A finite group is hyperlinear,
so `kervaire-laudenbach-holds-for-hyperlinear` makes its coefficient map
injective. By `kl-failure-localizes-to-the-coefficient-subgroup`, a failure over V
would already be a failure over the coefficient subgroup.

**R4.** Item 1 of `kl-four-same-sign-corner-words-inject` applies: at least four
light corners. A word with `n = 7` and `0 < m < 7` is never a proper power.
- For `n = 6`, a proper power `u^k` has `u` of variable length at most three and
  nonzero degree, so it is covered by POWER below whatever its corner count.
- Heavy and light are computed from exact label equality in V. The symbols `a`, `b`,
  `B`, `c` are four distinct nontrivial elements, and only `a`, `c` are
  involutions.

**POWER.** Write `w = u^k` with `k >= 2`. Then `u` has variable length at most
three and degree `deg(w)/k != 0`.
- `V -> V_u` is injective by `kl-length-at-most-five-equations-are-solvable`.
- `V_u` is a quotient of `V_w`, since `<<w>> <= <<u>>`, and the composite
  `V -> V_w -> V_u` is injective.
- So `V -> V_w` is injective.

**CORNER3.** Item 2 of `kl-four-same-sign-corner-words-inject`, whose hypotheses
are: `r = 3`, not a proper power, (D4) and (A2). The check is stricter than the
theorem requires.
- (D4): every reduced closed path of length four in `Theta`, at either vertex and
  through light edges, is tested. Its label is required to be nontrivial in both
  product orders of its edge labels.
- (A2): every loop label and its inverse is compared with both product orders of
  every reduced light closed path of length two at the loop's vertex, and with
  their inverses.
- The route `kl-four-same-sign-corner-words-weight-proof` uses (D4) only on
  all-light cyclically reduced 4-cycles. It uses (A2) only through the set of light
  length-two labels at a vertex, which is closed under inversion.

**RETRACT.** Let `P_k` be a complete prefix code with `k <= 4` elements, and
`delta(g)(p s) = p g(s)` for `p in P_k`. Then `delta : V -> V` is an injective
homomorphism.
- The search finds `t_0 in V` with `g_0^delta t_0^(e_0) ... g_(n-1)^delta t_0^(e_(n-1)) = 1`,
  checked by exact multiplication. The homomorphism `V * <t> -> V`, `g -> delta(g)`,
  `t -> t_0` kills `w`.
- Its restriction to V is `delta`, which is injective. The restriction factors
  through `V -> V_w`, so that map is injective.
- The candidates `t_0` form a ball of radius six in the generators, multiplied by
  every permutation of `P_k`. A pruning test on three random points only discards
  candidates, and every certificate is re-verified by
  `experiments/kl-thompson-v-census/verify_retract.py`.

**Trust surface.**
- The four required claims.
- Correct execution of the census and certification scripts, reproducible from the
  artifact.
- Completeness of the Bleak--Quick presentation of V is not used by any
  certificate. It enters only the collapse test, which certifies nothing here.
