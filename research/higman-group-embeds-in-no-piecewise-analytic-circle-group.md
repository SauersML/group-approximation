---
rg: 2
id: higman-group-embeds-in-no-piecewise-analytic-circle-group
kind: claim
title: Higman's four-generator group has only the trivial homomorphism to any group of piecewise real-analytic circle homeomorphisms
distinct_from:
  higman-group-embeds-in-no-graph-almost-automorphism-group: that excludes zero-dimensional almost-automorphism hosts; this excludes piecewise real-analytic circle homeomorphism groups, including Thompson's T in its projective model and Lodha's finitely presented simple group S.
---

**ESTABLISHED** (elementary; no novelty claimed beyond the scope below).

**Statement.** Let
`H4 = < g_0, g_1, g_2, g_3 | g_i g_(i+1) g_i^-1 = g_(i+1)^2, i ∈ Z/4 >`, and let
`PA(S^1)` be as in `piecewise-analytic-circle-square-conjugate-has-parabolic-ends`.
Every homomorphism `H4 → PA(S^1)` is trivial.

So `H4` embeds in no group of PL circle homeomorphisms with finitely many
breakpoints, and in no group of piecewise-`PSL_2(R)` homeomorphisms of `RP^1`
with finitely many breakpoints. That includes Thompson's `T` and Lodha's
finitely presented infinite simple group `S` (arXiv:1710.06220v2, Theorem 1.1).

**Literature.** Rivas--Triestino, arXiv:1905.00938v2 (Discrete Analysis
2019:20), read from the PDF text:
- "Theorem A. Higman's group H is left-orderable and hence it admits a faithful
  action on the real line by" homeomorphisms.
- "Theorem C. Every representation ρ : H → Diff^1(R) is trivial. The same holds
  for every representation ρ : H → Diff^1(S^1)."

Elements of `PA(S^1)` need not be `C^1`: they may have breakpoints. So Theorem C
does not apply, and this claim is a piecewise-analytic counterpart. Theorem A
shows that some regularity hypothesis is needed. No search was made for earlier
statements about PL or piecewise projective actions of `H4`.

The proof is `higman-group-piecewise-analytic-circle-obstruction-proof`.
