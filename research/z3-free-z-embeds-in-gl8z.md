---
rg: 2
id: z3-free-z-embeds-in-gl8z
kind: claim
title: The right-angled Artin group Z^k * Z embeds in GL_(2k+2)(Z); in particular Z^3 * Z embeds in GL_8(Z)
---

**ESTABLISHED** by `z3-free-z-embeds-in-gl8z-proof` (unreviewed).

For every `k >= 1`, the free product `Z^k * Z`, which is the right-angled Artin
group of a `k`-clique plus an isolated vertex, is isomorphic to a subgroup of
`GL_(2k+2)(Z)`. For `k = 3` this gives `Z^3 * Z <= GL_8(Z)`.

**Why it is recorded.** Belk–Bleak–Matucci (arXiv:1602.08635v1, Conjecture 1.7)
conjecture: "A right-angled Artin group A_Γ embeds into nV if and only if A_Γ
does not contain Z^(n+1) * Z." For `n = 2` that predicts `Z^3 * Z` is not in
`2V`. With this claim, the prediction would give the answer no to Zaremsky
2.19(d) through `some-gl-n-z-not-in-2v-via-z3-free-z`, with witness `GL_8(Z)`.
In the same paper (Remark 1.8(3)) they recall that Hsu and Wise embed every
right-angled Artin group in some `SL_n(Z)`. The proof here is a direct version
for this family.
