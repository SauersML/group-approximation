---
rg: 2
id: leavitt-identity-factor-failures-transfer-into-kernel-corners
kind: claim
title: On every finite-field Leavitt host with q at least 3, failures of direct finiteness in the Leavitt-visible factor transfer into kernel corners
distinct_from:
  ternary-anti-central-failures-transfer-into-kernel-corners: that is the instance q = 3, d = 2 with the level-two Klein constants; this is every prime power q >= 3 and every arity d, with the exact least amplification level.
  leavitt-unit-group-algebras-split-over-scalar-characters: that splits the group algebra over scalar characters and identifies the Leavitt-visible factor; this embeds that factor into the corner of a kernel idempotent, so its invisible normal form is universal.
artifacts:
  - research/artifacts/ternary-anti-central-kernel-normal-forms-2026-09-12.md
---

Let `q = p^r >= 3`, `d >= 2`, `L = L_(F_q)(1,d)`, `G = L^x`, `A = F_q[G]`, `pi` the evaluation,
`A_iota` the Leavitt-visible factor and `K_iota = ker(pi|A_iota)`. Put
`delta_k(g) = sum_(|gamma|=k) S[gamma] g T[gamma]`. Let `H` be a group of level-`k` diagonal
constants `sum lambda(gamma) S[gamma]T[gamma]` meeting the scalars trivially, and `psi` a character
of `H` different from every coordinate character. Put
`E = (1/|H|) sum psi(h)^(-1)[h]` and `mu(x) = delta_k*(x) E`.

1. `mu` is an injective ring homomorphism with `pi mu = 0` and `mu(eps_chi) = eps_chi E != 0`.
2. Every pair `c a = eps_iota != a c` in `A_iota` gives the pair
   `(eps_iota - q) + mu(a)`, `(eps_iota - q) + mu(c)`, with `q = eps_iota E`. This is a strict pair
   over `eps_iota` with both factors in `eps_iota + K_iota`. So `A_iota` fails direct finiteness iff
   `F_q eps_iota + K_iota` does.
3. **Level criterion.** Such `(k, H, psi)` exist iff `q >= 3`. The least level is `1` iff `q >= 4`
   or (`q = 3` and `d >= 3`), and it is `2` for `(q,d) = (3,2)`.
4. **Base change.** For `F_q <= F_q'`, multiplying by the identity character idempotent of
   `F_q'[G_q']` carries pairs over `eps_iota` to pairs, and kernel pairs to kernel pairs.

**Consequence.** Extra roots of unity lower the amplification level; they add no room to the
kernel normal forms. On each host the invisible problem is exactly that host's direct-finiteness
question for `A_iota`, and the colimit over finite fields gains only host monotonicity.

Proof: Section 7 of the artifact.
