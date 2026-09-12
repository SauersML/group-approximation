---
rg: 2
id: kun-thom-lamp-quotients-have-lamp-sofic-radical
kind: claim
title: Quotients of the Kun--Thom coset wreath by lamp submodules of its sofic radical keep the remaining lamps as sofic radical
distinct_from:
  kun-thom-wreath-sofic-radical-is-fibre-parity-kernel: that computes the sofic radical of the coset wreath itself; this passes it to every quotient by a submodule of that radical and so produces nonsofic abelian-by-residually-finite groups without lamp sites.
  kt-intermediate-coset-wreaths-are-nonsofic: that proves nonsoficity for the quotients by permutation kernels, the coset wreaths over intermediate subgroups; this covers every lamp submodule of the radical, including the non-permutation ones.
artifacts:
  - research/artifacts/kun-thom-lamp-quotient-hosts-2026-09-12.md
---

**ESTABLISHED** by `kun-thom-lamp-quotients-sofic-radical-proof`.

Let `W = P x| G` be the Kun--Thom coset wreath, with `P = F_2[G/Gamma]` and `K_even <= P` the
fibre-even configurations over `G/N`, `N = EL_r(R)`. For every `G`-submodule `U <= K_even`, put
`H_U = W/U = (P/U) x| G`. Then

    Rad_sof(H_U) = K_even / U,

so `H_U` is nonsofic exactly when `U != K_even`. The quotient `H_U / Rad_sof(H_U)` is the
residually finite group `W_N`.

These groups are split extensions of the residually finite linear group `G` by an elementary
abelian 2-group that is not finitely generated. So neither (O7) nor the lamp-site theorems of
the permanence closure apply to them directly. Section 2 of the artifact.
