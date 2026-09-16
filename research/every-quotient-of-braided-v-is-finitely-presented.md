---
rg: 2
id: every-quotient-of-braided-v-is-finitely-presented
kind: claim
title: Every quotient of the braided Thompson group bV is finitely presented (bV satisfies max-n)
refuted_by:
  - some-quotient-of-braided-v-is-not-finitely-presented
---

For every normal subgroup `N` of `bV = V_br`, the quotient `bV/N` is finitely
presented. Since `bV` is finitely presented, this is equivalent to max-n: every
normal subgroup is the normal closure of finitely many elements, or equivalently
every ascending chain of normal subgroups stabilizes.

By Corollary 2.8 of arXiv:1403.8132, only normal subgroups inside the pure
braided kernel `P_br` matter.

## Attempts

- 2026-09-13 (z2-10-bv-hopfian): bounded depth works. For each `c`, ascending chains
  of normal subgroups containing `gamma_c(P_br)` stabilize.
  - The graded pieces are noetherian `FS^op`-representations; see
    `research/artifacts/zp-braided-v-hopfian-2026-09-13.md` §6.
  - So "every quotient by a normal subgroup containing `gamma_c(P_br)` is finitely
    presented" is equivalent to "`bV/gamma_c(P_br)` is finitely presented".
  - Where it dies: a chain whose members differ only at unbounded depth `c` escapes
    the graded argument.
  - First concrete test: is `bV/[P_br, P_br]` finitely presented? It is an extension
    of `V` by `C_c(Y, Z)` (see `braided-thompson-group-bv-is-perfect`).
- The m-loose subgroups `K(Lambda_*(m))` of arXiv:1403.8132 §4 form a descending
  chain, so they say nothing about ACC.
