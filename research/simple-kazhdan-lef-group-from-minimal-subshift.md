---
rg: 2
id: simple-kazhdan-lef-group-from-minimal-subshift
kind: claim
title: EL_3 over a minimal subshift algebra modulo its centre is an infinite simple Kazhdan LEF group
distinct_from:
  infinite-simple-kazhdan-hyperlinear-group: that is Pestov's existential question; this is one explicit group, which answers it in the stronger sofic form.
  binary-leavitt-elementary-group-is-simple: that group lives over a purely infinite ring and is nonsofic; this one lives over a stably finite ring that embeds in ultraproducts of matrix algebras, and is LEF.
  simple-kazhdan-kac-moody-lattices-exist: those groups are finitely presented and therefore never LEF; this group is infinitely presented and LEF.
invalidates:
  - simple-kazhdan-full-mf-radical-proof
  - fp-simple-full-mf-radical-via-titz-witzel
  - titz-witzel-exact-kazhdan-mf-radical-over-z-proof
  - titz-witzel-mapping-tori-are-virtually-products-proof
artifacts:
  - research/artifacts/simple-kazhdan-lef-subshift-elementary-group-2026-09-12.md
  - research/artifacts/simple-kazhdan-lef-consequences-and-sources-2026-09-12.md
  - research/artifacts/ex-review-groups-2026-09-12-part1.md
---

Let `q` be a prime power, `X` an infinite minimal subshift (for example Fibonacci), and
`R = LC(X,F_q) ⋊ Z`. Put `G = EL_3(R)` and `S = G / Z(G)`. Then `S` is a finitely generated group
which is:

1. infinite and simple;
2. Kazhdan;
3. LEF, hence sofic, hence hyperlinear.

It answers Pestov's Open Question 9.1 (arXiv:0804.3968, p. 21) positively in both the hyperlinear
and the sofic form. It also answers Ozawa's remark in *About the QWEP conjecture*
(arXiv:math/0306067), the origin of 9.1: "It is unknown whether there exists a simple property (T)
group Γ which is hyperlinear". `S` is also the marked limit of the finite simple groups
`PSL_(3N_k)(F_q)` (`finite-simple-groups-converge-to-simple-kazhdan-group`). It is operator MF and,
by Ozawa--Thom, not weakly quasidiagonal.

**Status.**
- Proof: route `simple-kazhdan-lef-group-from-minimal-subshift-proof`, with the full derivation in
  the Part 1 artifact.
- Independent review PASS by `ex-verify-groups` (`research/artifacts/ex-review-groups-2026-09-12-part1.md`,
  commit 0efeac410). Its wording notes are applied.
- Novelty: bounded checks by this lane and by `ex-novelty` found no earlier infinite simple
  Kazhdan group that is LEF, sofic or hyperlinear.

## Credits

- **Property (T):** Ershov--Jaikin-Zapirain, arXiv:0809.4095, Theorem 1.1.
- **Simplicity of the ring:** the minimal-effective case of the simplicity criterion for Steinberg
  algebras (Brown--Clark--Farthing--Sims, arXiv:1204.3127). It is proved directly in the artifact.
- **Periodic models:** the return-word approximation of minimal subshifts behind Grigorchuk--Medynets'
  LEF theorem for topological full groups (arXiv:1105.0719), here in ring form.
- **Nearest prior art:** Thom, arXiv:0810.2180, Theorem 1.4, a finitely generated LEF Kazhdan group
  that is not residually finite and is not simple. `S` strengthens this to a simple group.
- **Kills recorded as graph structure.** The four routes listed under `invalidates:` all rested on
  "every infinite simple Kazhdan group has full MF radical". `S` refutes that statement.
- **New here:** passing to `EL_3` over the crossed-product ring, root detection through tower
  subrings, and the resulting simple Kazhdan LEF group.
