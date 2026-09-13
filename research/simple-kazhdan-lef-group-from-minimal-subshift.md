---
rg: 2
id: simple-kazhdan-lef-group-from-minimal-subshift
kind: claim
title: EL_3 over a minimal subshift algebra modulo its centre is an infinite simple Kazhdan LEF group
distinct_from:
  infinite-simple-kazhdan-hyperlinear-group: that is Pestov's existential question; this is one explicit group, which would answer it in the stronger sofic form.
  binary-leavitt-elementary-group-is-simple: that group lives over a purely infinite ring and is nonsofic; this one lives over a stably finite ring that embeds in ultraproducts of matrix algebras, and is LEF.
  simple-kazhdan-kac-moody-lattices-exist: those groups are finitely presented and therefore never LEF; this group is infinitely presented and LEF.
artifacts:
  - research/artifacts/simple-kazhdan-lef-subshift-elementary-group-2026-09-12.md
  - research/artifacts/simple-kazhdan-lef-consequences-and-sources-2026-09-12.md
---

Let `q` be a prime power, `X` an infinite minimal subshift (for example Fibonacci), and
`R = LC(X,F_q) ⋊ Z`. Put `G = EL_3(R)` and `S = G / Z(G)`. Then `S` is a finitely generated group
which is:

1. infinite and simple;
2. Kazhdan;
3. LEF, hence sofic, hence hyperlinear.

In particular it answers Pestov's Open Question 9.1 positively, in both the hyperlinear and the
sofic form. `S` is also the marked limit of the finite simple groups `PSL_(3N_k)(F_q)`, with
generating sets modulated by periodic return words of `X`. It is operator MF and, by Ozawa--Thom,
not weakly quasidiagonal.

**Status: complete written proof, UNREVIEWED.** The proof is in the Part 1 artifact. The route
`simple-kazhdan-lef-group-from-minimal-subshift-proof`, and the route into
`infinite-simple-kazhdan-hyperlinear-group`, are held until an independent `ex-verify` check,
following the swarm's gate for results that settle a named open question.

## Attempts

- **Subshift tower root detection (lane ex-kazhdan-simple-hyperlinear, 2026-09-12).**
  - (1) comes from `subshift-elementary-group-is-simple-modulo-centre`.
  - (2) comes from `elementary-groups-over-fg-rings-have-property-t`, since quotients of Kazhdan
    groups are Kazhdan.
  - (3) holds for `G` by `minimal-subshift-algebra-is-simple-lef-ring`. It passes to `S`: the
    finite central `Z(G) = Λ I_3` maps to the constant central `Λ I` in each `GL_(3N_k)(F_q)`, so
    `S` embeds in `prod_omega GL_(3N_k)(F_q)/Λ I` (artifact Part 1, §3.3). LEF gives sofic through
    left regular permutation representations, and sofic gives hyperlinear.

  No failing step is known. It is awaiting review.
- **Cross-check through operator MF.** `S` is LEF, hence operator MF (`lef-implies-operator-mf`).
  So the kernel-checked `kazhdan-mf-hyperlinear-fragment` (a simple Kazhdan MF group is hyperlinear)
  gives hyperlinearity of `S` by a second, analytic route, once (1) and (2) are accepted.
