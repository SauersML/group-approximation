---
rg: 2
id: positive-char-linear-groups-satisfy-boone-higman
kind: claim
title: Every finitely generated linear group over a field of positive characteristic satisfies Boone--Higman
root: true
distinct_from:
  char-two-linear-groups-satisfy-boone-higman: that is characteristic two only; this is every prime, where the hosts are elementary groups of Leavitt tensor powers modulo their finite scalar centres.
  positive-char-surface-linear-groups-satisfy-boone-higman: that is the established case of transcendence degree at most two; this is every transcendence degree.
artifacts:
  - research/artifacts/boone-higman-char-p-all-degrees-2026-09-12.md
---

**ESTABLISHED (2026-09-12)** through
`positive-char-linear-groups-via-leavitt-projective-elementary`, once
`leavitt-tensor-powers-have-vanishing-k-theory-in-all-degrees` supplied
`K_1 = K_2 = 0` for every tensor power. Not independently reviewed; see
attempt 4 for the imports it rests on.

Let `K` be a field of characteristic `p > 0` and `H <= GL_n(K)` finitely
generated. Then `H` embeds in a finitely presented simple group.

*Marked `root` because it is a natural class question in its own right.* The
Belk--Bleak--Matucci--Zaremsky survey arXiv:2306.16356v3 names no
positive-characteristic linear class. This graph proves transcendence degree
`<= 2` (`positive-char-surface-linear-groups-satisfy-boone-higman`).

The route `positive-char-linear-groups-via-leavitt-projective-elementary`
needs exactly `leavitt-power-projective-elementary-groups-finitely-presented`.

## Attempts

1. **Tensor-power hosts with `K_1 = K_2 = 0`.** `(L_p^(⊗d))^x / F_p^x` is
   finitely presented and simple once low `K`-theory vanishes.
   *Stops* at `prime-field-leavitt-tensor-powers-have-trivial-k-theory` for
   `d >= 3`.
2. **Projective elementary hosts.**
   - `char-p-linear-groups-embed-in-projective-leavitt-power-e-groups` puts
     every such `H` of transcendence degree `d` in the simple group
     `E_M(L_p^(⊗(d+1))) / Z` with no `K`-theory hypothesis. It stabilizes by
     `X |-> diag(X, I)`, and one extra factor kills the `K_1` classes by the
     corner swindle.
   - The Whitehead map `X |-> diag(X, X^-1, 1)` is dead: it is not a
     homomorphism (`whitehead-diagonal-map-is-not-multiplicative`).
   - *Stops* at finite presentation of that group, which is finite normal
     generation of the unstable Steinberg kernel. `K_1` is not needed.
3. **Fewer tensor factors.** No commutative domain of transcendence degree 3
   is known inside `L_p ⊗ L_p`.
   *Not disproved*: a unital embedding `F_p[t_1, t_2, t_3] -> L_p ⊗ L_p` would
   settle `d = 3` without new `K`-theory.
4. **Settled through the Farrell–Jones conjecture** (lane
   `bh-leavitt-nil-k-regularity`, 2026-09-12).
   - **The crux.** `prime-field-leavitt-tensor-powers-have-trivial-k-theory` is
     now established by `leavitt-tensor-powers-have-vanishing-k-theory-in-all-degrees`.
     `L_p^(⊗d)` is a crossed product by `Z^(d−1)` over a semihereditary,
     `K`-trivial coefficient ring. Farrell–Jones with additive coefficients for
     `Z^(d−1)` and the vanishing of twisted Nil terms give `K_n = 0` in every
     degree.
   - **The chain.** So `leavitt-power-projective-e-fp-from-trivial-k-theory`
     completes, and with it
     `positive-char-linear-groups-via-leavitt-projective-elementary`.
     `cairn why` on MSI reads this root ESTABLISHED.
   - **What it rests on.**
     - Literature imports: Bartels–Farrell–Lück arXiv:1101.0469, Bartels–Reich
       arXiv:math/0510602, Bartels–Lück arXiv:2002.03412 and Lück–Steimle
       arXiv:1309.1353, all read from arXiv sources.
     - Main's earlier imports behind the host claim
       `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre`, including
       `khanh-acyclicity-and-steinberg-criteria` (unrefereed preprint).
     - The reviewed embedding claim.
   - **Not yet done.** This lane did not recheck those earlier imports, and the
     new derivation has not been independently reviewed.
