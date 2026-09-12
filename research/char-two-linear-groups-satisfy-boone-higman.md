---
rg: 2
id: char-two-linear-groups-satisfy-boone-higman
kind: claim
title: Every finitely generated linear group over a field of characteristic two satisfies Boone--Higman
root: true
distinct_from:
  char-two-surface-linear-groups-satisfy-boone-higman: that is the established case of transcendence degree at most two; this is every transcendence degree, where the host (L^(⊗d))^x needs K_1 and K_2 of the tensor power to vanish.
  char-two-curve-linear-groups-satisfy-boone-higman: that is transcendence degree at most one in L^x; this is the full positive-characteristic-two linear class.
artifacts:
  - research/artifacts/boone-higman-leavitt-tensor-hosts-2026-09-12.md
---

**ESTABLISHED (2026-09-12)** through
`char-two-linear-groups-via-leavitt-tensor-powers`, once
`leavitt-tensor-powers-have-trivial-k-theory` was established. Not independently
reviewed; see attempt 3.

Let `K` be a field of characteristic two, and let `H <= GL_n(K)` be finitely
generated. Then `H` embeds in a finitely presented simple group.

*Marked `root` because it is a natural class question in its own right.* The
Belk--Bleak--Matucci--Zaremsky survey (arXiv:2306.16356v3, Problem 5.3) lists
`GL_n(Q)` among the open cases, settled later by Zaremsky arXiv:2405.09722, and
names no positive-characteristic linear class. This graph proves transcendence
degree `<= 2` (`char-two-surface-linear-groups-satisfy-boone-higman`).

The conditional route `char-two-linear-groups-via-leavitt-tensor-powers` needs
exactly `leavitt-tensor-powers-have-trivial-k-theory`.

## Attempts

1. **Inside one `L`.** Any commutative subring of `M_k(F_2[g^±])` has Krull
   dimension at most one, by Cayley--Hamilton.
   *Dies*: two commuting Thompson units with disjoint supports satisfy
   `(u-1)(v-1) = 0`, and no two-dimensional Laurent ring was found in `L`.
2. **Tensor powers.** Artifact Lemma 7.1 puts `F_2[t_1, ..., t_d][1/h]` in
   `L^(⊗d)`. `leavitt-tensor-hosts-acyclic-steinberg-and-fp` and
   `central-simple-leavitt-tensor-unit-groups-are-simple` then make
   `(L^(⊗d))^x` finitely presented and simple once `K_1` and `K_2` vanish.
   *Stops* at `leavitt-tensor-powers-have-trivial-k-theory` for `d >= 3`.
3. **Settled** (lane `bh-leavitt-nil-k-regularity`, 2026-09-12).
   - **The crux.** `leavitt-tensor-powers-have-trivial-k-theory` is now
     established by `leavitt-tensor-powers-have-vanishing-k-theory-in-all-degrees`.
     The proof writes `L^(⊗d)` as a crossed product by `Z^(d−1)` over a
     `K`-trivial regular ring, then applies Farrell–Jones with additive
     coefficients together with Nil vanishing.
   - **The chain.** So the route of attempt 2 completes, and `cairn why` on MSI
     reads this root ESTABLISHED.
   - **What it rests on.** Those imports, and main's earlier ones behind
     `leavitt-tensor-hosts-acyclic-steinberg-and-fp` and
     `central-simple-leavitt-tensor-unit-groups-are-simple`. Those earlier
     imports include `khanh-acyclicity-and-steinberg-criteria`, an unrefereed
     preprint.
   - **Not yet done.** The new derivation has not been independently reviewed.
