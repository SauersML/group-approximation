---
rg: 2
id: rich-2to1-perfect-completeness-has-robust-basic-sdp-gaps
kind: claim
title: For every delta > 0 there is n such that, for every eta > 0, some rich 2-to-1 instance with alphabets [2n], [n] has basic SDP value at least 1 - eta and integral value at most delta
distinct_from:
  walsh-frame-rich-2to1-games-have-value-near-one: that rules out one family of perfect SDP solutions as a gap; this asks whether any robust gap exists.
  sd-rich-and-unique-games-sos-gaps-interconvert: those gaps have completeness 1 - eta(n) with eta(n) tied to the alphabet, so at fixed n they do not beat a small threshold; this asks for every eta at fixed n.
---

**OPEN.** Proposed route: `robust-basic-sdp-gaps-from-rotated-frame-universe`.

This is the basic-SDP evidence question for BKM Conjecture 7 in the form that
matters at perfect completeness. If it is false, then for some `delta` and
every `n` there is `eta_0(n) > 0` such that basic SDP `>= 1 - eta_0(n)` implies
`val > delta`. That would be a polynomial-time algorithm for
`Gap-Rich-2-to-1_n[1, delta]` at every `n`, refuting Conjecture 7 unless
P = NP. If it is true, the basic SDP gives no such refutation, which is
consistent with the conjecture but proves nothing about hardness.

The GKOPTW Walsh-framed universe is not a witness
(`walsh-frame-rich-2to1-games-have-value-near-one`). The rotated-frame universe
is the surviving candidate. Its discretisation half is established; its
value half is open.

## Attempts

- 2026-09-17, e-ugc-pull-transplant (transplanter via finite-models):
  - Obvious witness: Khot--Vishnoi unique-games gaps, right-merged into rich
    games. It dies at the quantifier order. Their completeness is
    `1 - eta(n)` with `eta(n)` about `log(1/delta)/log n`, so at a fixed `n` a
    threshold `eta_0 < eta(n)` rejects them.
  - Second witness: GKOPTW Walsh-framed perfect solutions, enriched. It dies at
    forcing edge mass, which gives value `>= 1 - B(K)`.
  - Third witness: the rotated-frame universe `U_n`. It survives. The
    discretisation step is established. The value step is reduced to (A1) and
    (A2) in `rotated-frame-universe-rich-2to1-game-has-vanishing-value`, and
    every tested potential strategy decays like `n^(-0.2)` numerically.
