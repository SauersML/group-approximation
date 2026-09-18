---
rg: 2
id: ak3-is-stably-ac-trivial
kind: claim
title: The Akbulut–Kirby presentation AK(3) is stably Andrews–Curtis trivial
distinct_from:
  andrews-curtis-conjecture: that is the unstable conjecture for all balanced presentations; this is the stable question for AK(3) alone, which the unstable conjecture would imply
artifacts:
  - research/artifacts/hl-andrews-curtis-status-2026-09-13.md
---

**OPEN.** AK(3) = ⟨x, y | x^3 = y^4, xyx = yxy⟩ is stably AC-trivial (moves
(AC1)–(AC5) of `stable-andrews-curtis-conjecture`).

## Status correction (2026-09-13)

Secondary summaries repeat that Shehper et al. (2024) proved this. Their current
version, arXiv:2408.15332v2 (11 Feb 2025), says otherwise.
- `sec/introduction.tex` l.91: "we discovered a subtle misprint in \cite[p.10]{MMS}
  that had gone unnoticed for more than 20 years. This misprint undermines the claim
  that \eqref{eq:MMS3} is stably AC-trivial."
- `sec/stable.tex` l.195: the misprint "affect[s] the validity of one of their main
  theorems (\cite[Theorem 1.4]{MMS})".
- The former appendix `app/stable_ak3` is commented out of `ac_paper.tex`.

Lisitsa (arXiv:2501.18601, l.475–479) gives automated proofs that the MMS3
presentation P is AC-equivalent to AK(3). For stable triviality it cites the same
MMS/ACE family claim, Myasnikov–Myasnikov–Shpilrain, Contemp. Math. 296 (2002). So
neither source establishes this claim.

Verbatim pins are in the artifact.

## Attempts

1. **Through the MMS unknot family.** Dead as printed: the 13th Wirtinger relator is
   misprinted. For correct unknot diagrams, Shehper et al. prove the resulting
   presentations AC-trivial (Theorem `thm:unknot`, `sec/stable.tex` l.217). So no
   correct member of that family is AC-equivalent to AK(3) unless AK(3) is AC-trivial.
2. **Through one stabilization.** The route `ak3-stably-ac-trivial-via-one-stabilization`
   waits on `balanced-trivial-presentations-one-stabilization-ac-trivial`.
   By `shehper-z-conjecture-iff-one-stabilization-ac`, the rank-3 case of that
   premise is exactly Shehper et al.'s Conjecture `conj:general_Z` on 3 generators.
3. **Primitive-relator and projection certificates in rank 3 (sw-081, 2026-09-17).**
   `one-stabilization-ac-trivial-from-primitive-relator` gives checkable certificates. Under
   relator-pair AC moves and automorphisms of F(x, y, z), reach either a pair with a primitive
   relator, or a pair whose rank-2 projection (delete a generator with exponent-sum minor ±1)
   has total length ≤ 12. The exhaustive search `ak3-no-short-primitive-relator-certificate`
   finds neither through pairs of total length ≤ 24. Every projection of length ≤ 16 found
   there lies in the rank-2 AC-plus-automorphism class of AK(3), so at these lengths the extra
   generator gives nothing new.
