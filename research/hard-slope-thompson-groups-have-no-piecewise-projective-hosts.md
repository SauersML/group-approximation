---
rg: 2
id: hard-slope-thompson-groups-have-no-piecewise-projective-hosts
kind: claim
title: For computable Liouville slopes λ with hard digits, the simple group D(V_λ) embeds in no finitely presented group of piecewise-projective maps of an interval, circle or line; in particular V_λ and D(V_λ) are not finitely presented
requires:
  - fp-piecewise-projective-groups-specialize-to-algebraic-data
  - transcendental-slope-thompson-groups-have-hard-word-problems
distinct_from:
  transcendental-slope-thompson-groups-satisfy-boone-higman: that is the open embedding question for all computable transcendental λ; this excludes, for the hard λ, every finitely presented one-dimensional piecewise-projective host, simple or not.
  fp-pl-groups-with-f-have-no-transcendental-support-endpoints: that excludes finite presentation of PL groups containing a dyadic F and a transcendental bump; this excludes every finitely presented piecewise-projective overgroup of D(V_λ), which need not contain a dyadic F and may have any real data.
  stein-derived-groups-need-computable-modules: that notes non-finite presentation of D(V_λ) conditionally on Tanner's homology computation; for the hard λ this proves it unconditionally, together with non-finite presentation of V_λ.
---

**ESTABLISHED** (lane proof, not reviewed; a two-line combination of the required nodes).

## Statement

Let `λ ∈ (0,1)` be computable and transcendental, and suppose the word problem of `D(V_λ)` is not
solvable in polynomial time. Such `λ` exist: item 2 of
`transcendental-slope-thompson-groups-have-hard-word-problems` with `T(l) = 2^l` gives computable
Liouville examples. Then:

1. `D(V_λ)` embeds in no finitely presented group that acts faithfully by piecewise-projective
   maps (finitely many increasing Möbius pieces, arbitrary real data) on an interval, the circle
   or the line.
2. In particular `V_λ` and `D(V_λ)` are not finitely presented, and neither is any Stein,
   Bieri--Strebel, Thompson-like, irrational-slope or Lodha--Moore-type group containing
   `D(V_λ)`.
3. So a finitely presented simple host of `D(V_λ)`, if one exists, is not one-dimensional
   piecewise projective. It must come from higher-dimensional or Cantor-type constructions such as
   `nV`, twisted Brin--Thompson groups `SV_G`, or Röver--Nekrashevych groups.

## Proof

`D(V_λ)` is finitely generated and simple (Tanner, arXiv:2312.07375). If it lay in such a finitely
presented `G`, then by item 3 of `fp-piecewise-projective-groups-specialize-to-algebraic-data` it
would embed in `PP_K` for a real number field `K`, and its word problem would be polynomial-time.
That contradicts the hypothesis, which proves item 1. Item 2 follows because `V_λ` and `D(V_λ)` are
groups of PL maps of `[0,1)` containing `D(V_λ)`. ∎

## Remarks

- Item 2 does not use Tanner's homology `H_2(D(V_λ);Q) ≅ ⊕ Q`, on which the general transcendental
  non-finite presentation rests.
- For slopes with cheap digits, such as `1/e` or `π − 3`, the specialization theorem still says:
  `D(V_λ)` lies in a finitely presented PP group only if it embeds in `PP_K` over a real number field.
  Whether that can happen for transcendental `λ` is open.
