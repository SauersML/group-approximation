---
rg: 2
id: once-punctured-mcgs-are-continuous-asynchronous-automatic
kind: claim
title: The mapping class group of every once-punctured surface of genus at least one is continuous asynchronous automatic, and hence embeds in the rational group of Grigorchuk, Nekrashevych and Sushchanskii
distinct_from:
  mapping-class-groups-are-continuous-automatic: that is BBCMP Question 1.16, which asks for continuous (synchronous) automatic structures on all finite-type mapping class groups; this gives the asynchronous version for every once-punctured surface, including S_{2,1} and all genera at least three.
  low-complexity-mapping-class-groups-are-continuous-automatic: that gives synchronous continuity only for surfaces commensurable with braid groups modulo center or with SL_2(Z); this reaches all genera, asynchronously, through Mosher's normal forms.
  mosher-suffix-uniqueness-gives-continuous-inverse-normal-forms: that is the general lemma; this applies it to Mosher's structure on the mapping class groupoid.
  closed-mcg-embeds-in-rational-projective-full-group: that embeds closed-surface mapping class groups in a full group of integral projective germs; this embeds once-punctured ones in the rational group.
artifacts:
  - research/artifacts/gq-bh-bh-hhg-bbmz-method-for-hhgs.md
---

**ESTABLISHED** (lane proof, not reviewed; no priority claimed), modulo the cited
property (S) of Mosher's structure, which is quoted from source but whose proof is only
indicated there. Proof: `once-punctured-mcg-continuous-asynchronous-proof`.

## Statement

Let `S` be a closed oriented surface of genus `g ≥ 1` with one puncture `p`, and let
`Mod(S)` be the group of orientation-preserving homeomorphisms fixing `p`, modulo
isotopy fixing `p`. This is Mosher's convention, and it is `Mod(S_{g,1})`.
1. `Mod(S_{g,1})` is **continuous asynchronous automatic**, in the sense of
   Belk--Bleak--Chatterji--Matucci--Perego (BBCMP, preliminary version, §1.1).
2. Hence, by BBCMP Corollary 1.9, `Mod(S_{g,1})` **embeds in the rational group** of
   Grigorchuk--Nekrashevych--Sushchanskii.

## The input (S), quoted

Mosher, *A user's guide to the mapping class group: once punctured surfaces*,
arXiv:math/9409209, §IV, read from the TeX:

> "from the description of the subroutine *Do one move* it follows that the asynchronous
> automatic structure `𝓛_0` for the groupoid `𝓜𝒞𝒢` satisfies suffix uniqueness, with
> fellow traveller constant `K=1` and maximal suffix length `n=3`."

Also from §§I–II:
- `𝓛_0` is an asynchronous automatic structure on the mapping class groupoid, with
  unique normal forms and prefix closed.
- The groupoid is the edge-path groupoid of a finite 2-complex `X` with
  `π_1(X) = Mod(S)`.
- The algorithm processes normal forms "from back to front".

## Scope

- **Asynchronous only.** BBCMP Question 1.16 asks about synchronous structures. Mosher's
  synchronous structure `𝓛_1` (Dehn twist factorization, §V) would give the synchronous
  version if it also has suffix uniqueness. The guide uses that only as a hypothesis of
  its technique; it does not state it for `𝓛_1`, so this is not claimed.
- **Closed and multiply-punctured surfaces are not covered.** Mosher's closed-surface
  structure "is described in [M]" but is "not suited for practical calculation, because
  of the non-constructive nature of the proof". No suffix uniqueness is available for it
  here.
- **Boone--Higman is not new.** Punctured surfaces are already covered by BFFHZ. What is
  new is continuity and the rational-group embedding.
- **Citations taken as printed.** BBCMP Corollary 1.9 and its asynchronous closure
  properties, Proposition 1.4(4).
