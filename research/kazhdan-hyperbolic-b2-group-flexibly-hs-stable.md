---
rg: 2
id: kazhdan-hyperbolic-b2-group-flexibly-hs-stable
kind: claim
title: Some hyperbolic Kazhdan group with positive second Betti number is flexibly Hilbert--Schmidt stable
distinct_from:
  kazhdan-weak-ucp-stability-is-flexible-stability: that identifies weak ucp-stability with flexible HS-stability for hyperlinear Kazhdan groups; this asks for flexible HS-stability of one hyperbolic Kazhdan group with b_2 >= 1, which that equivalence may be used to restate
  random-complex-linear-cocycle-stability: that is a permutation cocycle-stability estimate for random complexes; this is unitary stability of a group, with no Hamming metric and no randomness required
---

**OPEN, conjectural.** There is a word-hyperbolic group `Γ` with property (T) and
`b_2(Γ;Q) >= 1` that is flexibly Hilbert--Schmidt stable. Every asymptotic
representation in normalized Hilbert--Schmidt norm is close, after enlarging the
dimension, to a genuine representation.

By `kazhdan-hyperbolic-hs-stability-kills-hyperlinearity` this gives a
non-hyperlinear hyperbolic group, which is both nonsofic and not residually finite.

## Candidates

* **Gromov density-model random groups at density in `(1/3, 1/2)`.** Source-verified
  in `density-random-group-hyperbolic-kazhdan-with-positive-b2`: w.o.p. torsion-free,
  hyperbolic, Kazhdan, with a finite aspherical presentation complex and
  `b_2 = |R| - m >= 1`. That is existence w.o.p., with no certified presentation.
  Dogon's 2023 theorems already list them for the infinite cyclic extension; see
  `kazhdan-weak-ucp-stability-is-flexible-stability`.
* **Hyperlinear candidates.** Stability of a hyperlinear candidate forces a persistent
  prime degree-two class (`hs-stable-hyperlinear-kazhdan-hyperbolic-forces-persistent-class`),
  so it is no easier than Gromov's question.
* **Square complexes with projective-plane links are not candidates.** They are CAT(0)
  cube complexes, so they admit no Kazhdan instance.
* **Mid-range Linial--Meshulam groups `π_1(Y(n, n^(-1+η)))`.** They are hyperbolic
  and Kazhdan a.a.s. (`random-complex-mid-range-pair-properties`, plus Garland--Żuk
  for λ < 1/2), with `b_2(Y) = χ(Y) - 1 ~ p·C(n,3)`. For `b_2(π_1 Y)` one must
  still bound the image of `π_2(Y)` (Hopf).

## What it cannot be

Strict HS-stability is excluded for every infinite hyperlinear Kazhdan group by
Becker--Lubotzky, so only the flexible notion is available. Reading the claim
contrapositively: if all hyperbolic groups are hyperlinear, this claim is false.

## Attempts

- **Class-wide stability is screened.** By
  `classwide-hyperbolic-kazhdan-hs-stability-covers-fp-kazhdan`, an argument proving
  flexible HS stability for every hyperbolic Kazhdan group would make every finitely
  presented Kazhdan group stable. So would one for any class closed under
  Belegradek--Osin covers. Such an argument would therefore make the binary Leavitt
  unit group and the Caprace--Rémy simple lattices non-hyperlinear. A proof for the
  candidates has to use a feature that such covers lack.
- **Covers add nothing.** By `flexible-hs-stability-passes-to-kazhdan-kernel-quotients`,
  stability of a hyperbolic Kazhdan group passes to each of its quotients by Kazhdan
  normal subgroups. So a cover is never easier to stabilize than its quotient.
- **`Ã_2` Ballmann--Świątkowski groups are not candidates.** They act properly and
  cocompactly on Euclidean buildings, contain `Z^2`, and so are not hyperbolic.
- **`GHB(7)`: now an explicit certified candidate, stability open.** It is
  Caprace--Conder--Kaluba--Witzel's KMS group `G_{HB_2}(7)`, with property (T) compiled
  in `GroupApproximation/Kazhdan/EJZAngleGHB.lean`. It has torsion, and `b_2(GHB(7);Q) = 0`.
  - **The torsion-free kernel.** The kernel `H` of the vertex-injective quotient
    `ψ : GHB(7) → SL_4(F_7)` (CCKW Prop 7.15; relator checks and vertex injectivity compiled)
    is torsion-free of finite index by CCKW Theorem 3.1(iv).
  - **Its invariants.** `H` acts freely on the CAT(−1) triangle complex. Counting cells gives
    `χ(H) = [G:H]·1381/2401`, so `b_2(H;Q) >= 1380`.
    See `ghb7-congruence-kernel-hyperbolic-kazhdan-with-large-b2` (established) and
    `research/artifacts/ghb7-kernel-certified-candidate-2026-09-12.md`.
  - **What is left.** The premise reduces to the single explicit statement
    `ghb7-congruence-kernel-flexibly-hs-stable`, through the route
    `kazhdan-hyperbolic-b2-stability-via-ghb7-kernel`. There is no stability input yet.
- **Cocompact `Sp(2,1)` lattices.** They are linear, hence hyperlinear and residually
  finite, so they fall under the hyperlinear bullet above. Their `b_2` has not been
  verified from a source.
- **No known example.** No source read for this node exhibits a flexibly HS-stable
  infinite property (T) group.

The candidate-by-candidate record is
`research/artifacts/kazhdan-hyperbolic-hs-candidates-2026-09-12.md`.
