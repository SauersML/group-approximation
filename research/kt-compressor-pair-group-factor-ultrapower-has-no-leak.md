---
rg: 2
id: kt-compressor-pair-group-factor-ultrapower-has-no-leak
kind: claim
title: The Kun--Thom compressor pair has no relative-commutant leak in the ultrapower of its own group factor
distinct_from:
  ccr-group-algebra-slice: that is the EXACT group-algebra slice, elements of L(G) commuting with the compressed copy; this is the approximate slice, bounded sequences in L(G) asymptotically commuting with it, which needs property (T) on top of the finite-orbit lemma.
  approximate-collapse-for-kt-compressor: that is the (AC) wall inside a tracial MATRIX ultraproduct; this proves the same identity in the self-ultrapower of L(G), a different tracial model, and so localises the wall to the orthocomplement of L(G).
  arithmetic-pair-group-factor-ultrapower-has-no-leak: that is the same statement for the arithmetic Hecke pair SL_n(Z) <= SL_n(Z[1/p]), where for n = 2 the gap comes from abelian centralisers; here the pair is the Kun--Thom compressor pair and the gap comes from property (T) of the compressed copy.
---

Let `(Gamma, G, t, Lambda = t Gamma t^-1)` be the Kun--Thom compressor
pair of `ccr-group-algebra-slice`: `Gamma = EL_r(F_q[x_1..x_d])` inside
`G = EL_r(F_q[x_1^(+-1)..x_d^(+-1)]) rtimes SL_d(Z)`, `r >= 3`, with
`Lambda = EL_r(S)` for the compressed monomial subalgebra `S`, and let
`Z = Z(G)` be the central scalars.  Then in the tracial ultrapower of the
group factor

```text
L(Lambda)' cap L(G)^omega  =  L(Gamma)' cap L(G)^omega
                           =  L(G)' cap L(G)^omega  =  L(Z)^omega.        (KTU1)
```

So the compressor-commutant rigidity `(CCR)`/`(AC)` of
`kt-centralizer-normalization-hs` and `approximate-collapse-for-kt-compressor`
holds when the ambient tracial algebra is `M = L(G)^omega`, `L(G)` is a full
factor modulo its centre, and for ANY tracial `M supseteq L(G)` the wall is
confined to the orthocomplement: with `L^2(M) = L^2(L(G)) (+) K_M`,

```text
(CCR)_M for the embedding L(G) subset M,  i.e.  L(Lambda)' cap M = L(Gamma)' cap M,
  <=>  every Lambda-fixed vector of K_M is Gamma-fixed.                 (KTU2)
```

This is the approximate companion of the exact slice: the exact slice says
no element of `L(G)` leaks, this says no central-sequence-type element of
`L(G)` leaks either, so the matrix-ultraproduct question of
`approximate-collapse-for-kt-compressor` is exactly about
`Lambda`-central elements of `M` orthogonal to `L(G)`.

**Restatement note (2026-08-22 audit).**  `(KTU2)` formerly used the symbol
`(AC)`, which in `approximate-collapse-for-kt-compressor` names a
different, OPEN statement (a `dist_2`-limit condition quantified over all
trace-faithful matrix-ultraproduct representations); the equivalence here
is for ONE fixed embedding `L(G) subset M`, is essentially a localization
(the `Lambda`-fixed vectors of `L^2(M)` are `L^2(L(Lambda)' cap M)`), and
does not assert `G`-fixedness on `K_M`, which is proved only on the
`L^2(L(G))` summand.  Also, `L(G)` is a finite direct sum of full II_1
factors when `Z(G) = {lambda I : lambda^r = 1}` is nontrivial, not "a
full factor modulo its centre".  `(KTU1)` is unaffected.
