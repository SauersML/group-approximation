---
rg: 2
id: arithmetic-pair-group-factor-ultrapower-has-no-leak
kind: claim
title: The arithmetic Hecke pair has no relative-commutant leak in the ultrapower of its own group factor
distinct_from:
  relative-commutant-collapse-for-sl2-pair: that asks for the collapse in every MATRIX ultraproduct model of the pair; this proves it in the ultrapower of the group factor itself and shows the whole matrix question lives in the orthocomplement of the group factor inside the ambient algebra.
  hecke-far-commutator-defect-formula: that computes the far Hecke defect of a leak in an arbitrary tracial model; this shows that in one specific tracial model, the self-ultrapower of L(A), no leak exists at all.
  ccr-group-algebra-slice: that kills the group-algebra-supported counterexample channel for the Kun--Thom compressor pair inside L(G); this does the same for the arithmetic pair and, in addition, kills the APPROXIMATE (central-sequence) channel, which for the non-Kazhdan SL_2 pair needs amenable centralizers rather than property (T).
---

Let `p` be a prime, `n >= 2`, and

```text
C = SL_n(Z)  <=  A = SL_n(Z[1/p]),      Z = Z(A) = {+-1} (n even) or {1}.
```

Let `L(A)^omega` be the tracial ultrapower of the group von Neumann algebra
along a free ultrafilter.  Then

```text
L(C)' cap L(A)^omega  =  L(A)' cap L(A)^omega  =  L(Z)^omega.          (UPL1)
```

In words: every bounded sequence in `L(A)` that asymptotically commutes
with the group elements of `C` asymptotically lies in the centre
`L(Z) = Z(L(A))`.  Three consequences:

1. **RCC holds in the standard model.**  The relative-commutant collapse
   `(RCC)` of `relative-commutant-collapse-for-sl2-pair` (and its `SL_3`,
   `SL_5` siblings) is true when the ambient tracial algebra is the
   self-ultrapower `M = L(A)^omega`.  Consequently the HNN group
   `G = <A, t | [t, C] = 1>` admits no trace-preserving embedding
   `L(G) -> L(A)^omega` extending the diagonal inclusion
   `L(A) subset L(A)^omega`: the stable letter cannot be realised as a
   central-sequence-type element over the group factor.
2. **Fullness.**  `L(A)` has no nontrivial central sequences modulo its
   centre, i.e. `L(PSL_n(Z[1/p]))` is a full factor, and the inclusion
   `L(C) subset L(A)` has spectral gap in Popa's sense.
3. **Where the matrix question lives.**  For ANY tracial von Neumann
   algebra `M supseteq L(A)` (trace-preserving inclusion), decompose
   `L^2(M) = L^2(L(A)) (+) K_M` as `C`-modules for the conjugation action
   `Ad pi(c)`.  The `C`-fixed vectors of the first summand are exactly
   `L^2(L(Z))`, already `A`-fixed.  Hence

   ```text
   (RCC) for the embedding L(A) subset M
     <=>  every C-fixed vector of K_M = L^2(M) (-) L^2(L(A)) is A-fixed.  (UPL2)
   ```

   So a matrix-ultraproduct counterexample to `(RCC)` is a `C`-central,
   non-`A`-central vector living entirely in the `L(A)`-bimodule
   `K_M`; nothing supported on the group factor, exactly or
   asymptotically, can contribute.  This is the arithmetic-pair analogue
   of the `M (-) L(G)` reduction recorded for the Kun--Thom compressor in
   `kt-centralizer-normalization-hs` (2026-08-18d), now including the
   approximate channel and the non-Kazhdan `n = 2` case.

The proof mechanism is the one a matrix model would have to reproduce
on `K_M`: the conjugation action of `C` on `l^2(A) (-) l^2(Z)` is a sum
of quasi-regular representations `l^2(C / C_C(g))` over the
`C`-conjugacy orbits of non-central `g in A`.  For `n = 2` every such
centraliser `C_C(g)` is abelian, so each summand is weakly contained in
the regular representation of the non-amenable group `C` and the sum has
a uniform spectral gap; for `n >= 3` every orbit is infinite and property
(T) of `C` supplies the gap.  Either way a `C`-almost-central sequence in
`L(A)` has vanishing component outside `L^2(L(Z))`.

Cautions.  `(UPL1)` is a statement about one tracial model and says
nothing about `R^omega`: the goal-relevant models are matrix
ultraproducts `M` in which `L(A)` is embedded by regular-trace
microstates, and there `K_M` is a genuinely new `L(A)`-bimodule.  The
claim is a calibration and a reduction, not progress on the matrix wall:
it shows the wall cannot be refuted through the group factor or its
central sequences, and that every proof attempt must control `K_M`.
