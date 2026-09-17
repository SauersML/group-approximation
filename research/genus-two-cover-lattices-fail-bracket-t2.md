---
rg: 2
id: genus-two-cover-lattices-fail-bracket-t2
kind: claim
title: No finite-index subgroup of the genus-two universal-cover lattice or of any Deligne cover of Sp_4(Z) has property [T_2]
distinct_from:
  sp2g-universal-cover-lattice-is-operator-hs-stable: that is the g >= 3 instance of BDL Conjecture 1.8, where [T_2] holds; this proves that at g = 2 the [T_2] hypothesis fails for the cover lattice and for every finite-index subgroup, so no genus-two instance of Conjecture 1.8 exists.
  blsw-real-lattice-frobenius-stability: that imports [T_2] and Frobenius stability for universal-cover lattices in rank at least three; this shows that the rank-two genus-two cover lattice is outside its hypothesis, even virtually.
  deligne-sp2g-covers-mf-radical-is-2z-at-genus-three: that derives non-MF of Deligne covers from operator-HS-stability for g >= 3; this blocks the [T_2] input at the one genus the triple-cover goal needs.
---

**ESTABLISHED** (`genus-two-cover-lattices-fail-bracket-t2-proof`).

**Setting.** Let `Gamma~_2` be the preimage of `Sp_4(Z)` in the universal cover
of `Sp_4(R)`, with central kernel `<z> = Z`. For `n >= 1` let
`E_n = Gamma~_2/<z^n>` be the Deligne cover. A group `Gamma` has property
`[T_2]` if `H^i(Gamma, V) = 0` for every unitary representation `V` and
`i = 1, 2` (BLSW Definition 1.2, quoted in `blsw-real-lattice-frobenius-stability-citation`).

**Statement.** Let `G` be `Gamma~_2` or some `E_n`, and let `Delta <= G` have
finite index. Let `Lambda_G` be the preimage of `Gamma_2(4) = ker(Sp_4(Z) -> Sp_4(Z/4))`
in `G` and `Delta' = Delta ∩ Lambda_G`. Then

```text
dim_C H^2(Delta; l^2(Delta/Delta')) >= 117,                          (G2T1)
```

so `Delta` fails `[T_2]`. The coefficient module is a finite-dimensional
permutation representation. It is a subrepresentation of `Ad(pi)` on
`M_N(C)`, where `pi` is the permutation representation and `N = [Delta:Delta']`.
Hence `H^2(Delta; M_N(C), Ad pi) != 0` for a genuine finite-dimensional unitary
representation `pi` with finite image, whose kernel contains the central subgroup `Delta ∩ <z>`.

**Invariant and where the class dies.** The invariant is
`b_2(Gamma_2(4)) = 118`, imported from `hoffman-weintraub-level-four-siegel-betti-numbers`.
Consider any argument that rounds asymptotic representations of `Gamma~_2`,
`E_3` or a finite-index subgroup by invoking the hypothesis
"`H^2(Gamma, V) = 0` for every unitary `V`". This covers DGLT/BLSW Theorem 1.1(F)
(Frobenius stability) and BDL Conjecture 1.8 (operator-HS-stability). Every such
argument dies at that hypothesis. Passing to finite index does not help, nor
does passing to a central quotient `E_n`.

**What this does not say.** It does not refute Frobenius or operator-HS-stability
of `Gamma~_2`. It also does not decide the weaker property `(T_2)`, which asks
for vanishing only for `V` without invariant vectors. That would need the
bound `dim H^2(Delta; C) < dim H^2(Delta'; C)`, for example
`dim H^2(Sp_4(Z); Q) = 1` when `Delta = Gamma~_2`, and no verbatim citation is
imported for it here. A genus-two stability proof must therefore use a
refined input, such as vanishing of only the specific defect classes, or a
non-cohomological mechanism.
