---
rg: 2
id: universal-torsion-defect-rings-have-exact-mf-radical
kind: claim
title: The MF radical of the elementary groups over every universal torsion-defect ring is exactly the finitary special linear group over the cyclic ring from rank four
distinct_from:
  finite-additive-order-one-sided-defects-are-mf-invisible: that is the inclusion of the relative elementary subgroup in the MF radical for every ring whose defect has finite additive order; this is equality for the universal rings, obtained by exhibiting the quotient as residually finite, together with the exact identification of the quotient and of the sign it retains.
  order-two-universal-ring-has-finitary-symbol-sequence: that is the ring structure and symbol sequence of the order-two universal ring alone; this computes the MF radical for every modulus and finds that from modulus three on the symbol kernel exceeds the radical by a central sign.
  binary-jacobson-mf-radical-dichotomy: that is the two-valued alternative for the binary Jacobson group in rank five; this is an exact value, for the characteristic-zero universal rings, at every rank from four.
  finite-modulus-finitary-kernels-have-uniform-support-rank: that exhibits a normal locally finite subgroup and a support bound in the universal ring's rank-four group as input to a transport argument; this is the radical computation, which consumes only the torsion theorem and the residually finite quotient.
  integral-jacobson-mf-radical-is-all-or-nothing: that is the integral ring, where the radical is one of two values and undecided; this is the torsion quotient, where the radical is decided.
artifacts:
  - research/artifacts/jacobson-exact-torsion-radical-and-integral-dichotomy-2026-09-09.md
---

**ESTABLISHED.**  Let `J = Z<s,t | ts = 1>`, `e = 1 - st`,
`I = JeJ = M_fin(N_0, Z)`, `S = Z[z,z^-1]`, and for `m >= 2`

```text
A_m = J / mI = Z<s,t | ts = 1, m(1 - st) = 0>,      I_m = A_m e A_m = M_fin(N_0, Z/m),
```

the universal unital ring with a one-sided inverse whose defect is
killed by `m`; it has characteristic zero and `A_m/I_m = S`.  For every
`m >= 2` and `n >= 4`,

```text
Rad_MF(EL_n(A_m)) = Res_fin(EL_n(A_m)) = E_n(A_m, I_m) = SL_fin(Z/m),   (ER1)
```

and the largest MF quotient, which is residually finite, is

```text
EL_n(A_m) / E_n(A_m, I_m)  =  EL_n(S)  (m = 2),     T_n  (m > 2),       (ER2)
```

with `T_n = EL_n(J)/SL_fin(Z)` the central `C_2`-extension of `EL_n(S)`
of `integral-jacobson-symbol-kernel-is-finitary-general-linear`.  More
precisely the symbol kernel of `EL_n(A_m)` is
`{g in GL_fin(Z/m) : det g = +-1}`, so for `m > 2`

```text
symbol kernel / Rad_MF  =  C_2,                                         (ER3)
```

the class of `eta = diag(1 - 2e, 1)`, which survives in a finite
quotient; for `m = 2` the two determinants coincide and the symbol
kernel is the radical.  The identifications `(ER2)`, `(ER3)` and the
finite residual hold already for `n >= 2`; only the radical equality
uses the rank-four torsion theorem, and this claim does not lower that
threshold.

**Two caveats for any general radical statement.**

* If `N <= Rad_MF(G)` then `Rad_MF(G) = q^-1(Rad_MF(G/N))`, and for
  countable groups residually MF is MF (diagonal block sums), so
  `Rad_MF(G) = N` iff `G/N` is MF.  `G/N` need not be the elementary
  group of `R/ReR`: `(ER2)` shows an extra central `C_2` for every
  `m > 2`.
* Equality `Rad_MF(EL_n(R)) = E_n(R, ReR)` is not universal: in
  `R = J_(F_2) x L_(F_2)(1,2)` with the pair `(s,1), (t,1)`, the selected
  defect ideal is `J_(F_2) e J_(F_2) x 0`, but the radical contains the
  whole second factor `EL_n(L_(F_2)(1,2))`, which has no nontrivial MF
  image.  A general equality needs a hypothesis on the quotient, not
  only on the selected defect.

Derivation: `universal-torsion-defect-rings-have-exact-mf-radical-proof`.
