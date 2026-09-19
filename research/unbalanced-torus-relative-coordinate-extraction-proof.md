---
rg: 2
id: unbalanced-torus-relative-coordinate-extraction-proof
kind: route
title: Kazhdan-round the relative denominator coordinate and apply the torus charge blockwise
target: unbalanced-torus-extracts-near-central-denominator-coordinate
requires:
  - exact-projective-codensity-has-a-uniform-trace-square-gap
  - two-torus-closures-detect-denominator-multiplicity
  - sl3-overlap-full-in-fd-ambient-images
---

By `sl3-overlap-full-in-fd-ambient-images`,

```text
sigma(C_+)=sigma(C),       sigma(C_+)'=sigma(C)'.       (NCP0)
```

Let `E` be the normalized-Hilbert--Schmidt orthogonal projection onto this
common commutant.  Property `(T)` of `C_+`, applied to the conjugation
representation on `M_d`, gives

```text
||W-E(W)||_2 <= kappa_+^(-1) sqrt(a_+(W)).              (NCP1)
```

The conditional expectation `E` is unital and completely positive, hence
`||E(W)||_op<=1`.  Take the polar decomposition of `E(W)` inside the finite
dimensional algebra `sigma(C)'` and extend its polar partial isometry to a
unitary `V in sigma(C)'`.  Orthogonality of `E` gives

```text
||W-E(W)||_2^2=1-||E(W)||_2^2.
```

Since `0<=|E(W)|<=1`,

```text
||E(W)-V||_2^2
 =tr((I-|E(W)|)^2)
 <=tr(I-|E(W)|^2)
 =1-||E(W)||_2^2.                                     (NCP2)
```

Consequently, with

```text
zeta=||W-V||_2,
```

we have the dimension-free estimate

```text
zeta <=2 kappa_+^(-1) sqrt(a_+(W)).                    (NCP3)
```

Finite-dimensional co-density for `C<A` says

```text
sigma(C)'=sigma(A)'.                                  (NCP4)
```

Thus `V` commutes with `sigma(h)` as well.  Put

```text
H_0=V sigma(h).
```

Then `||H-H_0||_2=zeta`.  More importantly, the computation of
`two-torus-closures-detect-denominator-multiplicity` is intrinsic, not tied
to a homogeneous tensor amplification.  Every lattice letter commutes with
`V`, and every denominator occurrence in the balanced words `D_12,D_23`
cancels its `V`-factor.  Therefore

```text
ev_(sigma|_C,H_0)(R_tor)=V^*.                          (NCP5)
```

If `ell` is the number of occurrences of `h^(plusOrMinus1)` in the fixed
word `R_tor`, word telescoping and `(NCP5)` give

```text
||V-I||_2 <= eta+ell zeta.                             (NCP6)
```

Let `K_1` be the constant in the ordinary-commutator form of the exact
projective co-density estimate.  Comparing first with the untwisted exact
actor `sigma(h)`, exactly as in
`unbalanced-torus-product-projective-transfer-proof`, yields

```text
||[U,H_0]-I||_2
 <=sqrt(K_1 q_C(U))+2||V-I||_2.                        (NCP7)
```

Also

```text
||[U,H]-[U,H_0]||_2<=2 zeta.                           (NCP8)
```

Since `1-|tr(Y)|^2<=||Y-I||_2^2` for a unitary `Y`, equations
`(NCP6)--(NCP8)` imply

```text
1-|tr([U,H])|^2
 <=(sqrt(K_1 q_C(U))+2 eta+2(ell+1)zeta)^2
 <=3K_1 q_C(U)+12 eta^2+12(ell+1)^2 zeta^2.            (NCP9)
```

Substitute `(NCP3)` into `(NCP9)`.  This proves `(NCD2)`, for example with

```text
K=3K_1,
C_0=max(12,48(ell+1)^2/kappa_+^2).                     (NCP10)
```

For the perturbative statement, fix word representatives over `S` for the
finitely many lattice letters occurring in `R_tor`, for `S_+`, and for
their conjugates `h^(-1)S_+h subset C`.  A product telescope bounds the
change in the torus-word evaluation by a fixed constant times `xi+delta`.
Similarly,

```text
| (1-|tr([U,X_s])|^2)
 -(1-|tr([U,sigma(s)])|^2) | <=4||X_s-sigma(s)||_2.    (NCP11)
```

For `c in S_+`, write `c'=h^(-1)c h`.  The evaluated fixed relation
`h c' h^(-1)c^(-1)=1`, followed by two more word telescopes comparing the
lattice packet with `sigma`, gives

```text
||[H sigma(h)^*,sigma(c)]||_2<=C_1(delta+xi),           (NCP12)
```

where `C_1` is independent of dimension, congruence level, and
multiplicity.  Thus `a_+(W)<=|S_+|C_1^2(delta+xi)^2`.
Insert this and `(NCP11)` in `(NCP9)`.  Since `R_tor` is one fixed
consequence of the ambient presentation, its defect is also `O(delta)`.
This proves `(NCD5)`.  If `(NCD6)` failed along an enemy, every term on the
right would tend to zero, contradicting its fixed target projective energy.
