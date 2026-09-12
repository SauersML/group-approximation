---
rg: 2
id: c2-regular-character-factor-provenance-counterexample
kind: route
title: Split the free C2 stabilizer character into trivial and sign factors
target: ergodic-irs-factor-components-need-not-be-stabilizer-characters
requires: []
---

Let `Gamma=C_2={e,s}` act on itself by left translation with normalized
counting measure. The action is transitive, hence ergodic, and free, so its
stabilizer IRS is the ergodic point mass `delta_({e})`. Its character is

```text
phi(e)=1,   phi(s)=0.                                  (IFP1)
```

This is the regular character. Its GNS algebra is

```text
L(C_2)=C e_+ direct_sum C e_-,
e_+=(1+lambda(s))/2,  e_-=(1-lambda(s))/2,              (IFP2)
```

and the regular trace assigns mass `1/2` to each summand. Hence the central
factor decomposition is

```text
phi=(1/2)chi_+ +(1/2)chi_-,
chi_+(s)=1,   chi_-(s)=-1.                             (IFP3)
```

The positive factor is the stabilizer character of `delta_Gamma`, but the
sign factor cannot be a stabilizer character: for every IRS `eta`,

```text
psi_eta(s)=eta({H:s in H}) in [0,1].                   (IFP4)
```

Thus an ergodic stabilizer law can have a nonfactorial character and a factor
summand outside the IRS-character image.

More generally, in the corner cut out by `q_-` for any central involution
`J`, one has `q_-pi(J)q_-=-q_-`. Direct-integral decomposition preserves
this operator equality, giving `(IFC3)` in every nonzero factor. This proves
the negative-sector assertion without any example-specific input.
