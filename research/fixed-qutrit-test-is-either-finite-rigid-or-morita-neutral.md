---
rg: 2
id: fixed-qutrit-test-is-either-finite-rigid-or-morita-neutral
kind: claim
title: A fixed qutrit Pauli test is either a finite rigid packet or Morita-neutral occurrence data
artifacts:
  - research/fixed-qutrit-constant-template-and-block-polar-proof.md
distinct_from:
  quantum-low-degree-is-a-non-equality-pauli-synchronizer: that records the positive growing-field self-test; this separates the fixed-field theorem bound from direct exactification of a fixed finite Pauli packet.
  fixed-field-plane-point-loses-uniform-low-degree-robustness: that uses the low-degree code distance to rule out a scalable fixed-field family; this adds the exact fixed-presentation alternative and the occurrence-block polar obstruction.
  first-uncancelled-g2-mixed-carrier-has-no-hall-deficit: that computes one literal raw S/T carrier; this proves why qutrit exactification cannot repair it by diagonal occurrence conditioning.
---

**ESTABLISHED SCOPE DICHOTOMY.**

Natarajan--Vidick Theorem 3.2 formally permits the prime field
(mathbb F_3): its one-element basis is self-dual.  But its stated
robustness has the form

[
 delta=operatorname{poly}!left(
   operatorname{poly}(3)operatorname{poly}(arepsilon)
   +operatorname{poly}(d/3)ight),qquad d=hm.          	ag{FQT1}
]

Thus that theorem does not give a vanishing fixed-(q=3) modulus as
(arepsilon	o0), and it does not give a scalable constant-template
family.  If the number (k) of tested qutrit coordinates is fixed instead,
the relevant generalized Pauli group is the finite group
(mathsf P_{3,k}) of order (3^{2k+1}).  Standard finite-group
Hilbert--Schmidt exactification already rounds that fixed packet; the
low-degree test is unnecessary for this constant-size job.

Fixing the packet does not fix the occurrence algebra.  In the central
character (J=omega),

[
 p_omega C^*(mathsf P_{3,k})p_omegacong M_{3^k}(mathbb C),
 qquad
 p_omega(C^*(mathsf P_{3,k})otimes_{max}A)p_omega
 cong M_{3^k}otimes_{max}A.                           	ag{FQT2}
]

Consequently an occurrence projection that commutes with the recovered
Pauli factor is exactly (1otimes p) and remains arbitrary.  Putting it
inside the Pauli factor instead makes it finite-dimensional with a fixed
rational matrix rank.  The qutrit test supplies no third, nonreducing
placement.  Such a placement has to be imposed by an explicit mixed
occurrence row.

There is an exact block obstruction.  For an occurrence PVM
((p_i)subset A) and head coefficients (b_iin M_{3^k}), put

[
 B=sum_i b_iotimes p_i .
]

Then polar decomposition is blockwise:

[
 operatorname{supp}|B|
   =sum_ioperatorname{supp}|b_i|otimes p_i,qquad
 operatorname{supp}|B^*|
   =sum_ioperatorname{supp}|b_i^*|otimes p_i.         	ag{FQT3}
]

Hence diagonal occurrence conditioning cannot add the ranges of different
head branches.  If every branch range lies below a target (R) and has
normalized head trace at most (r<operatorname{tr}(R)), then

[
 left|Rotimes1-operatorname{supp}|B^*|ight|_2^2
 ge operatorname{tr}(R)-r.                            	ag{FQT4}
]

For the collected moved-root qutrit target,
(operatorname{tr}(R)=1/18) and (rle5/192), so the exact squared
defect is at least

[
 rac1{18}-rac5{192}=rac{17}{576}.                 	ag{FQT5}
]

On the non-all-plus rows the bound is
(1/18-3/128=37/1152).  For the first uncollected two-letter raw
(S/T) carrier the source ranks are only (43/1152) and
(42/1152), both below the target rank (64/1152), before any
occurrence conditioning.

Therefore fixed (q=3) does remove the binary objection to a three-point
affine line, but it does not authenticate the positive nonaffine Lin
projection.  A surviving coefficient must simultaneously:

1. retain a raw positive and a raw negative Leavitt letter in one
   full-(C) Fourier coefficient;
2. have a full trace-(1/18) target and a uniform singular floor; and
3. contain an off-diagonal occurrence operator coupling different Lin
   blocks, rather than a sum (sum_i b_iotimes p_i).

No such bounded mixed row is supplied by Q-LOWDEG or by the audited
one- and two-letter qutrit carriers.  The nonhyperlinear-group root remains
open.

DERIVATION
fixed-qutrit-constant-template-and-block-polar-proof
