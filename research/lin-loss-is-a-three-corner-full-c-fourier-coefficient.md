---
rg: 2
id: lin-loss-is-a-three-corner-full-c-fourier-coefficient
kind: claim
title: Every Lin losing correlation is one three-corner full-C Fourier coefficient
artifacts:
  - research/three-corner-naimark-router-cross-gram-proof.md
distinct_from:
  fixed-qutrit-test-is-either-finite-rigid-or-morita-neutral: that proves diagonal occurrence conditioning is Morita-neutral; this constructs the exact off-diagonal coefficient which escapes that theorem.
  pauli-overlap-yields-positive-spectral-corner: that extracts a cross-Gram corner after a packet-overlap estimate; this identifies every decoded losing correlation literally as the norm of one bounded full-C coefficient.
  tailored-checks-to-common-marked-group-extensions: that reduces a general losing polynomial to a selected zero-compression condition; this gives an explicit common Naimark router whose zero compression is already a three-corner Fourier coefficient.
---

**ESTABLISHED ALGEBRAIC DECODER; ORDINARY-WORD RETURN STILL OPEN.**

Let (mathsf P_{3,k}) be a fixed generalized qutrit Pauli packet.  In
one central-character row let

[
 e_a,qquad ain K=mathbb F_3^k,
]

be the (D=3^k) joint (Z)-atoms, and fix one atom (e_r).
Let (c_x) be one unitary router for every context (x), commuting with
the central-character projection.  On the corner (e_r), define

[
 A_{x,a}=e_r c_xe_ac_x^*e_r.                            	ag{TCF1}
]

The (A_{x,a}) form a POVM.  For every ordered context/outcome pair put

[
 B_{y,b;x,a}=e_b c_y^*e_r c_xe_a.                       	ag{TCF2}
]

Then

[
 |B_{y,b;x,a}|_2^2
 =	au(A_{x,a}A_{y,b}).                                 	ag{TCF3}
]

Moreover (B_{y,b;x,a}) is a literal full-(C) bi-Fourier
coefficient:

[
 cB_{y,b;x,a}=chi_b(c)B_{y,b;x,a},qquad
 B_{y,b;x,a}c=chi_a(c)B_{y,b;x,a}
 quad(cin C).                                         	ag{TCF4}
]

Thus it is not in the diagonal algebra
(sum_i M_{m head}otimes p_i): its middle word
(c_y^*e_rc_x) is exactly the cross-context occurrence.

This decoder has exact perfect completeness.  Given any (D)-outcome PVM
((p_{x,a})) in a tracial algebra, on
(Aoverlineotimes M_D) take (e_a=1otimes E_a) and

[
 c_x=sum_{sin K}p_{x,s}otimeslambda(-s),             	ag{TCF5}
]

where (lambda) is the translation representation of (K).
Then

[
 e_r c_xe_ac_x^*e_r=p_{x,a-r}otimes e_r.               	ag{TCF6}
]

After relabelling (r=0), every perfect Lin strategy makes every losing
coefficient (TCF2) exactly zero.

Conversely, in every finite-dimensional packet/router representation,
the normalized trace on (e_r) and the POVMs (TCF1) give a legitimate
finite-dimensional strategy.  If the Lin game has gap
(Delta=1-omega_*(I)>0), some losing coefficient satisfies

[
 	au(B^*B)ge 	au(e_r)Delta.                          	ag{TCF7}
]

For

[
 R=1_{[Delta/2,1]}(B^*B),
]

one has the dimension-free bounds

[
 	au(R)gerac{Delta}{2-Delta}	au(e_r)
          gerac{Delta}{2}	au(e_r),qquad
 B^*BRgerac{Delta}{2}R.                             	ag{TCF8}
]

Hence the off-diagonal full-(C) coefficient has a fixed-density
initial corner and a uniform singular floor whenever finite-dimensional
Lin soundness fires.

Equations (TCF2)--(TCF8) close the occurrence-support identification
requested after the moved-root rank audit.  They do **not** yet make
(B=0) an ordinary group relator.  The remaining raw/full-(C) gate is
now exact: realize the same middle router (c_y^*e_rc_x) by a bounded
positive/negative Leavitt (S/T) return whose ordinary relators force
the zero compression without constraining the unused complement.  A raw
letter tensor factor which commutes through (TCF2) is only a removable
gauge and does not count.

The nonhyperlinear-group root remains open.

DERIVATION
three-corner-naimark-router-cross-gram-proof
