---
rg: 2
id: multiplicity-conditioning-cannot-repair-the-moved-root-target-deficit
kind: claim
title: A Lin occurrence PVM cannot repair the moved-root target deficit from the multiplicity algebra
artifacts:
  - research/multiplicity-block-polar-deficit-and-raw-full-c-condition-proof.md
distinct_from:
  moved-root-dft-router-loses-quarter-and-collides-two-to-one: that computes the finite-head quarter loss and collision before source occurrences are attached; this proves that arbitrary orthogonal occurrence conditioning in the Morita multiplicity algebra cannot recover the lost rank.
  reed-muller-pauli-stability-is-morita-neutral-to-nonlinear-occurrence-data: that separates a stable Pauli factor from arbitrary multiplicity data; this gives the exact block-polar deficit for the moved-root qutrit router.
  occurrence-conditioned-balanced-polar-discards-the-hall-excess: that starts with a source larger than the target and shows how a balanced polar can discard the excess; this starts with every routed occurrence branch smaller than the target and proves that no multiplicity conditioning can make it full.
  lin-independent-set-synchbcs-has-uniform-nonaffine-onehot-mass: that forces at least three positive source occurrences; this proves that every such positive block separately needs a full raw qutrit return.
---

**EXACT OCCURRENCE-BLOCK DEFICIT.**

Let \(R=Ee_2\) be the qutrit target projection, so

\[
 \tau(R)=\frac1{18}.                                    \tag{MOP1}
\]

For each sign row let \(T_i\) be any final-\(e_2\) compression of one of
the collected moved-root branches from the three-line selector. Its polar
range \(Q_i\) satisfies

\[
 Q_i\leq R,\qquad
 \tau(Q_i)\leq
 \begin{cases}
  5/192,&\text{in the all-plus row},\\
  3/128,&\text{in every other surviving row}.
 \end{cases}                                            \tag{MOP2}
\]

Now let \((A,\tau_A)\) be an arbitrary tracial occurrence algebra and let
\(p_1,\ldots,p_m\in A\) be a PVM. Form the most general tensor-separated
occurrence-conditioned collected row

\[
 T=\sum_{i=1}^m T_i\otimes p_i.                          \tag{MOP3}
\]

If \(V\) is its polar partial isometry, orthogonality of the \(p_i\)
gives

\[
 VV^*=\sum_i Q_i\otimes p_i.                             \tag{MOP4}
\]

Consequently

\[
 \begin{aligned}
 \tau(VV^*)&\leq\frac5{192},\\
 \big\|R\otimes1-VV^*\big\|_2^2
 &=\frac1{18}-\sum_i\tau(Q_i)\tau_A(p_i)
 \geq\frac{17}{576}.                                    \tag{MOP5}
 \end{aligned}
\]

If every active branch is a non-all-plus row, the stronger lower bound is
\(37/1152\).

Thus keeping the Lin occurrence projection in the Morita multiplicity
algebra does not turn the collected moved-root triangle into a
trace-\(1/18\) range. It makes the router block diagonal; it cannot enlarge
the common finite-head ceiling. The exact relation

\[
 VV^*=R\otimes1                                         \tag{MOP6}
\]

already fails in the honest tracial model by the dimension-independent
amount in (MOP5).

The collected head has the explicit finite absorber

\[
 \langle N,C,H,C_1,W\rangle,\qquad |\langle N,C,H,C_1,W\rangle|=1152.
                                                               \tag{MOP7}
\]

Tensoring its regular representation with any occurrence representation
realizes every tensor-separated collected row. Hence this coupling is
Morita-neutral: it neither compiles the source algebra into group words nor
creates a new matrix obstruction.

The next algebraic condition is now exact. For every source atom
\(p_i\) of positive trace, a surviving raw/full-\(C\) coefficient \(B_i\)
must satisfy

\[
 \operatorname{supp}\!\left(
  (RB_i e_{a_i})(RB_i e_{a_i})^*
 \right)=R,\qquad
 \tau\!\left(\operatorname{supp}|RB_i e_{a_i}|\right)=\frac1{18},
                                                               \tag{MOP8}
\]

with a dimension-independent lower bound on its least nonzero singular
value. At least one \(B_i\) must retain an uncollected \(S\) or \(T\)
constituent; every coefficient in the collected \(ST\)-root group is
bounded by (MOP2). The mixed relations must also identify the initial
support in (MOP8) with the already named Lin occurrence, rather than define
a new tautological source projection.

No such raw range-authentication relation is proved here. The
nonhyperlinear-group root remains open.

DERIVATION
multiplicity-block-polar-deficit-and-raw-full-c-condition-proof
