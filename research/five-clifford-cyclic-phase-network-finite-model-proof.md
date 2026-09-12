---
rg: 2
id: five-clifford-cyclic-phase-network-finite-model-proof
kind: route
title: Build the diagonal-spin representation and compute every cyclic leakage row
target: five-clifford-diagonal-spin-absorbs-the-full-orbit-lock
requires:
  - extraspecial-fusion-filter-local-normalizer-globalization
---

# Build the diagonal-spin representation and compute every cyclic leakage row

## 1. Two copies of the spin packet

The group

\[
 K=\langle J,X_1,\ldots,X_5\mid
 J^2=X_i^2=1,\ J\ {\rm central},\
 [X_i,X_j]_g=J\ (i\ne j),\
 X_1X_2X_3X_4X_5=J\rangle                              \tag{1}
\]

is extraspecial of order \(32\). This can be checked directly, without
the deleted odd-orbit predecessor: eliminate \(X_5\) using the volume
relation and put every word in the form
\(J^aX_1^{b_1}\cdots X_4^{b_4}\), giving at most 32 elements.
For the usual Pauli reflections \(X,Y,Z\), the assignments
\[
X_1=X\otimes I,\quad X_2=Z\otimes I,\quad
X_3=Y\otimes X,\quad X_4=Y\otimes Z,\quad
X_5=Y\otimes Y,\quad J=-I
\]
satisfy all the relations: the five reflections anticommute pairwise
and their ordered product is \(-I\). The 32 signed monomials in the
first four are distinct Pauli matrices. The commutator form on their
four binary exponents is nonsingular, so the center and commutator
subgroup both equal \(\langle J\rangle\). The actual extraspecial
prerequisite therefore applies. The group has a unique irreducible representation

\[
 \rho:K\longrightarrow U({\mathbf C}^4),\qquad
 \rho(J)=-I_4.                                          \tag{2}
\]

Cyclic permutation of the five \(X_i\) is an automorphism of order five.
Choose an implementing unitary \(h\) and rescale it so that

\[
 h^5=I,\qquad h\rho(X_i)h^{-1}=\rho(X_{i+1}).           \tag{3}
\]

Indices are read modulo five.

Consider the presentation obtained by adding an order-five letter \(g\)
with this cyclic conjugation action, and two involutions \(U,V\) with

\[
 UkU^{-1}=X_1kX_1,\qquad
 VkV^{-1}=X_2kX_2
 \quad(k\in K).                                         \tag{4}
\]

It is enough to impose (4) on the finite generating set of \(K\).

Define on \({\cal H}={\mathbf C}^4\otimes{\mathbf C}^4\)

\[
 \begin{aligned}
 \pi(k)&=\rho(k)\otimes I,\\
 \pi(g)&=h\otimes h,\\
 \pi(U)&=\rho(X_1)\otimes\rho(X_1),\\
 \pi(V)&=\rho(X_2)\otimes\rho(X_2).
 \end{aligned}                                          \tag{5}
\]

The first line and (2) give \(\pi(J)=-I_{\cal H}\). Equation (3) verifies
the actor relations. Both last operators in (5) are involutions. Since the
second tensor factor commutes with \(\pi(K)\), conjugation by them on
\(\pi(K)\) is exactly conjugation by the required first-factor Clifford
letter. Thus (4) also holds.

## 2. Every orbit commutator vanishes

Put

\[
 U_i=g^iUg^{-i},\qquad V_i=g^iVg^{-i}.                  \tag{6}
\]

Equations (3) and (5) give

\[
 \begin{aligned}
 \pi(U_i)&=\rho(X_{i+1})\otimes\rho(X_{i+1}),\\
 \pi(V_i)&=\rho(X_{i+2})\otimes\rho(X_{i+2}).
 \end{aligned}                                          \tag{7}
\]

For any two indices \(a,b\), the Clifford commutator is \(1\) when
\(a=b\), and is \(-I_4\) when \(a\ne b\). Therefore

\[
 [\rho(X_a)\otimes\rho(X_a),
   \rho(X_b)\otimes\rho(X_b)]_g=I_{\cal H}              \tag{8}
\]

in both cases: an off-diagonal pair contributes one minus sign in each
tensor factor. Every \(U_i\) and \(V_j\) is one of the five operators in
(8). Consequently

\[
 [U_i,U_j]_g=[V_i,V_j]_g=[U_i,V_j]_g=1                 \tag{9}
\]

holds in the representation for all \(i,j\).

This is stronger than cancelling one forbidden transverse cell. It
simultaneously satisfies the complete orbit rectangle, all within-family
commutation rows, one common order-five covariance, and the marked
five-Clifford table.

## 3. The odd orbit norm is scalar, not the payload

In cyclic order, the volume relation gives

\[
 \prod_{i=0}^4\pi(U_i)
 =\rho(X_1X_2X_3X_4X_5)\otimes
  \rho(X_1X_2X_3X_4X_5)
 =\rho(J)\otimes\rho(J)
 =I_{\cal H}.                                           \tag{10}
\]

For the \(V_i\), the cyclic product starts at \(X_2\). Moving \(X_1\) from
the end back to the front crosses four Clifford letters, so it contributes
\(J^4=1\). The same calculation therefore gives

\[
 \prod_{i=0}^4\pi(V_i)=I_{\cal H}.                      \tag{11}
\]

The phase-corrected orbit words

\[
 E_U=J\prod_{i=0}^4U_i,\qquad
 E_V=J\prod_{i=0}^4V_i                                 \tag{12}
\]

satisfy

\[
 \pi(E_U)=\pi(E_V)=-I_{\cal H}.                         \tag{13}
\]

They commute, but (13) is not either second-factor gauge
\(\rho(X_1)\) or \(\rho(X_2)\). Thus adding the extracted-gauge
commutator relation does not remove the model.

The displayed tensor calculation makes the phase cancellation equivariant:
the same order-five actor shifts both the controller packet and its
diagonal spin gauge. Equations (7)--(13) directly verify the complete
cyclic phase network, without an additional rectangular-network theorem.

## 4. Every actor-character cut leaks

The Schur decomposition relative to the first copy of \(K\) identifies the
actor multiplicity in (5) with the second copy of \(h\). Let
\(q_\lambda\) be a nonzero spectral projection of that \(h\). We prove

\[
 (1-q_\lambda)\rho(X_1)q_\lambda\ne0.                   \tag{14}
\]

Suppose instead that the left side vanished. Since \(\rho(X_1)\) is
self-adjoint, the opposite off-diagonal corner also vanishes, so
\(q_\lambda\) reduces \(\rho(X_1)\). It commutes with \(h\) by definition
and therefore reduces every conjugate

\[
 \rho(X_i)=h^{i-1}\rho(X_1)h^{-(i-1)}.                  \tag{15}
\]

Moreover \(h\) is the scalar \(\lambda\) on
\(q_\lambda{\mathbf C}^4\), so all five restrictions in (15) are equal:

\[
 q_\lambda\rho(X_i)q_\lambda
 =q_\lambda\rho(X_1)q_\lambda.                          \tag{16}
\]

But two different Clifford letters anticommute on the \(J=-1\) spin
space. Substituting (16) says on the nonzero range of \(q_\lambda\) that
the square of one reflection is the negative of itself. This is
\(I=-I\), a contradiction. Hence (14) holds.

There are only finitely many nonzero spectral cuts, so in this fixed model

\[
 c_0=\min_{q_\lambda\ne0}
 \frac{\|(1-q_\lambda)\rho(X_1)q_\lambda\|_2}
      {\|q_\lambda\|_2}>0.                              \tag{17}
\]

The same conclusion holds for every \(\rho(X_i)\) by cyclic symmetry.

All group relators in (1), (3), (4), and (9), as well as the orbit-gauge
commutator following (13), have exactly zero defect in this
sixteen-dimensional model. Equation (17) therefore rules out any estimate

\[
 \|(1-q_\lambda)Aq_\lambda\|_2^2
 \leq C\,E_{\rm orbit}                                  \tag{18}
\]

whose right side uses only those ordinary relator defects, for any finite
constant \(C\).

## 5. The exact remaining two-context gate

The model does not refute every nonnormal Hecke compiler. It refutes the
specific attempt to pay the unwanted multiplicity commutator by completing
the five-Clifford orbit with more central commutator phases. Even the full
orbit rectangle is absorbed diagonally.

To combine an actor-character corner with the gauge-free controlled-Pauli
overlap identity, one now needs an additional word whose defect is positive
in the model (5) and quantitatively dominates (17). Such a word cannot be:

1. a packet or volume relation;
2. an order-five actor relation;
3. a within-orbit or cross-orbit commutator;
4. a commutator of the two phase-corrected orbit norms.

It must see a nonmultiplicative return through the character cut, or an
equivalent noncentral fusion datum. The complementary result
extraspecial-fusion-filter-local-normalizer-globalization
shows that forcing every payload to reduce the cut instead returns to a
finite matrix-factor globalization. The complementary compressed-PVM
obstruction shows that one plain nonreducing transported PVM loses total
corner mass.

Thus the smallest two-context, one-forbidden-pair orbit model is completely
classified at the phase level: exact completeness is easy, but finite
Hilbert--Schmidt soundness requires a new ordinary word charging (17).
No such word is produced here, so the main nonhyperlinearity claim remains
open.
