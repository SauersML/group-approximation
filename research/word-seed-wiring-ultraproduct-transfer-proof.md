---
rg: 2
id: word-seed-wiring-ultraproduct-transfer-proof
kind: route
title: Pull marked matrix models back through a seed word map
target: word-level-seed-wirings-preserve-marked-matricial-approximability
requires:
  - opposite-sign-compressions-are-spectral-routing
---

# Pull marked matrix models back through a seed word map

## 1. Marked presentations and word wiring

Write the two finite presentations as

$$
\Gamma_C
 =\langle X,J_C\mid R_C\rangle,
\qquad
\Gamma_S
 =\langle Y,J_S\mid R_S\rangle,                        \tag{1}
$$

where the involution and centrality relations for the marked elements are
included among the relators.

A universal word-level seed wiring chooses, for each \(x\in X\), a word
\(w_x(Y,J_S)\), sends \(J_C\) to the literal word \(J_S\), and has the
property that every compiled relator becomes an identity in
\(\Gamma_S\).  Equivalently, it induces a marked homomorphism

$$
\Phi:\Gamma_C\longrightarrow\Gamma_S,
\qquad
x\longmapsto w_x,
\qquad
J_C\longmapsto J_S.                                    \tag{2}
$$

The direction in (2) is important.  Substituting seed observables for
compiled observables is contravariant on the universal groups.

## 2. The ultraproduct argument

Let

$$
\mathcal U=\prod_{n\to\mathcal W}
 \bigl(U(d_n),\|\cdot\|_{2,d_n}\bigr)                   \tag{3}
$$

be a tracial metric ultraproduct of matrix unitary groups, and suppose

$$
\pi_S:\Gamma_S\longrightarrow\mathcal U,
\qquad
\pi_S(J_S)=-1.                                         \tag{4}
$$

Then

$$
\pi_C:=\pi_S\circ\Phi:\Gamma_C\longrightarrow\mathcal U \tag{5}
$$

is a homomorphism and

$$
\pi_C(J_C)
 =\pi_S(\Phi(J_C))
 =\pi_S(J_S)
 =-1.                                                   \tag{6}
$$

Thus marked matricial approximability transfers from the seed to the
compiled presentation.  Notice that neither \(\Phi\) nor \(\pi_S\) must
be injective; the conclusion needed here is only that the distinguished
central sign remains nontrivial in a matrix ultraproduct.

For solution groups of binary LCS games, a sequence of normalized
Hilbert--Schmidt matrix models with \(J=-I\) is precisely the marked
approximation relevant to value-one finite-dimensional strategies.  Hence
a seed which has such approximants but no finite-dimensional exact model
cannot acquire a constant marked gap through (2).

## 3. A finite defect bound

The preceding argument has a direct quantitative version.  Choose the word
lift \(\widehat\Phi\) from the free group on \(X\cup\{J_C\}\) to the free
group on \(Y\cup\{J_S\}\).  For each \(r\in R_C\), the word
\(\widehat\Phi(r)\) lies in the normal closure of \(R_S\).  Choose once and
for all an expression

$$
\widehat\Phi(r)
 =\prod_{k=1}^{N_r}
   u_{r,k}\,s_{r,k}^{\sigma_{r,k}}\,u_{r,k}^{-1},       \tag{7}
$$

where \(s_{r,k}\in R_S\), \(\sigma_{r,k}\in\{+1,-1\}\), and the
\(u_{r,k}\)'s are seed words.  Put

$$
N:=\max_{r\in R_C}N_r.                                  \tag{8}
$$

This is finite because both presentations and the chosen decompositions
are finite.

Let \(Y^{(d)}\) be any tuple of \(d\)-dimensional unitaries satisfying

$$
\max_{s\in R_S}
 \|s(Y^{(d)})-I\|_{2,d}\leq\eta.                        \tag{9}
$$

Evaluate the compiled generators by

$$
x^{(d)}:=w_x(Y^{(d)}),
\qquad
J_C^{(d)}:=J_S^{(d)}.                                  \tag{10}
$$

Normalized Hilbert--Schmidt norm is invariant under multiplication by a
unitary and under unitary conjugation.  Also,

$$
\|AB-I\|_2
 \leq\|A-I\|_2+\|B-I\|_2.                              \tag{11}
$$

Applying (11) repeatedly to (7), and using
\(\|s^{-1}-I\|_2=\|s-I\|_2\), gives

$$
\|r(X^{(d)},J_C^{(d)})-I\|_{2,d}
 \leq N_r\eta
 \leq N\eta                                             \tag{12}
$$

for every \(r\in R_C\).

The same calculation includes the compiled involution and context
commutation relators.  The evaluated words in (10) are exact unitaries;
any reflection or commutation property required by the compiled
presentation holds to the error bounded in (12), and becomes exact in the
metric ultraproduct.

## 4. Application to complete binary seed routing

The two-gate result
[opposite-sign-compression-spectral-proof](opposite-sign-compression-spectral-proof.md)
shows that a complete pair of projection gates for the opposite TV signs
reduces to

$$
L=sZ,                                                   \tag{13}
$$

where \(Z=p_+-p_-\) is one seed reflection.  Relation (13) is a group-word
equality.  If every other compiled variable is likewise assigned a fixed
seed word and the resulting equations hold in the universal seed group,
then these assignments define exactly the homomorphism (2).  Sections 2
and 3 show that every marked matrix approximation of the seed pulls back
to one of the compiled presentation.

Thus a universal binary routing cannot amplify the distinction

$$
\text{finite-dimensional supremum }1
\quad\text{but no finite-dimensional maximizer}
$$

into a constant gap.  To escape, a proposed strategy must use properties
of one selected seed trace which are not consequences of the seed group
relations, or use incomplete relation-dependent corners which do not
define a universal word substitution.  In either case, the construction
must state those additional constraints and prove that finite-dimensional
near-models cannot realize them.  The fixed seed alone supplies no such
decoder.
