---
rg: 2
id: qutrit-multicoset-capacity-proof
kind: route
title: Fourier-filter the complete phase graph and count spin-block capacity
target: qutrit-two-to-one-multicoset-filter-is-half-kernel
requires:
  - qutrit-shortest-tk-word-graphs-are-diagonal-or-complete
  - thompson-27-cylinder-qutrit-cell-is-fd-invisible
  - qutrit-central-line-twist-is-impossible-in-jacobson-host
---

# Fourier-filter the complete phase graph and count spin-block capacity

## 1. Exact host-word coefficients

The three phase atoms are
\[
 e_a={1\over9}\sum_{j,l\in\mathbb F_3}
 \omega^{-j-al}J^jZ_1^l.
\]
Therefore
\[
\begin{aligned}
 e_2&={1\over9}\sum_{j,l}\omega^{-j-2l}J^jZ_1^l,\\
 R=e_0+e_1
 &={1\over9}\sum_{r,s}\omega^{-r}(1+\omega^{-s})J^rZ_1^s.
                                                               \tag{QMC7}
\end{aligned}
\]
For the generic active labeling, coordinates \(2\) and \(3\) have different
\(u_1\)-labels.  The raw root \(t=x_{23}(T)\) consequently has trivial
character-intersection subgroup and complete phase graph:
\[
 e_bte_a\ne0,\qquad \|e_bte_a\|_2^2={1\over81}
 \quad\hbox{for all }a,b.                               \tag{QMC8}
\]

Multiplying the two expressions in (QMC7) gives the promised exact
multi-word filter
\[
 A=e_2tR={1\over81}
 \sum_{j,l,r,s\in\mathbb F_3}
 \omega^{-j-2l-r}(1+\omega^{-s})
 J^jZ_1^l\,t\,J^rZ_1^s.                                \tag{QMC9}
\]
For its character blocks,
\[
 e_bAe_a=(e_be_2)t(Re_a)
 =\begin{cases}
   e_2te_a,&b=2,\ a=0,1,\\
   0,&\text{otherwise}.
  \end{cases}                                           \tag{QMC10}
\]
Equations (QMC8) and (QMC10) prove the exact support and norm table in the
claim.  The two surviving blocks are Hilbert-Schmidt orthogonal: by
traciality,
\[
 \tau\bigl((e_2te_0)^*(e_2te_1)\bigr)
 =\tau(e_0te_2te_1)
 =\tau(e_1e_0te_2t)=0.
\]
Thus \(\|A\|_2^2=2/81\).  The graph is genuinely the desired two-source,
one-target star.

## 2. Equal character multiplicities in every qutrit spin block

The order-\(3^5\) extraspecial qutrit packet has, for the nontrivial central
character \(J\mapsto\omega\), a unique irreducible representation of
dimension \(9\).  Hence the projection \(q\) in an arbitrary
finite-dimensional representation selects a direct sum of \(m\) copies of
this spin representation.

Inside one copy, \(Z_1\) has three eigenvalues.  The relation
\[
 X_1Z_1X_1^{-1}=JZ_1
\]
and the scalar action \(J=\omega I\) show that conjugation by \(X_1\)
cycles those eigenvalues.  Their multiplicities are equal.  Since their
sum is \(9\), each multiplicity is \(3\).  On \(m\) copies,
\[
 \dim(e_aH)=3m,\qquad\dim(RH)=6m.                        \tag{QMC11}
\]

## 3. The unavoidable singular-value kernel

Let \(B\) be any operator satisfying \(B=e_2BR\).  It maps \(RH\) into
\(e_2H\).  Equation (QMC11) gives
\[
 \operatorname{rank}(B|_{RH})\leq3m,\qquad
 \dim\ker(B|_{RH})\geq3m.                               \tag{QMC12}
\]
Thus at least half of the source singular values vanish.  This proof uses
only the two phase-typing equations; the number, length, or double-coset
location of the group words in \(B\) is irrelevant.

The same statement in the canonical finite trace follows from the polar
decomposition \(B=v|B|\).  Since
\[
 B=e_2B,\qquad B=BR,
\]
its support projections satisfy
\[
 vv^*\leq e_2,\qquad v^*v\leq R.
\]
Polar support projections have equal trace, so
\[
 \tau(v^*v)=\tau(vv^*)\leq\tau(e_2)={1\over9}.          \tag{QMC13}
\]
As \(\tau(R)=2/9\), the projection \(R-v^*v\) has trace at least \(1/9\).
Therefore
\[
 \|R-v^*v\|_2^2=\tau(R-v^*v)\geq{1\over9}.              \tag{QMC14}
\]
This proves both the half-source kernel and the quantitative \(1/3\)
Hilbert-Schmidt floor.

Finally suppose a residual factor is inserted.  If the expression remains
right typed, for example
\[
 B=e_2XR e_{\rm res}R,
\]
then \(B=e_2BR\) and the proof above is unchanged.  If the last \(R\) is
removed, then in general \(BR\ne B\); the initial support need not lie in
the two-phase carrier.  Such an expression may have different singular
geometry, but it is not yet a Hall arrow out of \(R\).  Any later covariance
which restores \(BR=B\) restores (QMC12)--(QMC14) at the same time.  This
is the exact finite-rank firewall asserted in the claim.
