---
rg: 2
id: controlled-pauli-overlap-identity-and-gauge-lock-proof
kind: route
title: Compute the controlled-Pauli overlap identity and isolate the universal gauge lock
target: controlled-pauli-commutator-robustly-measures-projection-overlap
requires:
  - controlled-pauli-commutator-is-and-times-multiplicity-commutator
  - controlled-pauli-corner-has-clifford-groupification
  - source-specific-pointed-rank-router-face
---

# Compute the controlled-Pauli overlap identity and isolate the universal gauge lock

## 1. Controlled reflections for arbitrary projections

Let \(p,q\) be projections in a finite tracial von Neumann algebra
\((M,\tau)\). Use normalized matrix trace on \(M_2(\mathbf C)\) and put

\[
 X=\begin{pmatrix}0&1\\1&0\end{pmatrix},
 \qquad
 Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.               \tag{1}
\]

Define

\[
 U=I_2\otimes(1-p)+X\otimes p,
 \qquad
 V=I_2\otimes(1-q)+Z\otimes q.                          \tag{2}
\]

The two summands in each expression are supported on complementary source
projections. Hence \(U=U^*=U^{-1}\) and \(V=V^*=V^{-1}\), without assuming
that \(p\) and \(q\) commute.

Write \(A=X-I_2\) and \(B=Z-I_2\). Then

\[
 U=I+ A\otimes p,\qquad V=I+B\otimes q,
\]

so the additive commutator is

\[
 UV-VU=AB\otimes pq-BA\otimes qp.                       \tag{3}
\]

Direct multiplication gives

\[
 AB=\begin{pmatrix}0&-2\\0&2\end{pmatrix},
 \qquad
 BA=\begin{pmatrix}0&0\\-2&2\end{pmatrix}.              \tag{4}
\]

Substitution in (3) gives the block matrix

\[
 UV-VU=
 \begin{pmatrix}
  0&-2pq\\
  2qp&2(pq-qp)
 \end{pmatrix}.                                         \tag{5}
\]

## 2. Exact Hilbert--Schmidt identity

For a block matrix \(T=(T_{ij})\), normalized tensor trace gives

\[
 \|T\|_2^2=\frac12\sum_{i,j}\|T_{ij}\|_{2,\tau}^2.       \tag{6}
\]

Also \(\|pq\|_2=\|qp\|_2\), since

\[
 \|pq\|_2^2=\tau(qp q)=\tau(pq p)=\|qp\|_2^2.           \tag{7}
\]

Applying (6)--(7) to (5),

\[
 \begin{aligned}
 \|UV-VU\|_2^2
 &=\frac12\left(
    4\|pq\|_2^2+4\|qp\|_2^2+
    4\|pq-qp\|_2^2\right)\\
 &=4\|pq\|_2^2+2\|pq-qp\|_2^2.                         \tag{8}
 \end{aligned}
\]

Because \(U,V\) are involutions,

\[
 (UV-VU)VU=I-VUVU.                                      \tag{9}
\]

Right multiplication is isometric in normalized Hilbert--Schmidt norm.
Moreover \(VUVU=(UVUV)^{-1}\), and a unitary has the same distance from the
identity as its inverse. Therefore

\[
 \|UV-VU\|_2=\|UVUV-I\|_2.                              \tag{10}
\]

Equations (8)--(10) prove

\[
 \|[U,V]_g-I\|_2^2
 =4\|pq\|_2^2+2\|pq-qp\|_2^2.                          \tag{11}
\]

Both terms on the right are nonnegative. Thus zero group-commutator defect
is equivalent to \(pq=0\), which by adjunction also gives \(qp=0\), and

\[
 \|pq\|_2\leq\frac12\|[U,V]_g-I\|_2.                   \tag{12}
\]

When \(p\) and \(q\) commute, equation (11) reduces to the AND-sector phase
identity in
controlled-pauli-commutator-is-and-times-multiplicity-commutator.

## 3. Perturbing the controlled form

Let \(\widetilde U,\widetilde V\) be reflections with

\[
 \|\widetilde U-U\|_2\leq\alpha,\qquad
 \|\widetilde V-V\|_2\leq\beta.                         \tag{13}
\]

Telescope the four-letter commutator word. Each occurrence is multiplied
on the left and right by unitaries, so

\[
 \|[\widetilde U,\widetilde V]_g-[U,V]_g\|_2
 \leq2\alpha+2\beta.                                    \tag{14}
\]

If the actual group relator has defect

\[
 \|[\widetilde U,\widetilde V]_g-I\|_2\leq\eta,          \tag{15}
\]

then (12)--(15) give

\[
 \|pq\|_2\leq\frac12(\eta+2\alpha+2\beta).              \tag{16}
\]

No constant depends on \(\dim M\).

## 4. Conditional compilation of the independent-set rows

Suppose a marked group presentation provided, for every source projection
\(p_{i,v}\), gauge-free controlled-\(X\) and controlled-\(Z\) reflections
of the form (2), together with the decoded source reflection

\[
 s_{i,v}=1-2p_{i,v}.                                    \tag{17}
\]

For every losing pair \((i,u),(j,v)\), impose the ordinary group relation

\[
 [U_{i,u},V_{j,v}]_g=1.                                 \tag{18}
\]

Equation (11) then gives

\[
 p_{i,u}p_{j,v}=0.                                      \tag{19}
\]

In particular, the within-question losing pairs make the projections
\(\{p_{i,v}\}_v\) pairwise orthogonal. For orthogonal projections,

\[
 \prod_v(1-2p_{i,v})=1-2\sum_vp_{i,v}.                  \tag{20}
\]

Thus the group-word equation

\[
 \prod_v s_{i,v}=J                                      \tag{21}
\]

in the sector \(J=-1\) makes (20) equal to \(-1\), and hence

\[
 \sum_vp_{i,v}=1.                                       \tag{22}
\]

Equations (18)--(22) reconstruct exactly the PVM and forbidden-overlap
relations of the canonical independent-set SynchBCS. Equation (16) is the
local dimension-free estimate needed in an approximate decoder. Since the
source is finite, standard word telescoping and finite PVM rounding would
turn uniform controlled-form errors into a fixed source-game energy bound.

This is a conditional compiler, not yet a group presentation realizing its
hypothesis.

## 5. The multiplicity factor is the sole local obstruction

A finite Pauli packet can force covariance but not a literal controlled
operator. On a packet-isotypic carrier, Schur's lemma gives

\[
 \widetilde U=C_X(p)A,\qquad
 \widetilde V=C_Z(q)B,                                  \tag{23}
\]

where \(A,B\) act on the external multiplicity space. Even when the decoded
source projections commute, the group commutator in (23) contains the
factor \([A,B]\). On the joint active sector, an anticommuting pair \(A,B\)
can cancel the Pauli minus sign exactly. The resulting forbidden-overlap
model has zero relator defect, so finite-group stability has nothing to
round away.

This is why (11) does not contradict
finite-clifford-couplings-cannot-prune-a-forbidden-atom. The latter induces
an exact forbidden selector sector in every fixed finite overgroup. In that
sector the controlled expression is not gauge-free, and the extra
multiplicity commutator cancels the signal measured by (11).

There are only two possible ways to use the cell.

1. Force \(A\) and \(B\) to commute on every relevant source corner by
   genuinely shared cross-context relations.
2. Make \([A,B]\) independently observable and charge its deviation in the
   presentation defect before applying (16).

Ordinary packet covariance, a private Clifford cell, or sector-wide
literal selector projections do not achieve either. Odd tensor closure
also rules out a universal exact router which promises extensions for all
three allowed NAND atoms. Therefore the live form is the pointed one in
source-specific-pointed-rank-router-face: authenticate the controlled
rounding only on one distinguished non-tensor-closed source trace and on
the canonical matrix face used for soundness.

The analytic NAND decoder after such authentication is now exact and
dimension-free by (11)--(16). The pointed multiplicity lock itself remains
open, so no group-corner embedding and no nonhyperlinear group follows from
this route alone.
