---
rg: 2
id: multiplicity-block-polar-deficit-and-raw-full-c-condition-proof
kind: route
title: Diagonalize the occurrence PVM and compute the surviving head rank
target: multiplicity-conditioning-cannot-repair-the-moved-root-target-deficit
requires:
  - moved-root-dft-router-loses-quarter-and-collides-two-to-one
  - reed-muller-pauli-stability-is-morita-neutral-to-nonlinear-occurrence-data
  - occurrence-conditioned-balanced-polar-discards-the-hall-excess
  - lin-independent-set-synchbcs-has-uniform-nonaffine-onehot-mass
---

# Diagonalize the occurrence PVM and compute the surviving head rank

## 1. A general block-polar lemma

Let \((M,\tau_M)\) and \((A,\tau_A)\) be finite tracial von Neumann
algebras. Let \(p_1,\ldots,p_m\) be orthogonal projections in \(A\) with

\[
 \sum_{i=1}^m p_i=1.                                    \tag{1}
\]

For arbitrary \(t_i\in M\), put

\[
 T=\sum_i t_i\otimes p_i.                               \tag{2}
\]

Because \(p_ip_j=0\) for \(i\ne j\),

\[
 T^*T=\sum_i t_i^*t_i\otimes p_i,\qquad
 TT^*=\sum_i t_it_i^*\otimes p_i.                       \tag{3}
\]

Write \(t_i=v_i|t_i|\) for the polar decomposition, with zero on the
kernel. Functional calculus in the direct sum (3) gives

\[
 T=V|T|,\qquad V=\sum_i v_i\otimes p_i.                 \tag{4}
\]

If \(q_i=v_iv_i^*=\operatorname{supp}(t_it_i^*)\), then

\[
 VV^*=\sum_i q_i\otimes p_i,\qquad
 \tau(VV^*)=\sum_i\tau_M(q_i)\tau_A(p_i).                \tag{5}
\]

This is the key point. Orthogonal occurrence labels remove cross terms;
they do not make the head ranges add without paying the trace of their
multiplicity blocks.

Now fix a head target projection \(R\in M\) and suppose \(q_i\leq R\)
for every \(i\). Then \(VV^*\leq R\otimes1\), and hence

\[
 \begin{aligned}
 \|R\otimes1-VV^*\|_2^2
 &=\tau\big((R\otimes1-VV^*)^2\big)\\
 &=\tau_M(R)-\sum_i\tau_M(q_i)\tau_A(p_i).               \tag{6}
 \end{aligned}
\]

In particular, if \(\tau_M(q_i)\leq r<\tau_M(R)\), then

\[
 \|R\otimes1-VV^*\|_2^2\geq\tau_M(R)-r.                 \tag{7}
\]

There is also a blockwise exact form. If \(VV^*=R\otimes1\), multiply
this equality by \(1\otimes p_i\). For every nonzero \(p_i\),

\[
 (R-q_i)\otimes p_i=0,
\]

so

\[
 q_i=R.                                                  \tag{8}
\]

Thus a full conditional target requires every positive occurrence branch
to be head-full. It is not enough that the joins of the different head
ranges fill \(R\).

## 2. Insert the collected moved-root bounds

For the corrected moved-root triangle, let

\[
 R=Ee_2,\qquad \tau_M(R)=\frac1{18}.                    \tag{9}
\]

The route moved-root-dft-router-quarter-loss-proof constructs the
collected \(ST\)-root modes \(D_1,D_2\), forms the correctly ordered row,
and proves that after the final \(e_2\) cut the polar range trace is at
most

\[
 r_+=\frac5{192}                                        \tag{10}
\]

in the all-plus sign row and at most

\[
 r_o=\frac3{128}                                        \tag{11}
\]

in every other surviving sign row. The first number is larger:

\[
 \frac5{192}=\frac{30}{1152}>
 \frac{27}{1152}=\frac3{128}.                           \tag{12}
\]

Let an arbitrary occurrence PVM choose, on each \(p_i\), any one of these
sign rows and any of the two collected source branches. After target
compression call the resulting head operator \(t_i\). Equations
(10)--(12) give

\[
 q_i=\operatorname{supp}(t_it_i^*)\leq R,\qquad
 \tau_M(q_i)\leq\frac5{192}.                            \tag{13}
\]

Apply (7):

\[
 \begin{aligned}
 \|R\otimes1-VV^*\|_2^2
 &\geq\frac1{18}-\frac5{192}\\
 &=\frac{32-15}{576}
 =\frac{17}{576}.                                       \tag{14}
 \end{aligned}
\]

If all branches use a non-all-plus sign row, then

\[
 \|R\otimes1-VV^*\|_2^2
 \geq\frac1{18}-\frac3{128}
 =\frac{64-27}{1152}
 =\frac{37}{1152}.                                      \tag{15}
\]

These bounds do not depend on the number of outcomes, their trace
weights, the dimension of the occurrence algebra, or whether that algebra
is Connes embeddable.

## 3. The Lin occurrence cannot hide the deficit

The Lin independent-set SynchBCS supplies, in every perfect trace, a
one-hot question with at least three positive occurrence projections.
Let those positive projections be among the \(p_i\) in (1).

If a proposed exact range-authentication row asserted

\[
 VV^*=R\otimes1,                                        \tag{16}
\]

then (8) would require \(q_i=R\) on each of those positive blocks. But
(9)--(13) give

\[
 \tau_M(q_i)\leq\frac5{192}<\frac1{18}=\tau_M(R),        \tag{17}
\]

a contradiction. In fact (14) shows that the proposed relation has a
uniform positive defect even before the nonaffine cross-context relations
of the source are used.

One might instead require only range containment,

\[
 VV^*\leq R\otimes1.                                    \tag{18}
\]

That relation is already true and carries no occurrence authentication:
every smaller block range satisfies it. The gap is precisely between
containment (18) and fullness (16).

This also distinguishes the present obstruction from the balanced-polar
construction. A target compression of the original three-line source,
whose trace is \(5/72\) or \(1/16\), may discard source mass and produce a
balanced trace-\(1/18\) polar. The collected moved-root triangle has
already reduced each occurrence branch below \(1/18\); multiplicity
conditioning cannot recreate the discarded head dimension.

## 4. The explicit collected absorber

The moved-root computation identifies

\[
 N\cong C_2^2,\qquad
 F_{\rm head}=\langle N,C,H,C_1,W\rangle,\qquad
 |F_{\rm head}|=1152.                                   \tag{19}
\]

All collected \(D_s\), sign projections, qutrit projections, and their
polar ranges lie in the finite-dimensional group algebra of
\(F_{\rm head}\). Its regular representation realizes the quarter kernel
and the two-to-one collision exactly.

For any representation of the occurrence algebra \(A\), tensoring that
regular head representation with it realizes (2). If \(A\) has a
finite-dimensional representation, the tensor product is an explicit
finite-dimensional model of the entire tensor-separated coupling.
Conversely, merely tensoring with this head does not turn the projections
of \(A\) into words of a finitely presented group. This is the same
Morita-neutral boundary as for the stable Pauli factor, now with the exact
moved-root rank loss included.

## 5. The necessary raw/full-\(C\) condition

Suppose a new construction uses head coefficients \(B_i\) and wants a
conditional row

\[
 Y=\sum_i (RB_i e_{a_i})\otimes p_i                     \tag{20}
\]

whose polar is full on \(R\otimes1\). Applying (8) to (20) shows that for
every \(i\) with \(p_i\ne0\),

\[
 \operatorname{supp}\!\left(
  (RB_i e_{a_i})(RB_i e_{a_i})^*
 \right)=R.                                             \tag{21}
\]

Trace equality for a polar then forces

\[
 \tau_M\!\left(\operatorname{supp}|RB_i e_{a_i}|\right)
 =\tau_M(R)=\frac1{18}.                                 \tag{22}
\]

Equations (21) and (22) are the exact, blockwise Hall condition. A
quantitative compiler additionally needs a constant \(c>0\), independent
of the matrix model, such that on the initial support \(P_i\),

\[
 (RB_i e_{a_i})^*(RB_i e_{a_i})\geq c^2P_i.             \tag{23}
\]

Without (23), exact full range has no stable polar modulus.

No \(B_i\) in the collected \(ST\)-root algebra can satisfy (21), by
(13). Therefore at least one raw \(S\) or \(T\) constituent must remain
uncollected in the same full-\(C=\langle k,h\rangle\) Fourier coefficient.
Finally, the initial projection \(P_i\) in (23) must be identified by
mixed relations with the already named Lin projection \(p_i\). Defining
\(p_i\) after the fact as \(P_i\) would yield the tautological finite-head
source ruled out by the balanced-polar absorber.

This isolates the next calculation without claiming it: find one
uncollected full-\(C\) root-triangle coefficient satisfying
(21)--(23), and prove that its initial support is the source occurrence.
Until that is done, the nonhyperlinear-group root remains open.
