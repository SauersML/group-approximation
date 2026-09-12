# Native heat stays at distance one from entanglement-breaking channels

2026-09-08. Pure finite-dimensional inequalities and an ultraproduct
argument. This is an exclusion of a channel approximation strategy,
not a determination of hyperlinearity of H.

Let P_n be the native L-heat maps of a full canonical H-microstate
sequence, at admissible times. Write EB_d for the bistochastic
entanglement-breaking channels on M_d. Then

\[
\boxed{\inf_{T\in\mathrm{EB}_{d_n}}
       \|P_n-T\|_{\infty\to2}\longrightarrow1.}       \tag{1}
\]

The scalar expectation is in EB_d and always gives the upper bound
one. Thus (1) gives the exact limiting distance to this class.
In particular, replacing the native heat by a measure-and-prepare
channel cannot establish the required expectation rounding. Exact
expectations onto noncommutative algebras remain available to the
rounding problem; this result does not rule them out.

## 1. A finite matrix-algebra test

Use normalized trace throughout. Let p be a projection in M_d, and
let a copy of M_k, k>=2, sit unitally in p M_d p. Put q=1-p and
choose a Weyl unitary basis V_0=p,V_1,...,V_(k^2-1) for this copy,
orthonormal for its normalized trace. Define actual unitaries in M_d
by U_j=V_j+q, for j>=1.

For every bistochastic entanglement-breaking T:M_d->M_d,

\[
\boxed{\max_{j\geq1}\|T(U_j)-U_j\|_2
       \geq\frac{k}{k+1}\tau(p).}                  \tag{2}
\]

We use the measure-and-prepare characterization of entanglement
breaking, in the Heisenberg convention:

\[
T(x)=\sum_a\phi_a(x)F_a,\qquad
F_a\geq0,\quad\sum_aF_a=1,
\quad\sum_a\tau(F_a)\phi_a=\tau,                  \tag{3}
\]

where the phi_a are states. This characterization is established in
[Horodecki--Shor--Ruskai, General Entanglement Breaking Channels](https://arxiv.org/abs/quant-ph/0302031).
The last two identities in (3) express unitality and trace
preservation. Discard terms with zero F_a, and set

\[
w_a=\tau(F_a),\qquad
\psi_a(x)=\tau(F_ax)/w_a.
\]

The psi_a are states, sum w_a=1, and both state averages, of phi_a
and of psi_a, equal tau.

For any state omega on M_d, restriction to the copy of M_k and
Parseval's identity for its Weyl basis give

\[
\sum_{j\geq1}|\omega(U_j)|^2
 \leq (k-1)\omega(p)+(k^2-1)\omega(q)
 =k-1+k(k-1)\omega(q).                            \tag{4}
\]

Indeed, if omega(p)>0, its normalized restriction has a density
matrix of ordinary trace one. The sum of squares of all its Weyl
coefficients is k times the purity, at most k; deleting the identity
coefficient leaves at most k-1. The vector of omega(U_j) is the
convex combination, with weights omega(p),omega(q), of that vector
and the all-ones vector. Convexity of squared Euclidean norm proves
(4), including either zero-weight case.

From (3), weighted Cauchy--Schwarz over a and j, and (4),

\[
\begin{aligned}
\operatorname{Re}\sum_{j\geq1}\tau(U_j^*T(U_j))
 &=\operatorname{Re}\sum_{a,j\geq1}
       w_a\phi_a(U_j)\overline{\psi_a(U_j)}\\
 &\leq k-1+k(k-1)\tau(q).                         \tag{5}
\end{aligned}
\]

If the maximum in (2) is epsilon, each real correlation on the left
is at least 1-epsilon, by Hilbert--Schmidt Cauchy--Schwarz and
\(\|U_j\|_2=1\). Consequently

\[
(k^2-1)(1-\varepsilon)
 \leq k-1+k(k-1)\tau(q),
\]

which is exactly (2).

More generally, for any map P and
\(\alpha=\max_{j\geq1}\|P(U_j)-U_j\|_2\), (2) implies

\[
\boxed{\|P-T\|_{\infty\to2}
       \geq\frac{k}{k+1}\tau(p)-\alpha.}          \tag{6}
\]

This quantitative test is uniform in the multiplicity of the
M_k copy, the ambient dimension, and the number of terms in (3).

It also proves that an exact trace-preserving matrix-algebra
expectation is entanglement breaking precisely when its range is
abelian. A noncommutative simple block would contradict (2) on its
fixed corner Weyl unitaries. For an abelian algebra with minimal
projections p_i, the formula
`E(x)=sum_i tau(p_i x)/tau(p_i) p_i` has form (3).

## 2. The native fixed algebra supplies every fixed matrix size

Use the native commuting subgroups L and K in H: L acts on the
first three Leavitt coordinates and K is the full unit group on the
fourth coordinate. The established identifications give K isomorphic
to H. It is infinite ICC, so its canonical von Neumann algebra is a
II_1 factor.

For any tracial ultraproduct of a full canonical H-microstate
sequence, let pi denote the canonical embedding. The native heat
identification gives

\[
(P_n)_\omega=E_D,\qquad
D=\pi(L)'\cap\prod_\omega M_{d_n}.               \tag{7}
\]

See the [full heat-commutant proof](leavitt-heat-kernel-inclusion-and-cp-reversal-obstruction-2026-09-08.md).
Since L and K commute, D contains the unital II_1 factor generated
by pi(K). Thus D contains a unital copy of M_k for every fixed k.

We only need the usual fixed-size matrix-unit lifting fact: a
unital M_k in a tracial matrix ultraproduct has representatives that
are exact matrix units in corners p_n M_(d_n) p_n, with
\(\tau(p_n)\to_\omega1\). One obtains these by rounding the
finitely many diagonal projections, making them orthogonal, using
polar decompositions of the off-diagonal lifts, and trimming their
ranks to the common minimum. Their limiting traces are all 1/k,
so the discarded normalized rank tends to zero. This is lifting of
one fixed finite-dimensional algebra, not extraction or rounding of
the full D.

Take the exact corner Weyl unitaries V_(j,n) for these lifts, and
put U_(j,n)=V_(j,n)+1-p_n. They represent the unitaries of the
chosen M_k in D, and (7) therefore gives

\[
\max_{j\geq1}\|P_n(U_{j,n})-U_{j,n}\|_2
       \longrightarrow_\omega0.                  \tag{8}
\]

Equations (6)--(8) show that every sequence T_n in EB_(d_n)
satisfies

\[
\lim_\omega\|P_n-T_n\|_{\infty\to2}
       \geq\frac{k}{k+1}
\]

for every fixed k, hence has lower limit at least one. The same
argument applies after taking any subsequence and choosing any
nonprincipal ultrafilter on it. Selecting T_n within 1/n of the
infimum proves the ordinary lower limit in (1).

For the upper bound, let E_sc(x)=tau(x)1. Since P_n is bistochastic
and L2-contracting,

\[
\|(P_n-E_{\rm sc})(x)\|_2
 =\|P_n(x-\tau(x)1)\|_2
 \leq\sqrt{\|x\|_2^2-|\tau(x)|^2}\leq1
\]

for every contraction x. This proves (1).

The statement concerns the native subgroup heat. It does not assert
that global H-heat has a noncommutative fixed algebra, and is
compatible with the conditional scalar-commutant selection argument.
