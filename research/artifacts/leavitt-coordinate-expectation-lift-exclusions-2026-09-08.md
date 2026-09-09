# Coordinate-expectation exclusions for the rounding problem

Date: 2026-09-08.

These are exclusions of proposed counterexamples to uniform tracial
conditional-expectation rounding. They do not prove rounding, disprove
rounding, or decide hyperlinearity of the Leavitt unit group. The issue is
whether an abstract ultraproduct expectation is induced by coordinate
maps at all, before asking whether those maps can be rounded.

Throughout, matrix traces and Hilbert--Schmidt norms are normalized, and
\(\omega\) is a free ultrafilter on the positive integers.

## 1. The initial-tensor relative commutant has no coordinate retraction

Put

\[
M_n=M_2^{\otimes n},\qquad
\mathcal M=\prod_\omega(M_n,\tau_n).
\]

For fixed \(k\), embed \(A_k=M_2^{\otimes k}\) in \(\mathcal M\) using
the first \(k\) tensor factors for \(n\geq k\). Let

\[
R=\left(\bigcup_k A_k\right)'',\qquad D=R'\cap\mathcal M.
\]

Here \(R\) is the hyperfinite \(\mathrm{II}_1\) factor. In particular,
the trace-preserving normal conditional expectation \(E_D\) exists.

**Proposition.** There are no linear maps \(T_n:M_n\to M_n\) satisfying
all of the following:

1. \(\sup_n\|T_n\|_{\infty\to\infty}<\infty\);
2. the formula \(T((x_n)_\omega)=(T_n(x_n))_\omega\) defines a map on
   the tracial ultraproduct;
3. \(T(\mathcal M)\subseteq D\) and \(T|_D=\mathrm{id}_D\).

Thus \(E_D\) has no such coordinate realization, even without imposing
positivity, trace preservation, or self-adjointness on the coordinates.

**Proof.** Write \(C=\sup_n\|T_n\|_{\infty\to\infty}\). For
\(u\in\mathcal U(A_k)\), let \(u^{(n)}\) denote its initial-tensor
realization. The range condition implies

\[
\lim_\omega\sup_{\|x\|_\infty\leq1}
       \|[T_n(x),u^{(n)}]\|_2=0.                 \tag{1}
\]

Otherwise, coordinate witnesses give a bounded sequence whose image
under \(T\) fails to commute with \(u\). This contradicts
\(T(\mathcal M)\subseteq D\).

For each fixed \(k\), finite operator-norm nets in
\(\mathcal U(A_k)\), together with

\[
\|[T_n(x),u^{(n)}-v^{(n)}]\|_2
 \leq 2C\|u-v\|_\infty,
\]

upgrade (1) to

\[
\varepsilon_{n,k}:=
\sup_{\substack{\|x\|_\infty\leq1\\u\in\mathcal U(A_k)}}
\|[T_n(x),u^{(n)}]\|_2
\longrightarrow_\omega0.                    \tag{2}
\]

This is asserted only for \(n\geq k\).

Here is an explicit diagonal choice. Define the decreasing
\(\omega\)-large sets

\[
F_k=\{n\geq2k:\ \max_{1\leq j\leq k}\varepsilon_{n,j}
                           \leq1/k\}.
\]

For \(n\in F_1\), set

\[
k_n=\max\{1\leq k\leq\lfloor n/2\rfloor:n\in F_k\};
\]

off \(F_1\), set \(k_n=1\). Then \(k_n\to_\omega\infty\),
\(1\leq k_n\leq n\), and
\(\varepsilon_{n,k_n}\to_\omega0\). The latter follows from
\(\varepsilon_{n,k_n}\leq1/k_n\) on \(F_1\).

Let \(X_n,Z_n\) be Pauli \(X,Z\) unitaries on tensor position
\(k_n\), acting as the identity elsewhere. They commute with every
fixed initial tensor algebra eventually along \(\omega\). Consequently

\[
X=(X_n)_\omega,\ Z=(Z_n)_\omega\in D.
\]

Commutation extends from the initial tensor union to \(R\) by
\(L^2\)-density and the uniform operator bounds on \(X_n,Z_n\).
The retraction condition gives
\(\|T_n(X_n)-X_n\|_2\to_\omega0\). But
\(Z_n\in\mathcal U(A_{k_n}^{(n)})\), so (2) gives
\(\|[T_n(X_n),Z_n]\|_2\to_\omega0\). This contradicts

\[
2=\|[X_n,Z_n]\|_2
 \leq2\|X_n-T_n(X_n)\|_2
        +\|[T_n(X_n),Z_n]\|_2
 \longrightarrow_\omega0.\qquad\square       \tag{3}
\]

### 1.1. Why this is not a near-idempotent-channel counterexample

Suppose \(P_n:M_{d_n}\to M_{d_n}\) are bistochastic UCP maps and

\[
\|P_n^2-P_n\|_{\infty\to2}\longrightarrow_\omega0.
\]

The coordinate maps contract operator norm and \(L^2\), hence induce a
bistochastic UCP idempotent \(P\) on \(\prod_\omega M_{d_n}\).
It is normal: positivity and trace preservation show that it preserves
suprema of bounded increasing positive nets, using the faithful normal
trace. If \(a=P(a)\), Schwarz and trace preservation give

\[
P(a^*a)-a^*a\geq0,\qquad
\tau(P(a^*a)-a^*a)=0,
\]

and similarly for \(aa^*\). Thus every fixed element belongs to the
multiplicative domain of \(P\). Its range is consequently a von Neumann
subalgebra, and \(P\) is its trace-preserving conditional expectation.

The proposition says that this range cannot be the particular \(D\)
above. Starting from that abstract relative commutant therefore cannot
produce a counterexample by simply lifting its expectation to coordinate
UCP maps. In particular, an abstract expectation and a coordinate
expectation are distinct requirements even before finite-algebra
rounding is considered.

### 1.2. The native Kazhdan heat has a different feature

For the native corner subgroup \(L\), the existing
[heat calculation, equation (8b)](leavitt-heat-kernel-inclusion-and-cp-reversal-obstruction-2026-09-08.md)
does provide a coordinate realization of the full relative-commutant
expectation: along canonical microstates, if
\(t_n\to\infty\) and \(\epsilon_nt_n\to0\), the heat maps induce

\[
E_{\pi(L)'\cap\mathcal M}.
\]

The energy estimate fixes every bounded sequence in that commutant,
without a separate rate assumption on its generator commutators.
The diagonal Pauli obstruction above therefore does not apply to this
native expectation. The unresolved step remains replacing those
coordinate heat maps by exact finite-dimensional expectations.

For comparison, the quantum-expander relative commutants in
[Farah--Jekel--Pi, Lemmas 4.8 and 4.9](https://arxiv.org/html/2310.06197#S4.SS4)
have explicit coordinate spectral-gap bounds to specified coordinate
algebras. Those particular constructions already identify the limiting
commutants with ultraproducts of coordinate algebras; they do not supply
a failure of conditional-expectation rounding.

## 2. An outer involution cannot have a coordinate expectation

**Lemma (same-dimension coordinate endomorphisms are inner).** Let
\(\mathcal M=\prod_\omega(M_{d_n},\tau_{d_n})\). Suppose unital,
complex-linear, adjoint-preserving maps
\(\phi_n:M_{d_n}\to M_{d_n}\), with
\(\sup_n\|\phi_n\|_{\infty\to\infty}\leq C<\infty\), induce a
well-defined unital \(*\)-endomorphism \(\Phi\) of \(\mathcal M\).
Then there are \(u_n\in\mathcal U(M_{d_n})\) such that

\[
\lim_\omega\sup_{\|x\|\leq1}
 \|\phi_n(x)-u_nxu_n^*\|_{2,d_n}=0.                 \tag{4}
\]

Thus \(\Phi=\operatorname{Ad}((u_n)_\omega)\); surjectivity was not
assumed. Well-definedness on the tracial quotient is a hypothesis,
not a consequence asserted for arbitrary operator-bounded maps.

The external input is the dimension-independent, full-unit-ball
stability theorem of
[Alekseev--Thom, Theorem 3.5](https://arxiv.org/html/2606.07369v1),
in the finite-matrix formulation of
[De Bondt--Thom, Theorem 5.4](https://arxiv.org/html/2607.19556v1).
A contraction-valued, approximately unital \(*\)-homomorphism on the
entire source unit ball can be approximated by a genuine matrix
\(*\)-homomorphism after enlarging the target by a vanishing relative
dimension. We verify the contraction and full-ball hypotheses below.
The reduced-product classification in their Theorem 5.5 is related;
here we use only the quantitative matrix theorem, with limits along
\(\omega\), and no additional set-theoretic assumptions.

**Proof.** Set

\[
\delta_n=\sup_{\|x\|,\|y\|\leq1}
 \|\phi_n(xy)-\phi_n(x)\phi_n(y)\|_{2,d_n}.
\]

Then \(\delta_n\to_\omega0\): otherwise choose contraction witnesses
on an \(\omega\)-large set to contradict multiplicativity of \(\Phi\).
For each unitary \(v\),

\[
\|\phi_n(v)^*\phi_n(v)-1\|_{2,d_n}\leq\delta_n.
\]

Completing its polar factor to a unitary gives \(w\) with
\(\|\phi_n(v)-w\|_{2,d_n}\leq\delta_n\), since
\(|s-1|\leq|s^2-1|\) for \(s\geq0\).
Every matrix contraction is the average of two unitaries: if
\(x=v|x|\) is a polar decomposition with unitary completion \(v\),
use \(v(|x|\pm i\sqrt{1-|x|^2})\). Linearity therefore puts
\(\phi_n(x)\) within \(\delta_n\) of the operator unit ball.

For \(\|x\|\leq1\), let \(h_n(x)\) be obtained by clipping the
singular values of \(\phi_n(x)\) at one. This is the Hilbert--Schmidt
metric projection onto the operator unit ball, so

\[
\sup_{\|x\|\leq1}\|h_n(x)-\phi_n(x)\|_{2,d_n}
 \leq\delta_n.                                     \tag{5}
\]

Extend radially outside that ball:
\(h_n(x)=\|x\|h_n(x/\|x\|)\) when \(\|x\|>1\).
Then \(h_n(1)=1\), and it preserves adjoints. Its additivity defect
for contractions \(x,y\), including when \(x+y\) is outside the
unit ball, is at most \(4\delta_n\); its scalar-homogeneity defect
for \(|\lambda|\leq1\) is at most \(2\delta_n\). Also

\[
\sup_{\|x\|,\|y\|\leq1}
 \|h_n(xy)-h_n(x)h_n(y)\|_{2,d_n}
 \leq(C+3)\delta_n.                                \tag{6}
\]

Indeed, insert \(\phi_n(xy)\) and \(\phi_n(x)\phi_n(y)\), then use
\(\|\phi_n(y)\|\leq C\), \(\|h_n(x)\|\leq1\), and (5).
Thus these maps satisfy the actual stability hypotheses uniformly
over the whole source unit ball.

The matrix theorem supplies numbers \(\epsilon_n\to_\omega0\),
integers \(d_n\leq m_n\leq(1+\epsilon_n)d_n\), isometries
\(W_n:\mathbb C^{d_n}\to\mathbb C^{m_n}\), and homomorphisms

\[
\psi_n(x)=v_n^*(x^{\oplus r_n}\oplus0)v_n
\]

such that

\[
\sup_{\|x\|\leq1}
 \|\psi_n(x)W_n-W_nh_n(x)\|_{2,m_n}\leq\epsilon_n.  \tag{7}
\]

Here rectangular norms use the ambient normalization \(m_n^{-1}\).
These are ultrafilter limits: to obtain the varying tolerances, take
decreasing defect thresholds for target errors \(1/k\), and on each
coordinate use the largest admissible \(k\leq n\). Every fixed
threshold holds on an \(\omega\)-large set. No ordinary convergence
or special diagonal property of \(\omega\) is required.

For \(\omega\)-almost every \(n\), \(m_n<2d_n\), so \(r_n\leq1\).
Putting \(x=1\) in (7) excludes \(r_n=0\), whose error would be
\(\sqrt{d_n/m_n}>1/\sqrt2\). Hence \(r_n=1\).
The projections \(p_n=W_nW_n^*\) and \(q_n=\psi_n(1)\) have equal
rank \(d_n\), and (7) gives

\[
\|p_n-q_n\|_{2,m_n}
 =\sqrt2\|(1-q_n)p_n\|_{2,m_n}
 \leq\sqrt2\epsilon_n.
\]

Equal-rank projections admit an aligning unitary \(z_n\) with
\(z_nq_nz_n^*=p_n\) and
\(\|z_n-1\|_{2,m_n}\leq\sqrt2\|p_n-q_n\|_{2,m_n}\).
This follows by rotating their principal-angle two-planes; the squared
cost is at most twice the squared projection distance. Consequently

\[
\theta_n(x)=W_n^*z_n\psi_n(x)z_n^*W_n
\]

is a unital \(*\)-automorphism of \(M_{d_n}\), and telescoping (7)
gives

\[
\sup_{\|x\|\leq1}\|\theta_n(x)-h_n(x)\|_{2,d_n}
 \leq5\epsilon_n\sqrt{m_n/d_n}.
\]

Since matrix automorphisms are inner, (5) proves (4). Choices on the
remaining \(\omega\)-small coordinates do not matter. \(\square\)

**Corollary (the reflection test).** Suppose \(\alpha\) is an outer
involutive automorphism of \(\mathcal M\). Its conditional expectation
onto the fixed algebra,

\[
E=\tfrac12(\mathrm{id}+\alpha),
\]

cannot be induced by coordinate bistochastic UCP maps \(P_n\).
Otherwise \(\phi_n=2P_n-\mathrm{id}\) are unital, linear,
adjoint-preserving maps with operator norms at most three, inducing
\(\alpha\). They also have \(L^2\)-operator norms at most three,
so their action on the tracial quotient is well-defined. The lemma
would make \(\alpha\) inner, a contradiction.

This is conditional on having an outer involution; it does not assert
its existence on every matrix ultraproduct. Nor does it cover arbitrary
expectations: for a general \(E\), the reflection \(2E-\mathrm{id}\)
need not be multiplicative. The full-unit-ball multiplicativity used
above comes from that reflection being an automorphism, and does not
follow from small idempotence defect alone.

**Positive special case.** If coordinate near-idempotent bistochastic
UCP maps \(P_n\) induce an expectation \(E\) and
\(\alpha=2E-\mathrm{id}\) is multiplicative, then they do round to
exact expectations in the original dimensions. Indeed,
\(\alpha^2=\mathrm{id}\), so the lemma gives \(\alpha=\operatorname{Ad}U\).
The matrix ultraproduct is a factor; hence \(U^2\) is scalar, and
rescaling \(U\) makes it a self-adjoint unitary \(V\). Lift the
projection \((1+V)/2\) to coordinate projections \(p_n\), and set
\(V_n=2p_n-1\). Then

\[
E_n(x)=\tfrac12(x+V_nxV_n)
      =p_nxp_n+(1-p_n)x(1-p_n)
\]

are exact trace-preserving conditional expectations. They induce
\(E\), so choosing contraction witnesses gives
\(\|P_n-E_n\|_{\infty\to2}\to_\omega0\). This handles expectations
that pinch into at most two full matrix blocks. The extra reflection
hypothesis is not available for the native heat in general: even
the exact diagonal expectation on \(M_3\) fails it, because its
reflection sends each off-diagonal matrix unit to its negative, and
therefore fails multiplicativity on \(e_{12}e_{23}=e_{13}\).

## 3. The remaining Kazhdan commutant question

The exact scope is also visible in
[Alekseev--Thom, Open Problem 6.2](https://arxiv.org/html/2608.05362v1#S6):
for a Kazhdan-group homomorphism into a matrix tracial ultraproduct,
part (a) asks whether its relative commutant has the form
\(\prod_\omega A_n\) for finite-dimensional coordinate subalgebras
after replacing dimensions \(d_n\) by \(m_n\) with
\(m_n/d_n\to_\omega1\). Part (b) asks for coordinate generator lifts
whose exact centralizers are those \(A_n\). The native heat-rounding
route would give such an internal-algebra conclusion; neither
exclusion above supplies that rounding step or an admissible
counterexample to it.
