---
rg: 2
id: compactness-closes-exact-actor-pauli-window
kind: route
title: Round the root pair and collide two finite-dimensional sites
target: kazhdan-stabilizer-collapses-shared-pauli-sign
requires:
  - shared-center-extraspecial-wreath-has-fd-invisible-spin-sector
  - property-t-does-not-kill-boolean-fiber-holonomy
---

# Round the root pair and collide two finite-dimensional sites

All Hilbert--Schmidt norms are normalized.

## 1. Kazhdan projection into the stabilizer commutant

Let
\[
 \mathcal C=\rho(\Gamma)'\cap M_D.
\]
The conjugation action
\[
 \operatorname{Ad}\rho:\Gamma\longrightarrow U(L^2(M_D))
\]
is a genuine unitary representation. Its invariant vectors are exactly
\(L^2(\mathcal C)\).

Let \(E_{\mathcal C}:M_D\to\mathcal C\) be the trace-preserving
conditional expectation, equivalently the Hilbert-space orthogonal
projection onto the invariant vectors. The Kazhdan inequality and (KPS3)
give
\[
 \|A-E_{\mathcal C}(A)\|_2\le\frac{\delta}{\kappa},
 \qquad
 \|B-E_{\mathcal C}(B)\|_2\le\frac{\delta}{\kappa}.       \tag{1}
\]

We use a standard finite-algebra polar completion. If \(U\) is unitary,
\(T=E_{\mathcal C}(U)\), and
\(\eta=\|U-T\|_2\), then there is a unitary
\(\widehat U\in\mathcal C\) with
\[
 \|U-\widehat U\|_2\le2\eta.                             \tag{2}
\]
Indeed \(T\) is a contraction. Complete its polar partial isometry to a
unitary \(\widehat U\in\mathcal C\). If \(s_j\in[0,1]\) are the singular
values of \(T\), then
\[
 \|T-\widehat U\|_2^2
 \le \operatorname{tr}_D(1-|T|^2)
 =1-\|T\|_2^2
 =\|U-T\|_2^2.                                          \tag{3}
\]
The last equality is Pythagoras for the orthogonal projection
\(E_{\mathcal C}\).

Apply (2) to \(A,B\). There are
\[
 \widehat A,\widehat B\in U(\mathcal C)
\]
such that
\[
 \|A-\widehat A\|_2,\ \|B-\widehat B\|_2
 \le\eta,\qquad
 \eta=\frac{2\delta}{\kappa}.                            \tag{4}
\]

## 2. The rounded pair is well defined at every site

For \(x=g\Gamma\in X\), define
\[
 \widehat A_x=\rho(g)\widehat A\rho(g)^*,\qquad
 \widehat B_x=\rho(g)\widehat B\rho(g)^*.                \tag{5}
\]
If \(g\Gamma=g'\Gamma\), then \(g'=g\gamma\) for some
\(\gamma\in\Gamma\). Since \(\widehat A,\widehat B\in\mathcal C\),
the right side of (5) does not change. Thus the pair is well defined on
\(X\), not merely on a choice of representatives. It is exactly
\(G\)-equivariant:
\[
 \rho(u)\widehat C_x\rho(u)^*=\widehat C_{ux}
 \quad(u\in G,\ C\in\{A,B\}).                            \tag{6}
\]

Replacing each entry of an additive commutator by an \(\eta\)-close
unitary changes its norm by at most \(4\eta\). Therefore (KPS4) and (4)
give
\[
 \|\widehat C\,\rho(r_\ell)\widehat D_0\rho(r_\ell)^*
   -\rho(r_\ell)\widehat D_0\rho(r_\ell)^*\widehat C\|_2
 \le\delta+4\eta
 =\delta+\frac{8\delta}{\kappa}.                         \tag{7}
\]

Every ordered pair of distinct sites belongs to one of the non-diagonal
orbits represented by
\((\Gamma,r_\ell\Gamma)\). Exact equivariance (6) transports (7) without
any word-length loss. Hence, for all distinct \(x,y\in X\) and all
\(C,D_0\in\{A,B\}\),
\[
 \|\widehat C_x\widehat D_{0,y}
   -\widehat D_{0,y}\widehat C_x\|_2
 \le c,\qquad
 c=\delta+\frac{8\delta}{\kappa}.                        \tag{8}
\]

This is the point at which finite double-coset rank and an exact actor are
both used. There are finitely many input rows, but they become a uniform
statement over every ordered pair.

## 3. Compactness turns a cross relation into the same-site relation

The set
\[
 U(D)\times U(D)
\]
is compact in the Hilbert--Schmidt topology. Since \(X\) is infinite, for
every \(\varepsilon>0\) there are distinct sites \(x,y\) with
\[
 \|\widehat A_x-\widehat A_y\|_2<\varepsilon,\qquad
 \|\widehat B_x-\widehat B_y\|_2<\varepsilon.             \tag{9}
\]
If the site-pair map has finite image, take two sites with identical image;
otherwise take two terms near one cluster point.

Use only the second inequality in (9) and the \(A,B\) instance of (8):
\[
\begin{aligned}
 \|\widehat A_x\widehat B_x-\widehat B_x\widehat A_x\|_2
 &\le
 \|\widehat A_x(\widehat B_x-\widehat B_y)\|_2\\
 &\quad+
 \|\widehat A_x\widehat B_y-\widehat B_y\widehat A_x\|_2\\
 &\quad+
 \|(\widehat B_y-\widehat B_x)\widehat A_x\|_2\\
 &\le 2\varepsilon+c.                                   \tag{10}
\end{aligned}
\]
The left side is independent of \(x\), by (5) and unitary invariance of
the norm. Letting \(\varepsilon\downarrow0\) gives
\[
 \|\widehat A\widehat B-\widehat B\widehat A\|_2
 \le\delta+\frac{8\delta}{\kappa}.                       \tag{11}
\]

Returning from the rounded pair to \(A,B\) costs at most another
\(4\eta=8\delta/\kappa\):
\[
 \|AB-BA\|_2
 \le\delta+\frac{16\delta}{\kappa}.                      \tag{12}
\]

## 4. Collapse of the shared sign

For arbitrary unitaries \(A,B\),
\[
 \|ABA^*B^*-I\|_2=\|AB-BA\|_2.                           \tag{13}
\]
Indeed right multiplication of the first difference by \(BA\) produces
\(AB-BA\).

Combining (KPS2), (12), and (13) yields
\[
\begin{aligned}
 \|J-I\|_2
 &\le\|J-ABA^*B^*\|_2+\|ABA^*B^*-I\|_2\\
 &\le2\delta+\frac{16\delta}{\kappa}.                    \tag{14}
\end{aligned}
\]
This is (KPS5).

If the shared-center presentation is evaluated with exact actor
representations \(\rho_n\) and all its displayed finite rows have defects
\(\delta_n\to0\), equation (14) gives
\[
 \|J_n-I\|_2\to0.
\]
No divisibility estimate, window size, or comparison between
\(\delta_n\) and \(D_n\) is needed.

## 5. Why arbitrary hyperlinear coordinates remain outside the theorem

In a general matrix almost-representation, the actor matrices satisfy each
fixed actor relator only asymptotically. Their ultraproduct is a genuine
representation, but its unitary group is no longer compact in the
Hilbert--Schmidt topology. Conversely, at one finite coordinate the site
conjugates are compact, but transporting a double-coset identity through a
dimension-dependent actor word incurs an uncontrolled proof-length error.

Property \((T)\) controls almost-invariant vectors for a genuine
conjugation representation and supplies Section 1. It does not turn an
arbitrary normalized-HS almost-representation of the actor into a genuine
coordinate representation. The exact-actor theorem therefore identifies
the remaining gate precisely: a successful nonhyperlinearity proof must
make the finite-coordinate double-coset propagation uniform, or
exactify the actor strongly enough to invoke (14). This is the same
approximate-image-collapse frontier isolated for the Kun--Thom compressor.
