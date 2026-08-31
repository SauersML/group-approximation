---
rg: 2
id: every-relative-ucp-window-lives-in-one-induced-representation
kind: claim
title: Every finite relative ucp window lives in one induced representation
requires:
  - finite-positive-definite-window-is-a-relative-corner-selector
distinct_from:
  induced-rounding-needs-rms-section-fillings: that constructs one canonical isometry from word evaluations and bounds its defect; this parametrizes all possible relative ucp windows by all core-intertwining isometries in the same finite induced space.
  right-core-cayley-average-gives-toeplitz-window: that gives a sufficient unitary-fibre gauge family; this proves the exact universal parametrization, including kernels outside that ansatz.
  tfd-finite-corner-collapse-and-rfd-firewall: that collapses a finite corner after it has been found; this identifies a single finite representation in which every such corner can be sought.
---

Let \(G\) be finite, \(B<G\), and let
\(\beta:B\to U(H_\beta)\), \(\dim H_\beta=d\).  Put

\[
\rho=\operatorname{Ind}_B^G(\beta),\qquad
\dim H_\rho=[G:B]d.                                    \tag{UIR1}
\]

The operator-valued positive-definite functions
\(F:G\to B(H_\beta)\) satisfying

\[
F(e)=1,\qquad F(b)=\beta(b)\quad(b\in B)                \tag{UIR2}
\]

are exactly the matrix coefficients

\[
F(g)=V^*\rho(g)V,                                      \tag{UIR3}
\]

where \(V:H_\beta\to H_\rho\) ranges over the isometries satisfying

\[
\rho(b)V=V\beta(b)\quad(b\in B).                        \tag{UIR4}
\]

Thus a single induced representation is a universal finite-dimensional
Stinespring host for every ucp map which is exact on the prescribed core.

For the nontrivial direction, let \(\Theta:C^*(G)\to B(H_\beta)\) be the
ucp map associated with \(F\), and take its minimal Stinespring triple

\[
\Theta(a)=V_0^*\sigma(a)V_0.
\]

The unitary values in (UIR2) put \(C^*(B)\) in the multiplicative domain,
so \(\sigma(b)V_0=V_0\beta(b)\).  Decompose

\[
\sigma=\bigoplus_{\pi\in\operatorname{Irr}(G)}
        \pi\otimes1_{\mathbb C^{m_\pi}}.                \tag{UIR5}
\]

The \(m_\pi\) components of \(V_0\) in the \(\pi\)-isotypic block are
elements of

\[
\operatorname{Hom}_B(H_\beta,H_\pi|_B).                \tag{UIR6}
\]

They are linearly independent.  Otherwise a nonzero vector in the
multiplicity space annihilates \(V_0H_\beta\); because \(G\) acts trivially
on that multiplicity coordinate, the corresponding copy of \(H_\pi\) is
orthogonal to the cyclic span \(\sigma(C^*(G))V_0H_\beta\), contradicting
minimality.  Hence

\[
m_\pi\leq
 \dim\operatorname{Hom}_B(H_\beta,H_\pi|_B).            \tag{UIR7}
\]

By Frobenius reciprocity, the right side is precisely the multiplicity of
\(\pi\) in \(\operatorname{Ind}_B^G\beta\).  Therefore \(\sigma\) embeds
\(G\)-equivariantly into \(\rho\).  Composing \(V_0\) with this embedding
gives (UIR3)--(UIR4).  The converse follows immediately by compression.

This turns the authenticated Iwahori selector into one finite Stiefel
problem.  For

\[
G=A_N,\qquad B=B_N,\qquad
\rho_{N,\beta}=\operatorname{Ind}_{B_N}^{A_N}\beta,
\]

define

\[
\Delta_{N,\beta}(X)=
 \inf_{\substack{V^*V=1\\
       \rho_{N,\beta}(b)V=V\beta(b)\ (b\in B_N)}}
 \|V^*\rho_{N,\beta}(x)V-X\|_{2,d}.                    \tag{UIR8}
\]

Then a positive-definite relative window with \(F(x)\) within \(\eta\) of
\(X\) exists if and only if

\[
\Delta_{N,\beta}(X)\leq\eta.                            \tag{UIR9}
\]

All core generators are exact automatically.  Consequently

\[
\Delta_{N_n,\beta_n}(X_n)\longrightarrow0              \tag{UIR10}
\]

is sufficient, via property \((T;FD)\), for the authenticated flexible
Iwahori lift.

The canonical identity-coset inclusion is not enough at every nondegenerate
level with \(x\notin B_N\).  Its \(x\)-coefficient is then zero, so its
distance from a unitary \(X\) is exactly one.  Equivalently,
'exact-core-multiplicative-domain-does-not-descend-to-normal-quotient'
shows that the conjugated \(t^N\)-row of the corresponding infinite induced
model has defect \(\sqrt2\).  The required isometry in (UIR8) must therefore
mix core cosets nontrivially.

The stabilizer constraint on its \(x\)-coefficient is

\[
V^*\rho(x)V\in
 \operatorname{Hom}_{B_N\cap xB_Nx^{-1}}
   (\beta^x,\beta),                                    \tag{UIR11}
\]

the \(BxB\) Hecke intertwiner space.  The approximate inversion row controls
part of this linear condition, while positivity and the two cubic rows must
place the coefficient in the compression range (UIR8).  Finite
restriction-ring data only decomposes \(\rho_{N,\beta}\); it does not select
the required Stiefel point.

No theorem currently proves (UIR10) for every regular Iwahori microstate.
The root remains open, but global RFD has been replaced by the explicit
finite induced-space selector (UIR8).
