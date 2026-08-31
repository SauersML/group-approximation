---
rg: 2
id: bass-serre-tree-localizes-the-missing-normal-rows
kind: route
title: Read the missing normal rows as returns in the Bass--Serre tree
target: index-three-frames-leave-deck-holonomy-uncontrolled
requires:
  - index-three-qsystem-rounding-is-relative-repair
  - exact-core-domain-does-not-descend-to-normal-quotient
  - optimized-core-full-pd-energy-is-intrinsic-selector
---

# The three-sheet systems are the two stars of one Bass--Serre edge

Let \(\mathcal T\) be the Bass--Serre tree of (IDH1). Its vertices are
\[
 A/V_+\ \sqcup\ A/V_-,
\]
its edges are \(A/B\), and every vertex has degree three. In the induced
model (IDH3), the Hilbert space is the square-summable field of
\(\mathbb C^d\)-fibers over \(A/B\), with the usual \(\beta\)-twist on
representatives. The identity edge carries \(J\mathbb C^d\).

The three edges incident to the base \(V_+\)-vertex are \(V_+/B\).
Their fibers form \(\mathcal K_+\), and left translation by \(V_+\)
preserves this three-edge star. The resulting representation is exactly
\(\operatorname{Ind}_B^{V_+}\beta\). The identical argument at the other
endpoint gives \(\mathcal K_-\). Distinct edges have orthogonal fibers, so
both spaces have dimension \(3d\). This proves (IDH4) and all local
three-coset identities without an estimate.

# A stabilizer relation need not vanish on translated fibers

Because \(t^N\in B\) and \(\beta(t)^N=1\), it acts trivially on the
identity fiber:
\[
 \rho(t^N)J=J.                                            \tag{1}
\]
For any \(g\in A\), the vector \(\rho(g)J\xi\) is supported on the edge
\(gB\). Thus
\[
 \rho(xt^Nx^{-1})J\xi
\]
is supported on \(xt^Nx^{-1}B\). The standard square-free matrices give
\[
 xt^Nx^{-1}=
 \begin{pmatrix}1&0\\-N&1\end{pmatrix},
\]
whereas \(B\) is the upper Iwahori subgroup. Hence this coset differs from
\(B\), and the two \(d\)-dimensional fibers are orthogonal. Therefore
\[
 \|(\rho(xt^Nx^{-1})-1)J\|_{\mathrm F}^2=2d,              \tag{2}
\]
which is (IDH6).

# Quotient descent is exactly deck-holonomy triviality

The range of the translates \(\rho(w)J\mathbb C^d\), \(w\in A\), is dense
in the induced representation. Therefore \(\rho\) kills the normal
subgroup \(\Lambda_N\) if and only if
\[
 (\rho(\lambda)-1)\rho(w)J=0
 \quad(\lambda\in\Lambda_N,\ w\in A),                    \tag{3}
\]
proving (IDH8). Geometrically, \(\Lambda_N\) acts by deck transformations
on \(\mathcal T\). The quotient graph has edge set
\[
 \Lambda_N\backslash A/B\simeq G_N/B_N,
\]
and (3) says that every return obtained by identifying a lifted edge in
this quotient has trivial fiber holonomy.

The two index-three stars are simply connected local neighborhoods in
\(\mathcal T\). Their finite Schreier cocycles determine transport inside
those stars, but no cycle of the quotient graph lies in one star. Equation
(2) is the shortest explicit normal return missed by the local data.

# Why this blocks the finite-corner conclusion

A relative ucp coefficient map on the infinite amalgam may be exact on
\(C^*(B)\); its Stinespring vacuum then satisfies (1). To factor through
the finite-dimensional algebra \(C^*(G_N)\), its minimal Stinespring
representation must satisfy all rows (3). The local Q-system identities
do not add them. Property \((T;FD)\) also cannot be applied before this
step if the resulting Stinespring representation is infinite-dimensional.

Conversely, suppose the joint flat-projection problem is solved over a
common core \(\beta\). Identity-coordinate evaluation compresses the two
invariant flat projections to exact \(V_\pm\)-representations on one
\(d\)-dimensional carrier, both restricting to \(\beta\). The amalgam
universal property gives an exact representation \(\pi:A\to U(d)\).
Since \(\pi(t)^N=\beta(t)^N=1\), the representation kills
\(\Lambda_N\) automatically and factors through \(G_N\). Hence joint
flat rounding supplies every deck row at once; proving it is not a local
finite-index corollary but the original relative repair theorem in another
coordinate system.
