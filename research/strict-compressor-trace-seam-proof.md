---
rg: 2
id: strict-compressor-trace-seam-proof
kind: route
title: Show that conjugation averaging annihilates the Kazhdan projection difference before any IRS limit
target: strict-compressor-kazhdan-radical-is-tracially-zero
requires:
  - strict-kazhdan-compressor-forces-non-rfd
  - coinduction-preserves-but-cannot-create-algebraic-envelope
  - probability-coinduction-retains-factor-but-not-group-generation
  - manzoor-native-haar-envelope-is-ce-after-corners
---

# The strict-compressor projection lies entirely outside the finite trace world

Let
\[
 K=tHt^{-1}<H,\qquad p=p_H,\qquad q=tpt^{-1},\qquad e=q-p.
                                                               \tag{1}
\]
The strict-compressor proof shows
\[
                       0\ne e=e^*=e^2.                    \tag{2}
\]

## 1. Every trace kills the projection

Let \(\tau\) be any tracial state on \(C^*_{\max}(G)\).  Since \(t\) is
unitary,
\[
 \tau(q)=\tau(tpt^{-1})=\tau(p),\qquad \tau(e)=0.          \tag{3}
\]
Because \(e\) is a projection,
\[
                       \tau(e^*e)=0.                      \tag{4}
\]
This kills \(e\) in the whole GNS representation, not only at its cyclic
vector.  Indeed, for every \(a\in C^*_{\max}(G)\),
\[
\begin{aligned}
 \|\pi_\tau(e)\pi_\tau(a)\xi_\tau\|^2
 &=\tau(a^*ea)
  =\tau(eaa^*)\\
 &\leq \|a\|^2\tau(e)=0.                                 \tag{5}
\end{aligned}
\]
The cyclic vectors \(\pi_\tau(a)\xi_\tau\) are dense, so
\[
                       \pi_\tau(e)=0.                     \tag{6}
\]

Equivalently, the tracial null set
\[
 N_\tau=\{a:\tau(a^*a)=0\}
\]
is a two-sided ideal and contains \(e\).  Intersecting (6) over all traces
puts the nonzero projection in the tracial radical.

The equal-rank finite-dimensional proof is the special case of a more
general finite-von-Neumann argument.  In a finite tracial representation,
the projections \(P=\pi(p)\leq Q=\pi(q)\) are unitarily equivalent.  Their
trace difference is zero, and faithfulness forces \(P=Q\).

## 2. Nonnormal commutators do not escape the radical

The Kazhdan projection \(p_H\) is central in \(C^*_{\max}(H)\).  Hence for
every \(\gamma\in H\),
\[
 [q,\gamma]=[q-p,\gamma]=[e,\gamma].                     \tag{7}
\]
Equation (6) yields
\[
 \pi_\tau([q,\gamma])=0,\qquad
 \tau([q,\gamma]^*[q,\gamma])=0                          \tag{8}
\]
for every tracial state.

When \(K\) is not normal in \(H\), the quasi-regular representation can
still prove \([q,\gamma]\ne0\).  Choose
\(\gamma^{-1}K\gamma\not\subseteq K\).  On
\(\ell^2(G/K)\),
\[
 q\delta_K=\delta_K,\qquad
 q\delta_{\gamma K}\ne\delta_{\gamma K},
\]
and therefore
\[
 [q,\gamma]\delta_K
    =q\delta_{\gamma K}-\delta_{\gamma K}\ne0.            \tag{9}
\]
Equations (8)--(9) make the seam exact: nonnormality supplies an
operator-norm detector, but no finite trace can assign it positive
\(L^2\)-mass.

## 3. IRS averaging annihilates the signal

For a subgroup \(L\leq G\), the root coefficient of the quasi-regular
representation is the state
\[
                  \varphi_L(g)=1_{\{g\in L\}}.            \tag{10}
\]
At \(L=K\), the computation in the strict-compressor proof gives
\[
 \varphi_K(e)=1-{1\over[H:K]}\geq {1\over2}.              \tag{11}
\]
This state is not tracial.

Let \(\mu\) be any invariant random subgroup and let
\[
 \tau_\mu(g)=\int_{\operatorname{Sub}(G)}1_{\{g\in L\}}\,d\mu(L).
                                                               \tag{12}
\]
Conjugation invariance makes \(\tau_\mu\) a trace.  Hence (3)--(8) give
\[
 \tau_\mu(e)=0,\qquad
 \tau_\mu([q,\gamma]^*[q,\gamma])=0.                      \tag{13}
\]
No choice of IRS, including coinduction or a weak limit of conjugacy-orbit
measures, can retain the quasi-regular signal.

The cancellation is visible before taking a limit.  For any state
\(\psi\),
\[
 \psi(e)=\psi(tpt^{-1})-\psi(p).                          \tag{14}
\]
Thus any net of averaged states which becomes invariant under
\(\operatorname{Ad}t\) on the single test \(p\) has
\(\psi_i(e)\to0\).  The loss is the defining invariance equation, not a
bad choice of orbital Følner sets.

## 4. No finite group-factor corner can carry the projection

Let \((M,\operatorname{tr})\) be a finite von Neumann algebra with faithful
normal trace, let \(z\in M\) be nonzero, and suppose
\[
 \Theta:C^*_{\max}(G)\longrightarrow zMz
\]
is a unital star-homomorphism, where the unit of the target corner is \(z\).
The normalized corner trace composed with \(\Theta\) is a tracial state.
Equation (3) says
\[
 \operatorname{tr}_z(\Theta(e))=0.
\]
The image is a projection and the corner trace is faithful, so
\[
                         \Theta(e)=0.                    \tag{15}
\]
This applies in particular to every matrix tracial ultraproduct and every
corner \(zL(\Lambda)z\) of a group factor.

Consequently a group extension, double, wreath product, or shared-center
presentation cannot promote \(e\) merely by embedding the original group
unitaries in a larger finite tracial representation.  Its restriction to
\(G\) is still tracial and (15) applies.  A nonreducing compression may
retain the quasi-regular vector state, but then it is not a star-homomorphism;
making that compression into a positive canonical corner is exactly the
missing trace-to-regular problem.

## 5. Norm detection has zero normalized-HS density

A norm matrix ultraproduct
\[
 \prod_n M_{d_n}\big/\bigoplus_n M_{d_n}
\]
need not carry a faithful normalized trace, so a star-homomorphism into it
may detect \(e\).  Let \(E_n\) be projection representatives.  Every
ultralimit of normalized matrix traces composed with the representation is
tracial on \(C^*_{\max}(G)\), so (3) forces
\[
                         {\operatorname{rank}E_n\over d_n}
                         \longrightarrow_\omega0.         \tag{16}
\]
Thus the same sequence is zero in the normalized-HS ultraproduct.  Tensoring
with an exact regular-character carrier preserves the rank fraction in
(16), and direct-sum repetition does the same.  A norm-level MF detector
therefore cannot be trace-masked into a positive-density HS detector by
amplification alone.

This is the precise MF-versus-hyperlinear boundary for the Kazhdan
projection witness.

## 6. What the recent IRS results do and do not provide

Manzoor, arXiv:2502.06697v2, constructs a non-co-hyperlinear IRS on a
nonabelian free group and embeds its non-Connes-embeddable GNS algebra in an
equivalence-relation algebra.  The free actor itself is sofic and
hyperlinear.  Hence the result is an explicit counterexample to the
implication
\[
 \text{non-CE IRS trace on }G
 \quad\Longrightarrow\quad
 \text{nonhyperlinear canonical trace of }G.              \tag{17}
\]
The 2025 sequel arXiv:2508.15154 remains in the IRS framework and proves
that even the IRS version of the determinant conjecture does not imply
co-hyperlinearity; it does not replace the IRS trace by a regular group
trace.

Probability coinduction can retain a supplied non-CE finite algebra as a
tensor coordinate of a crossed product.  However the canonical acting-group
unitaries generate \(L(\Lambda)\), not that coordinate.  Compact algebraic
coinduction similarly preserves an algebraic envelope only after one is
already supplied.  These are the exact conclusions of
\(\textit{probability-coinduction-retains-factor-but-not-group-generation}\)
and
\(\textit{coinduction-preserves-but-cannot-create-algebraic-envelope}\).

If one could put the non-CE IRS GNS algebra in a nonzero trace-preserving
corner of some \(L(\Lambda)\), then \(L(\Lambda)\) would be non-CE and
\(\Lambda\) would be a nonhyperlinear group.  That would solve the open root
problem itself.  Neither recent IRS paper supplies such a compiler, and
(15) proves that the strict-compressor projection \(e\) cannot be the
payload of one.
