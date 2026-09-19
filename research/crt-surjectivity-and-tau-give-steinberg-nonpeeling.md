---
rg: 2
id: crt-surjectivity-and-tau-give-steinberg-nonpeeling
kind: route
title: Use CRT surjectivity and congruence expansion to rule out Steinberg peeling
target: steinberg-endpoints-are-indecomposable-but-payload-width-one
requires:
  - bounded-payload-congruence-tensors-have-uniform-capture
---

# Every odd reduction is already visible on the Iwahori edge

Work first in \(\operatorname{SL}_2\). The upper Iwahori subgroup is the
inverse image of an order-two point stabilizer
\[
 H_2<\operatorname{SL}_2(\mathbb F_2)\cong S_3
\]
under reduction modulo two. For odd \(p\), classical surjectivity of
\(\operatorname{SL}_2(\mathbb Z)\) onto
\(\operatorname{SL}_2(\mathbb Z/2p\mathbb Z)\), followed by the Chinese
remainder theorem, gives
\[
 \operatorname{SL}_2(\mathbb Z)
 \longrightarrow
 \operatorname{SL}_2(\mathbb F_2)\times
 \operatorname{SL}_2(\mathbb F_p)                        \tag{1}
\]
onto. Given \(g\in\operatorname{SL}_2(\mathbb F_p)\), lift the pair
\((1,g)\). Its first coordinate lies in \(H_2\), so the lift belongs to the
Iwahori subgroup and maps to \(g\) modulo \(p\). Projectivizing proves that
\[
 B\longrightarrow G_p
\]
is onto. The positive modular vertex is onto by ordinary reduction. The
negative vertex is conjugate to it inside
\(\operatorname{PSL}_2(\mathbb Z[1/2])\); modulo odd \(p\), the conjugating
diagonal matrix is invertible and induces an automorphism of \(G_p\).
Therefore the negative vertex is onto as well. This proves (SIP2).

The Steinberg representation of \(G_p\) is irreducible and has dimension
\(p\). Since the image of each group in (SIP2) is all of \(G_p\), its
restriction along each of the three surjections remains irreducible. In
particular its edge commutant is exactly the scalars.

# Selberg expansion upgrades Schur irreducibility to uniform nonpeeling

The finite-index subgroup \(B<\operatorname{PSL}_2(\mathbb Z)\) has
property tau with respect to its congruence kernels. Fixing \(S_B\), there
is \(\kappa_B>0\) such that every congruence-quotient representation
\(\rho\) and every vector \(\xi\) orthogonal to its invariant vectors obey
\[
 \sum_{s\in S_B}\|\rho(s)\xi-\xi\|^2
 \geq\kappa_B\|\xi\|^2.                                  \tag{2}
\]
Apply (2) to the conjugation representation
\[
 \rho_p(s)T=\eta_p(s)T\eta_p(s)^*
\]
on \(M_p\) with its normalized Hilbert--Schmidt inner product. This
representation factors through the congruence quotient \(G_p\). By the
irreducibility just proved, its invariant vectors are precisely
\(\mathbb C1\); hence the traceless matrices are exactly the orthogonal
complement of the invariant space. Taking
\[
 \xi=T-\operatorname{tr}_p(T)1
\]
in (2), and observing that
\[
 \|\rho_p(s)T-T\|_{2,p}=\|[T,\eta_p(s)]\|_{2,p},
\]
gives (SIP3).

For a projection \(e\) with \(\operatorname{tr}_p(e)=t\),
\[
 \|e-t1\|_{2,p}^2=t-t^2=t(1-t).                          \tag{3}
\]
At least one term in the sum in (SIP3) is no smaller than its average.
Equations (SIP3) and (3) therefore imply (SIP4). An exact common reducing
decomposition would give a nontrivial projection commuting with the edge
image, contradicting Schur's lemma. A sequence of positive-density
approximately reducing decompositions would contradict the uniform lower
bound (SIP4). Decomposing the separate order-two or cyclic spectral
subgroups does not evade this conclusion because their spectral projections
are not common reducing projections for the full edge image.

# The same blocks are already exact endpoints

Reduction modulo \(p\) is a homomorphism on
\(A=\operatorname{PSL}_2(\mathbb Z[1/2])\), since \(2\) is invertible modulo
\(p\). Thus \(\eta_p\) is one exact representation of \(A\), and its two
vertex restrictions agree exactly under the prescribed Iwahori
identification. Taking the one-dimensional trivial payload pair and
\(\eta_p\) itself as the congruence endpoint realizes (SIP5). Its edge
defect and congruence-capture distance are both zero.

Hence the same family simultaneously has dimension tending to infinity,
irreducible vertex and edge restrictions, a uniform adjoint commutant gap,
and minimal residual payload width one. High-dimensional irreducibility is
therefore not the unbounded-payload obstruction isolated by the
authentication trichotomy. Only dimension which cannot be transferred into
a compatible congruence endpoint factor remains relevant.
