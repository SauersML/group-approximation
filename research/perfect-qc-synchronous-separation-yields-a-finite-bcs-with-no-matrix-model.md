---
rg: 2
id: perfect-qc-synchronous-separation-yields-a-finite-bcs-with-no-matrix-model
kind: claim
title: A 2025 perfect commuting separation yields a finite BCS with no matrix model
distinct_from:
  every-bcs-is-a-trace-pullback-quotient-of-an-lcs: that starts from an arbitrary BCS trace and constructs a reverse LCS-to-BCS quotient with a classical matrix sector; this supplies a particular perfect-qc BCS whose algebra has no unital finite-dimensional representation at all.
  trace-extending-bcs-to-lcs-maps-are-already-terminal: that states the abstract terminal criterion; this extracts a concrete 2025 source algebra and reduces it further to an independent-set predicate.
  central-block-hecke-predicates-force-affine-group-spectra: that classifies finite central-type selector blocks; this identifies the exact nonaffine projection algebra which a successful group corner would have to carry.
---

**ESTABLISHED PRIMARY-SOURCE BRIDGE; NO GROUP OR NONHYPERLINEAR
WITNESS YET.**

There is a finite synchronous nonlocal game \(G\) such that

\[
 \omega^{\mathrm{co}}(G)=1,
 \qquad
 \omega^*(G)\leq \frac12 .
 \tag{PQB1}
\]

This is an exact consequence of Lin's 2025 \(1/2\)-Bell-separation
construction: Theorem 6.15 is RE-complete, and the paragraph immediately
after the theorem realizes its no instances by synchronous games with
precisely the two values in (PQB1). In particular, perfect commuting
completeness no longer has to be obtained by taking an
\(\varepsilon\)-complete construction to a limit.

One may choose the source in the following more rigid form. Let
\(X(G)\) be the game graph, let \(t\) be the number of questions of \(G\),
and let \(I=(X(G),t)\) be the associated independent-set game. Then

\[
 \omega^{\mathrm{co}}(I)=1,
 \qquad
 \omega^*(I)<1 .
 \tag{PQB2}
\]

The perfect-regime reduction of Mancinska--Spaas--Spirig--Vernooij
(Theorem 3.1 and Remark 3.2) is formulated with PVMs in a tracial von
Neumann algebra and therefore applies both to finite-dimensional and
commuting strategies. Its 2025 stability theorem also gives a quantitative
gap, but strict inequality in (PQB2) already suffices here.

Let \(\mathcal A_I\) be the finite synchronous projection algebra of
\(I\). It has a tracial state, but

\[
 \mathcal A_I\longrightarrow M_d(\mathbf C)
 \quad\text{has no unital star-homomorphism for any }d<\infty .
 \tag{PQB3}
\]

Moreover every tracial state on \(\mathcal A_I\) is
non-Connes-embeddable. Indeed, a unital matrix representation would be a
perfect finite-dimensional strategy, while a Connes-embeddable trace
would approximate its finite list of projection moments by matrix PVMs
and force \(\omega^*(I)=1\), contradicting (PQB2).

Paddock's Proposition 4.22 identifies the synchronous game algebra
star-isomorphically with its finite SynchBCS algebra. Consequently there
is a finite Boolean constraint system \(B_I\) such that

\[
 \mathcal A(B_I)\cong\mathcal A_I,
 \tag{PQB4}
\]

so \(\mathcal A(B_I)\) has a trace, has no unital finite-dimensional
representation, and every one of its traces is non-CE. The constraints
are explicit: one Boolean symmetry for every question-outcome pair,
one-hot commuting/product relations in each question, and one
\(\widetilde{\mathrm{AND}}\) constraint for every forbidden pair.

The exact remaining compiler is now sharply isolated. It would be enough
to construct a finitely presented group \(\Gamma\), a central involution
\(J\), \(p_-=(1-J)/2\), and a unital map

\[
 \Phi:\mathcal A(B_I)\longrightarrow p_-C^*(\Gamma)p_-
 \tag{PQB5}
\]

which extends one of the traces in (PQB4) and has a dimension-independent
normalized-Hilbert--Schmidt decoder from approximate representations of
\(\Gamma\) back to near-perfect strategies for \(I\). Exact unitality
alone would make every finite-dimensional representation of \(\Gamma\)
kill \(p_-\), but the repository's shared-center and Abels examples show
that exact finite-dimensional invisibility is not enough: the robust
decoder is load-bearing.

The newer embedding theorems do not yet supply (PQB5).
Fanizza--Kroell--Mehta--Paddock--Rochette--Slofstra--Zhao, Theorem 5.5,
embeds a nested-conjugacy BCS algebra into another BCS algebra and extends
every trace, but it leaves the source's nonlinear BCS relations as BCS
relations. Their Lemma 3.12 runs from an involutively generated group
algebra into a BCS algebra, the reverse of (PQB5). The 2026
Kakariadis--Leimbach--Todorov--van Suijlekom Theorems 4.22 and 5.21
characterize positive operator extension on finite group Fourier windows
by complete Fejer--Riesz/factorisation properties; they provide completely
positive maps, not projection-preserving star-homomorphisms.

The node
`naimark-stinespring-does-not-weaken-the-finite-synchbcs-pauli-corner-gate`
now closes the formal dilation shortcuts around (PQB5).  If ambient
Naimark projections compress to the sharp SynchBCS PVMs, the identity
`pPp-(pPp)^2=pP(1-p)Pp` forces the corner to reduce every projection.
The full multiplicative-domain calculation gives the same conclusion for
an exactly multiplicative Stinespring or matrix-unit compression.  Thus
finite amplification and exact dilation already produce a literal unital
corner map.  If the host is a finite-phase Pauli crossed product, pulling
back its normalized corner trace makes the host non-CE and the finite
central-character compiler produces a nonhyperlinear group.  This is an
exact terminal implication, not a construction of the missing map.

The universal free-label shortcut is also exact but circular.
`free-label-haarization-erases-the-source-and-canceling-labels-restate-the-group-factor-gate`
shows that `v_i=u_i tensor lambda(s_i)` always generates a copy of
`L(F_n)`, independently of the source tuple.  Adding
`b_i=1 tensor lambda(s_i)` recovers `u_i tensor 1`, but the generated
abstract group is exactly `H times F_n`.  Its ambient trace is canonical
if and only if `tau(h)=0` for every nonidentity `h in H`, equivalently
the original GNS algebra was already trace-isomorphic to `L(H)`.  Thus
free labels either erase the non-CE source or restate the group-factor
gate.

Thus the 2025 literature closes the perfect-completeness source gate and
reduces it to a finite independent-set/BCS algebra. The unresolved gate is
solely a robust multiplicative group-corner realization of its partition
and forbidden-overlap projections. No nonhyperlinear group is claimed.

Primary sources:

- Junqiao Lin, *MIPco=coRE*, Definition 6.14 and Theorem 6.15,
  https://arxiv.org/abs/2510.07162
- Laura Mancinska, Pieter Spaas, Taro Spirig, and Matthijs Vernooij,
  *Gap-preserving reductions and RE-completeness of independent set
  games*, Theorem 3.1, Remark 3.2, and Theorem A,
  https://arxiv.org/abs/2505.05253
- Connor Paddock, *Rounding near-optimal quantum strategies for nonlocal
  games to strategies using a maximally entangled state*, Proposition
  4.22, https://arxiv.org/abs/2203.02525
- Marco Fanizza et al., *The NPA hierarchy does not always attain the
  commuting operator value*, Lemma 3.12 and Theorem 5.5,
  https://arxiv.org/abs/2510.04943
- Evgenios Kakariadis et al., *Operator systems and positive extensions
  over discrete groups*, Theorems 4.22 and 5.21,
  https://arxiv.org/abs/2603.29958

DERIVATION
perfect-qc-graph-algebra-and-fourier-multiplicative-domain-proof
