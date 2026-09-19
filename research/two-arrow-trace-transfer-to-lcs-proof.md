---
rg: 2
id: two-arrow-trace-transfer-to-lcs-proof
kind: route
title: Transfer a non-CE BCS separation through one trace-extending arrow
target: trace-extending-bcs-to-lcs-maps-are-already-terminal
requires:
  - nested-conjugacy-stops-at-tv-dictator-projectors
---

# Transfer a non-CE BCS separation through one trace-extending arrow

## 1. The source supplied by MIP-star equals RE

Paddock--Slofstra
[Example 4.2](https://arxiv.org/html/2310.07901v2#S4) records the exact
algebraic consequence of MIP\(^*=\)RE used here: there is a finite BCS
\(B\) whose algebra \(\mathcal A_B\) has a tracial state, but admits no
unital \(*\)-homomorphism

$$
\mathcal A_B\longrightarrow\mathcal R^{\mathcal U}.    \tag{1}
$$

In their terminology, \(B\) is tracially satisfiable but not
\(\mathcal R^{\mathcal U}\)-satisfiable.  The associated synchronous game
has a perfect commuting-operator strategy but no perfect
quantum-approximable strategy.

Fix any tracial state \(\tau\) on \(\mathcal A_B\).

## 2. One arrow blocks every matrix-ultraproduct model

Let \(L\) be a finite binary LCS and suppose

$$
\iota:\mathcal A_B\longrightarrow\mathcal A_L          \tag{2}
$$

is a unital \(*\)-homomorphism.

If \(L\) were \(\mathcal R^{\mathcal U}\)-satisfiable, there would be a
unital \(*\)-homomorphism

$$
\psi:\mathcal A_L\longrightarrow\mathcal R^{\mathcal U}. \tag{3}
$$

The composite

$$
\psi\circ\iota:
\mathcal A_B\longrightarrow\mathcal R^{\mathcal U}     \tag{4}
$$

would contradict (1).  Therefore

$$
\mathcal A_L
\text{ is not }\mathcal R^{\mathcal U}\text{-satisfiable}.  \tag{5}
$$

No injectivity assumption on \(\iota\) was used.

## 3. Extending one trace supplies perfect completeness

Assume there is a tracial state \(\widetilde\tau\) on
\(\mathcal A_L\) such that

$$
\widetilde\tau\circ\iota=\tau.                         \tag{6}
$$

In particular, \(\mathcal A_L\) has a tracial state.  Combining (5) and
(6), \(L\) is tracially satisfiable but not
\(\mathcal R^{\mathcal U}\)-satisfiable.

Extension of every source trace is stronger than necessary.  Existence of
one pair \((\tau,\widetilde\tau)\) satisfying (6) is enough.

There is a simple two-arrow sufficient condition.  If, in addition to
(2), there is any unital \(*\)-homomorphism

$$
\kappa:\mathcal A_L\longrightarrow\mathcal A_B,        \tag{7}
$$

then

$$
\widetilde\tau:=\tau\circ\kappa                        \tag{8}
$$

is a tracial state on \(\mathcal A_L\).  Equations (2) and (7) need not be
inverse, and no condition on either composition is required.

## 4. Why an LCS target is terminal

Let \(\Gamma_L\) be the solution group of \(L\), with marked central
involution \(J\).  Paddock--Slofstra
[Lemma 5.7](https://arxiv.org/html/2310.07901v2#S5) states that

$$
\begin{aligned}
L\text{ tracially satisfiable}
 &\Longleftrightarrow J\neq1\text{ in }\Gamma_L,\\
L\text{ }\mathcal R^{\mathcal U}\text{-satisfiable}
 &\Longleftrightarrow
 J\text{ is nontrivial in approximate representations}.
\end{aligned}                                         \tag{9}
$$

By Sections 2 and 3, \(J\neq1\), but \(J\) is trivial in every approximate
representation.  Hence \(\Gamma_L\) is not hyperlinear.  This is also the
forward implication of their
[Proposition 5.8](https://arxiv.org/html/2310.07901v2#S5), which states the
equivalence between a tracial/non-\(\mathcal R^{\mathcal U}\) LIN
instance and a finitely presented nonhyperlinear group.

Thus the trace-extending map (2) is not an intermediate technical
convenience when the codomain is LCS.  It is the terminal theorem itself.

## 5. Audit of the published bridges

Fanizza--Kroell--Mehta--Paddock--Rochette--Slofstra--Zhao
[Theorem 5.5](https://arxiv.org/html/2510.04943v4#S5.SS1) constructs an
embedding of a nested-conjugacy BCS algebra into another BCS algebra and
extends every tracial state.  Therefore it has exactly the two properties
in Sections 2 and 3, except that its codomain is a general BCS.  If that
codomain were always an LCS, Section 4 would produce the sought
nonhyperlinear group.

The proof of their theorem retains the ordinary outer BCS relation and
routes the conjugacy relations through their group-to-BCS Lemma 3.12.
The projector analysis in
[tv-nested-conjugacy-bridge-boundary-proof](tv-nested-conjugacy-bridge-boundary-proof.md)
identifies that retained relation in the zero-noise Taller--Vidick cell as
the exactly-one dictator projector.

This agrees with two explicit literature fences.

- Paddock--Slofstra
  [Proposition 5.8](https://arxiv.org/html/2310.07901v2#S5) identifies the
  LIN separation itself with the group problem.
- Taller--Vidick
  [Introduction](https://arxiv.org/html/2507.22444v2#S1) state that generic
  algebra-embedding reductions from BCS to LCS are obstructed, and that
  perfect completeness would imply a nonhyperlinear group.

Consequently a source-dependent cyclic network which realizes (2) and
(6) should be evaluated as a proposed full solution, including its
finite-dimensional decoder.  The known MIP, CSP, nested-conjugacy, and
zero-noise long-code reductions do not already contain such a network.
