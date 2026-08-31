---
rg: 2
id: amenable-edge-cycle-hyperlinearity-proof
kind: route
title: Close source-dependent Bass-Serre networks under hyperlinearity
target: amenable-edge-cycles-cannot-create-an-lcs-gap
---

# Close source-dependent Bass-Serre networks under hyperlinearity

## 1. The graph-of-groups permanence theorem

Let

\[
 {\cal G}=(X,(G_v)_{v\in V(X)},(G_e)_{e\in E(X)})
\]

be a graph of groups. The two maps from an edge group to its incident
vertex groups are injective, as required in Bass-Serre theory. Put

\[
 \Gamma=\pi_1({\cal G}).
\]

Assume that every \(G_v\) is hyperlinear and every \(G_e\) is amenable.
Then

\[
 \Gamma\text{ is hyperlinear}.                           \tag{1}
\]

Here is the operator-algebra proof, including the cycle case. For every
edge incidence, the group inclusion gives a trace-preserving inclusion

\[
 L(G_e)\longrightarrow L(G_v)
\]

of finite von Neumann algebras. The canonical conditional expectation is
the Fourier truncation

\[
 E_e^v(\lambda_g)=
 \begin{cases}
  \lambda_g,&g\in G_e,\\
  0,&g\notin G_e.
 \end{cases}                                             \tag{2}
\]

Hyperlinearity of \(G_v\) says that \(L(G_v)\) embeds trace preservingly
in \({\cal R}^{\omega}\). Amenability of \(G_e\) says that \(L(G_e)\) is
amenable. The reduced fundamental von Neumann algebra of this graph is
\(L(\Gamma)\).

Fima and Freslon, Corollary 6.10(1), state that the reduced fundamental
von Neumann algebra of a graph of finite von Neumann algebras embeds in
\({\cal R}^{\omega}\) if all vertex algebras do and all edge algebras are
amenable. Their Proposition 6.9 unscrews an arbitrary graph into
amalgamated free products and HNN extensions. In particular, their proof
does not assume that the underlying graph is a tree. For an HNN edge they
use the corner identity

\[
 \operatorname{HNN}(M,N,\theta)
 \cong
 e_{11}\left(
   (M_2(\mathbb C)\mathbin{*}_{N\oplus N})
   (M_2(\mathbb C)\otimes N)
 \right)e_{11},                                         \tag{3}
\]

with the first factor in (3) understood as \(M_2(\mathbb C)\otimes M\).
Thus the same \({\cal R}^{\omega}\)-embeddability permanence handles the
cycle edges. Applying the corollary to (2) proves (1).

There is also a direct statement in Fima-Freslon, Theorem 4.6(3): a graph
of unimodular hyperlinear discrete quantum groups with amenable edge
quantum groups has hyperlinear fundamental quantum group. Ordinary
discrete groups are a special case.

## 2. The marked LCS consequence

Let \(B\) be the BCS associated with a finite linear system \(Ax=b\), and
let \(\Gamma_B=\Gamma(A,b)\) be its solution group with distinguished
central involution \(J\). Assume

\[
 \Gamma_B\cong\pi_1({\cal G})                            \tag{4}
\]

for a graph satisfying the hypotheses of Section 1.

Paddock-Slofstra, Lemma 5.7, gives the two exact equivalences

\[
 \begin{aligned}
 B\text{ is tracially satisfiable}
  &\Longleftrightarrow J\ne1\text{ in }\Gamma_B,\\
 B\text{ is }{\cal R}^{\cal U}\text{-satisfiable}
  &\Longleftrightarrow
   J\text{ is nontrivial in approximate representations of }\Gamma_B.
 \end{aligned}                                          \tag{5}
\]

Suppose \(B\) is tracially satisfiable. The first line of (5) gives
\(J\ne1\). By (1) and (4), \(\Gamma_B\) is hyperlinear. By definition,
every nonidentity element of a hyperlinear group is nontrivial in
approximate representations. In particular this holds for \(J\), and the
second line of (5) proves

\[
 B\text{ is }{\cal R}^{\cal U}\text{-satisfiable}.       \tag{6}
\]

One can see the marked separation directly. A trace-preserving embedding

\[
 \iota:L(\Gamma_B)\longrightarrow{\cal R}^{\omega}
\]

is injective and satisfies, for \(J\ne1\),

\[
 \|\iota(J)-1\|_2^2
 =2-2\operatorname{Re}\tau(\iota(J))
 =2,                                                     \tag{7}
\]

because the canonical group trace of \(J\) is zero. Thus \(J\) is not
merely nontrivial in the ultraproduct; it is maximally separated from the
identity in the normalized Hilbert-Schmidt metric.

The game interpretation of (6) is a perfect
quantum-approximable strategy. Therefore for every \(\varepsilon>0\)
there is a finite-dimensional strategy with winning probability at least
\(1-\varepsilon\). No constant \(s<1\) can upper-bound all
finite-dimensional strategies while the commuting-operator value is one.

## 3. Pointwise source dependence does not help

Let a proposed compiler assign to each source instance \(S\) a possibly
different graph of groups \({\cal G}(S)\). It may choose:

- different vertex groups;
- different amenable interface groups and embeddings;
- arbitrarily many overlapping contexts; and
- an arbitrary collection of HNN cycle edges.

If each vertex group of \({\cal G}(S)\) is hyperlinear and each edge group
is amenable, the proof above applies separately to that single \(S\).
There is no uniformity, functoriality, or fixed-seed hypothesis anywhere
in the argument. Hence source dependence by itself does not open an
escape.

The injectivity of the edge maps is essential. Adding a relation by a
noninjective coequalizer produces a quotient, not a Bass-Serre graph of
groups. Hyperlinearity is not available through arbitrary quotients, so
that case is intentionally outside the theorem. Likewise, a BCS
projector equation is not an edge-group identification.

## 4. Finite-cell networks have an exact finite-dimensional sector

There is a stronger conclusion in the common finite-cell case. Suppose
the underlying graph is finite and all vertex groups are finite. Then all
edge groups are finite and the Karrass-Pietrowski-Solitar theorem makes
\(\Gamma=\pi_1({\cal G})\) virtually free.

A virtually free group is residually finite. For completeness, let
\(F\triangleleft\Gamma\) be a finite-index free subgroup. If
\(g\notin F\), the finite quotient \(\Gamma/F\) detects \(g\). If
\(1\ne g\in F\), residual finiteness of \(F\) gives a finite-index normal
subgroup \(N\triangleleft F\) with \(g\notin N\). Intersect the finitely
many \(\Gamma\)-conjugates of \(N\). The resulting subgroup is
finite-index and normal in \(\Gamma\), is contained in \(N\), and still
omits \(g\).

Apply this to a nontrivial distinguished involution \(J\). There is a
finite quotient \(q:\Gamma\to Q\) with \(q(J)\ne1\). In the left regular
representation of \(Q\), the projection

\[
 p_-=\frac{1-\lambda_Q(q(J))}{2}                         \tag{8}
\]

is nonzero. Since \(J\) is central, \(p_-\) reduces the representation.
On \(p_-\ell^2(Q)\), the restricted representation satisfies

\[
 \rho(J)=-I.                                             \tag{9}
\]

For a solution group, (9) is an exact finite-dimensional operator
solution: the variable generators are reflections, variables in a
context commute, and the equation products have the prescribed signs.
Thus a finite graph of finite group cells has an exact
finite-dimensional perfect sector whenever \(J\ne1\), not just a
sequence of near-perfect sectors.

## 5. The Hilbert-Schmidt Dehn-function boundary

Fix a finite presentation of \(\Gamma_B\). Let

\[
 \operatorname{hlp}(J;\delta,\eta)
\]

be the least matrix dimension of an \(\eta\)-representation in which
\(J\) is at least \(\delta\) away from the identity, with value \(+\infty\)
if none exists. Paddock-Slofstra use the fixed separation \(1/4\); any
constant in \((0,\sqrt2)\) is equivalent.

For the amenable-edge graph networks above,

\[
 \operatorname{hlp}(J;1/4,\eta)<+\infty
 \qquad\text{for every }\eta>0                           \tag{10}
\]

whenever \(J\ne1\). The dimensions in (10) need not have any reasonable
bound. Cycles can therefore amplify hyperlinear profile or an
Hilbert-Schmidt Dehn function drastically. What they cannot do is make
the profile infinite at some positive relation error. The latter is
exactly the marked obstruction required by (5) for a commuting-versus-
quantum-approximable LCS separation.

Consequently, a genuinely live cyclic route must use at least one of:

1. a vertex group already outside the hyperlinear class;
2. a nonamenable edge/interface;
3. a noninjective quotient relation; or
4. an operator-algebraic corner/projector not expressible as a group
   amalgamation.

The first option is already the root problem. The other three are the
precise residual gates left by this theorem.

## 6. Citation audit

- Pierre Fima and Amaury Freslon,
  [Graphs of quantum groups and K-amenability,
  Theorem 4.6(3), Proposition 6.9, and Corollary
  6.10(1)](https://arxiv.org/html/1307.5609).
  Corollary 6.10(1) is exactly the
  \({\cal R}^{\omega}\)-embeddability permanence statement for graphs of
  finite von Neumann algebras with amenable edge algebras. Its proof
  explicitly handles HNN extensions by the corner construction (3).

- Connor Paddock and William Slofstra,
  [Satisfiability problems and algebras of boolean constraint system
  games, Lemma 5.7 and Proposition
  5.8](https://arxiv.org/html/2310.07901).
  Lemma 5.7 is exactly (5); the paragraph following it identifies
  hyperlinearity with nontriviality of every nonidentity element in
  approximate representations.

- A. Karrass, A. Pietrowski, and D. Solitar,
  [Finite and infinite cyclic extensions of free
  groups](https://doi.org/10.1017/S1446788700015445),
  Journal of the Australian Mathematical Society 16 (1973), 458-466.
  Their structure theorem gives the equivalence between finitely
  generated virtually free groups and fundamental groups of finite
  graphs of finite groups used in Section 4.
