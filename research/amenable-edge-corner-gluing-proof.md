---
rg: 2
id: amenable-edge-corner-gluing-proof
kind: route
title: Pass Connes embeddability through every reducing corner of an operator graph
target: amenable-edge-operator-cycles-cannot-glue-mipstar-corners
requires:
  - finite-predicate-signed-permutation-sector
---

# Pass Connes embeddability through every reducing corner of an operator graph

## 1. Input from the MIP-star separation

Paddock-Slofstra, Example 4.2, records the consequence of MIP-star equals
RE needed here: there is a finite BCS algebra \(A\) such that

\[
 A\text{ has a tracial state},                           \tag{1}
\]

but

\[
 \text{there is no unital star-homomorphism }
 A\longrightarrow{\cal R}^{\cal U}.                     \tag{2}
\]

Equivalently, the associated synchronous game has a perfect
commuting-operator strategy but no perfect quantum-approximable strategy.
This is the source separation an exact BCS-to-LCS compiler would have to
preserve.

## 2. Reduced operator-graph gluing is Connes embeddable

Let

\[
 {\mathfrak G}
 =({\cal G},(M_v,\tau_v)_v,(N_e,\tau_e)_e)
\]

be a graph of finite von Neumann algebras with faithful normal traces and
trace-preserving edge embeddings. Assume

\[
 M_v\hookrightarrow{\cal R}^{\omega}
 \quad\text{trace preservingly for every }v,             \tag{3}
\]

and assume every \(N_e\) is amenable. Let

\[
 M=\pi_1^{\rm red}({\mathfrak G})                        \tag{4}
\]

with its fundamental trace.

Fima-Freslon, Corollary 6.10(1), applies directly to (3)-(4) and gives a
trace-preserving embedding

\[
 \Theta:M\longrightarrow{\cal R}^{\omega}.              \tag{5}
\]

Their Proposition 6.9 writes (4) as an inductive limit of iterated
amalgamated free products and HNN extensions. Their proof of Corollary
6.10 explicitly reduces an HNN extension to a corner of an amalgamated
free product. Thus (5) includes arbitrary cycles in \({\cal G}\); it is
not a tree-only assertion.

## 3. Corner lemma

We need the following standard permanence fact in its normalized-trace
form.

**Lemma.** If a finite von Neumann algebra \((M,\tau)\) embeds trace
preservingly in \({\cal R}^{\omega}\), and \(0\ne p\in M\) is a
projection, then

\[
 (pMp,\tau_p),\qquad
 \tau_p(x)=\frac{\tau(x)}{\tau(p)},                       \tag{6}
\]

also embeds trace preservingly in \({\cal R}^{\omega}\).

**Proof.** Put \(q=\Theta(p)\) and \(t=\tau(q)>0\). Represent \(q\) by a
sequence of projections \(q_n\in{\cal R}\) with
\(\tau_{\cal R}(q_n)\to t\). Compression represents \(q{\cal
R}^{\omega}q\), with normalized trace, inside

\[
 \prod_{\omega}
 \left(q_n{\cal R}q_n,
       \frac{\tau_{\cal R}}{\tau_{\cal R}(q_n)}\right).  \tag{7}
\]

Every nonzero corner \(q_n{\cal R}q_n\), with its normalized trace, is
isomorphic to the hyperfinite \(\mathrm{II}_1\) factor \({\cal R}\).
After discarding an \(\omega\)-null set of zero \(q_n\)'s and choosing
trace-preserving isomorphisms coordinatewise, the ultraproduct in (7) is
\({\cal R}^{\omega}\). The restriction of \(\Theta\) to \(pMp\) is
therefore the required normalized trace-preserving embedding. \(\square\)

## 4. No MIP-star decoder can live in the corner

Suppose, contrary to the claim, that \(0\ne p\in M\) and that there is a
unital star-homomorphism

\[
 \Phi:A\longrightarrow pMp.                             \tag{8}
\]

Here unital means \(\Phi(1_A)=p\), the unit of the corner. By the corner
lemma there is a unital trace-preserving embedding

\[
 \Psi:pMp\longrightarrow{\cal R}^{\omega}.              \tag{9}
\]

Then \(\Psi\circ\Phi\) is a unital star-homomorphism from \(A\) to
\({\cal R}^{\omega}\), contradicting (2). This proves the no-go.

The trace version is equally direct. The trace decoded by (8) is

\[
 \sigma=\tau_p\circ\Phi.                                 \tag{10}
\]

Equations (9)-(10) exhibit \(\sigma\) as a
Connes-embeddable trace. Thus even when the source algebra has other
traces, no prescribed non-Connes-embeddable trace can be obtained by
restricting the fundamental trace of an operator graph satisfying (3).

## 5. Why this reaches nonlinear local predicate sectors

For a nonempty Boolean predicate
\(S\subseteq\{+1,-1\}^k\), the
finite-predicate-signed-permutation-sector construction gives a finite
group \(H_S\), an irreducible representation \(\pi_S\), and commuting
coordinate involutions whose joint spectrum in that sector is exactly
\(S\). Therefore every local nonlinear predicate can be represented
exactly in a finite-dimensional algebra

\[
 M_S=\pi_S(\mathbb C[H_S])''.                            \tag{11}
\]

One may choose arbitrary source-dependent finite-dimensional overlap
algebras \(N_e\), arbitrary trace-preserving embeddings into the local
blocks, and arbitrary HNN cycles. Nevertheless,

\[
 M_S\text{ is }{\cal R}^{\omega}\text{-embeddable},
 \qquad
 N_e\text{ is amenable}.                                \tag{12}
\]

Sections 2-4 apply. Hence exact nonlinear support inside every separate
cell does not evade the global obstruction. The reduced graph
construction supplies only a Connes-embeddable global trace.

This pinpoints the failure more sharply than scalar affine-hull leakage.
The local selected irreducible types may be perfectly nonlinear. What
fails is making their global holonomy carry the MIP-star
non-Connes-embeddable trace while all interfaces remain amenable.

## 6. Exact residual gate for an LCS compiler

A perfect decoder of the source BCS observables inside a target model
automatically induces (8), by the universal property of the BCS algebra.
Consequently, an exact LCS compiler cannot place its perfect target model
entirely inside a reduced operator graph of the class above.

At least one of the following must happen:

1. an edge algebra is nonamenable;
2. a vertex algebra is already non-Connes-embeddable;
3. the target is a quotient or another non-reduced completion for which
   the Fima-Freslon embedding theorem does not apply; or
4. the global selector projection is imposed outside the fundamental
   operator graph.

Options 1, 3, and 4 are genuine remaining mathematical gates. Option 2
already contains the source obstruction and does not groupify it. This
theorem neither supplies any of these gates nor constructs a
nonhyperlinear group.

## 7. Citation audit

- Connor Paddock and William Slofstra,
  [Satisfiability problems and algebras of boolean constraint system
  games, Example 4.2](https://arxiv.org/html/2310.07901).
  The example states exactly that MIP-star equals RE supplies a BCS algebra
  with a tracial state and no homomorphism to
  \({\cal R}^{\cal U}\).

- Pierre Fima and Amaury Freslon,
  [Graphs of quantum groups and K-amenability, Proposition 6.9 and
  Corollary 6.10(1)](https://arxiv.org/html/1307.5609).
  Proposition 6.9 is the unscrewing theorem. Corollary 6.10(1) states
  exactly that amenable edge algebras and
  \({\cal R}^{\omega}\)-embeddable vertex algebras give an
  \({\cal R}^{\omega}\)-embeddable reduced fundamental von Neumann
  algebra; its proof explicitly includes HNN cycles.
