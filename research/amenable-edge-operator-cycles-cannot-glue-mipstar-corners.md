---
rg: 2
id: amenable-edge-operator-cycles-cannot-glue-mipstar-corners
kind: claim
title: Amenable-edge operator cycles cannot glue MIP-star predicate corners
artifacts:
  - research/amenable-edge-corner-gluing-proof.md
distinct_from:
  amenable-edge-cycles-cannot-create-an-lcs-gap: that treats Bass-Serre groups and the marked LCS involution; this treats arbitrary reducing corners in graphs of finite von Neumann algebras and an arbitrary BCS decoder.
  finite-predicate-signed-permutation-sector: that constructs every nonlinear predicate in one finite irreducible sector; this proves that reduced operator-graph gluing of those sectors cannot carry a non-Connes-embeddable global trace.
  finite-morita-toricization-cannot-encode-nonaffine-support: that assumes a representation-functorial finite Morita encoding; this assumes neither functoriality nor central coordinates and allows source-dependent HNN cycles.
---

Let \(A\) be a unital BCS algebra which has a tracial state but no
homomorphism to \({\cal R}^{\cal U}\), as supplied by MIP-star equals RE.
Let

\[
 {\mathfrak G}
 =({\cal G},(M_v,\tau_v)_v,(N_e,\tau_e)_e)
\]

be an arbitrary graph of finite von Neumann algebras with
trace-preserving edge embeddings. Suppose

1. every \(M_v\) embeds trace preservingly in \({\cal R}^{\omega}\); and
2. every \(N_e\) is amenable.

Write \(M=\pi_1^{\rm red}({\mathfrak G})\) for the reduced fundamental von
Neumann algebra. Then there is no nonzero projection \(p\in M\) and no
unital star-homomorphism

\[
 \Phi:A\longrightarrow pMp,                             \tag{1}
\]

where \(pMp\) is unital with unit \(p\).

More generally, every BCS trace decoded inside such a corner is
Connes-embeddable. Hence a prescribed non-Connes-embeddable MIP-star trace
cannot extend to a perfect model living in an amenable-edge operator
network.

This is a pointwise theorem. The graph, vertex algebras, edge embeddings,
corner, and decoder may all depend arbitrarily on the source instance.
Cycles and HNN gluings are allowed.

In particular, take the exact finite signed-permutation sector for each
local nonlinear predicate and glue the selected finite-dimensional blocks
along any finite-dimensional overlap algebras. Every vertex algebra is
finite-dimensional and every edge algebra is amenable, so the reduced
fundamental algebra is Connes-embeddable. Local exact predicate support
therefore does not become the required non-Connes-embeddable global
support by cyclic gluing.

The proof is one line after the correct permanence theorem. Fima-Freslon,
Corollary 6.10(1), puts \(M\) in \({\cal R}^{\omega}\). Every nonzero
corner of an \({\cal R}^{\omega}\)-embeddable finite algebra is again
\({\cal R}^{\omega}\)-embeddable. Composing (1) with such an embedding
contradicts the defining property of \(A\).

Thus the first possible trace-selected escape must use a nonamenable edge
algebra, a non-Connes-embeddable vertex algebra, a quotient rather than a
reduced fundamental algebra, or a global corner imposed outside the
operator-graph construction. The first option may be useful but is no
longer a finite-state synchronization interface; the second is already
the root obstruction. The claim does not construct a nonhyperlinear
group.
