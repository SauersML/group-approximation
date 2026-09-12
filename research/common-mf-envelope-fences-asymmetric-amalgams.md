---
rg: 2
id: common-mf-envelope-fences-asymmetric-amalgams
kind: claim
title: A common MF envelope fences an asymmetric amalgam
artifacts:
distinct_from:
  shulman-amalgam-mf-criterion: that is the exact C*-algebraic common-corona criterion; this is a concrete group-normal-form sufficient condition using one common MF group envelope.
  mf-is-invariant-under-symmetric-doubling: that treats two full copies of one vertex group; this embeds genuinely different vertex groups into such a symmetric double.
  kazhdan-edge-terminal-sign-remains-hyperlinear: that exposes a direct product and finite transverse edge in one explicit construction; this applies to any edge, without needing a transverse decomposition of the target amalgam itself.
---

**ESTABLISHED OPERATOR-NORM MF FIREWALL; TRACE-BLIND.**

Let \(H,G_0,G_1,M\) be countable groups, let
\(\theta_i:H\hookrightarrow G_i\) and \(j_i:G_i\hookrightarrow M\) be
injections, and suppose
\[
j_0\theta_0=j_1\theta_1=:j.                              \tag{CME1}
\]
If \(M\) is MF in the operator-norm matrix-corona sense, then
\[
G_0*_{\theta_0,\theta_1}G_1
\quad\text{is operator MF}.                              \tag{CME2}
\]

More precisely, there is a canonical injection
\[
G_0*_{H}G_1\ \hookrightarrow\
M*_{j(H)}M.                                              \tag{CME3}
\]
Shulman's symmetric-double theorem makes the group on the right MF, and
operator MF passes to subgroups.

The edge \(H\) is unrestricted: it may be infinite, nonamenable, or have
property \((T)\). Consequently, merely making the two vertices unequal does
not leave the symmetric-double firewall. Any asymmetric terminal-sign design
whose two vertex embeddings synchronize inside one known MF group is still
operator MF. In particular, if \(G_0\leq G_1=M\) and the two edge maps agree
inside \(M\), then \(G_0*_H G_1\) is operator MF whenever \(M\) is.

This is not a hyperlinear permanence statement. The embedding in (CME3) and
Shulman's theorem select no canonical trace, so they do not give
normalized-Hilbert--Schmidt microstates. A putative nonhyperlinear amalgam
could still be operator MF. For an operator-MF obstruction, however, the
asymmetric branch must fail every such common-envelope realization; at the
C*-level Shulman's compatible-corona condition is the exact broader
criterion.

DERIVATION
embed-asymmetric-amalgam-in-a-symmetric-mf-double
