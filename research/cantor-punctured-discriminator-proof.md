---
rg: 2
id: cantor-punctured-discriminator-proof
kind: route
title: Use a displaced cone away from the punctures and dovetail equality with normal-closure certificates
target: cantor-punctured-prefix-groups-detect-word-problem
requires: []
artifacts:
  - research/artifacts/boone-higman-shell-effective-presentation-2026-09-08.md
---

First K_F is nontrivial and simple. For F empty this is simplicity
of the binary Thompson group V. Otherwise choose nested proper
clopen neighborhoods U_n of F cofinal among its neighborhoods.
The complement of each U_n is a nonempty finite union of binary
cones. A prefix identification with the full Cantor set identifies
Fix_V(U_n) with V. These are nested simple groups with union K_F.
A nontrivial normal subgroup of the union meets some stage
nontrivially and hence contains every later stage by simplicity.
Thus it is the whole union.

Now let N be a nontrivial normal subgroup of D, and choose 1!=f in N.
Its moved-point set is nonempty and open. Removing F union f^-1(F)
still leaves a moved point x. Choose a small cylinder U about x
such that U and f(U) are disjoint and both avoid F. Choose prefix
permutations a,b supported in U whose commutator is nonidentity;
for example interchange respectively the first two and last two
of three disjoint equal-depth subcylinders of U. They lie in K_F.

With [a,b]=a*b*a^-1*b^-1 and right-to-left composition, disjoint
support gives

    [[a,f],b]=[a,b]!=1.

Indeed f*a^-1*f^-1 is supported in f(U) and commutes with b.
Normality puts this double commutator in N. Hence N intersect K_F
is a nontrivial normal subgroup of K_F. Simplicity gives K_F<=N.
This does not require K_F itself to be normal in D.

For a recursive presentation of D on a finite generating set,
fix a word for one nonidentity k in K_F. On input w, run these
two searches in parallel:

1. Enumerate a proof that w=1 from the relators of D.
2. Enumerate a proof that k=1 after adjoining w as one extra relator.

When w=1, the first search terminates and the second cannot, since
k!=1 in D. When w!=1, the normal closure of w contains K_F and
hence k, so the second search terminates and the first cannot.
This decides the word problem. Existence of the fixed marked word
for k is enough for decidability of a fixed group; no procedure
for recognizing a valid presentation of D is asserted.

For the shell applications E_nu contains V, and S(M,M') contains
K_(M'). All are actual groups of Cantor homeomorphisms, so their
actions are faithful. Apply the argument with F empty or F=M'
as appropriate. The A_1 case has F={p}. The germ quotient has
k=1 and therefore does not retain the two-search discriminator.
