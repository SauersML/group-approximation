---
rg: 2
id: no-proper-character-groups-avoid-amenable-orbit-full-groups
kind: claim
title: Simple groups without proper characters, including every purely infinite alternating full group and Thompson's T, act trivially in amenable orbit full groups
distinct_from:
  stabilizer-rigid-groups-avoid-amenable-orbit-full-groups: That proves the exclusion for a group with only trivial and regular characters and applies it to V and groups containing V; this imports the two general sources of that hypothesis (Dudko--Medynets compressible actions, Gardella--Tanner purely infinite groupoids), which reach Thompson-like groups that need not contain V, and verifies Thompson's T.
  amenable-full-group-forces-invariant-measure: That shows groups realizing moving bisections of compressible groupoids are not amenable; this consumes it for non-amenability and adds the character obstruction to realizations inside amenable orbit full groups.
---

**ESTABLISHED.**

**Setting** (as in `amenable-orbit-full-group-subgroups-are-sofic`). `Lambda` is
countable amenable and acts essentially freely, preserving `mu`, on a standard
probability space `X`. `W(Lambda ~ X)` is the group of Borel bijections with
finite-range cocycles into `Lambda`.

A group *has no proper characters* (Dudko--Medynets, arXiv:1212.1230, Definition
`DefinitionCompressible`) if its only indecomposable characters are the identity and
the regular one.

**Theorem.**
1. **General.** Let `Gamma` be a countable infinite simple non-amenable group with no
   proper characters. Then every homomorphism `rho : Gamma -> W(Lambda ~ X)` acts
   trivially almost everywhere.
2. **Compressible actions** (Dudko--Medynets Theorem 2.9). Every countable simple
   group with a compressible action on an infinite regular Hausdorff space has no
   proper characters. Item 1 applies to the non-amenable ones.
3. **Purely infinite groupoids** (Gardella--Tanner). Let `G` be a minimal, purely
   infinite, essentially principal Cantor groupoid. Then `A(G)` is infinite, simple
   and non-amenable and has no proper characters, so item 1 applies. This covers
   the Thompson-like finitely presented simple groups that are alternating full
   groups of such groupoids, for example `nV_(2,r)` and `V_(k,r)` for even `k`
   (Gardella--Tanner, TeX lines 1840), whether or not they contain `V`.
4. **Thompson's `T`.** Assume `T` is simple (classical, Cannon--Floyd--Parry, Section
   5; theorem number not re-read). Then `T` has no proper characters and is not
   amenable, so item 1 applies. In particular `T` embeds in no topological full group
   `[[Lambda ~ X]]` of an amenable group with an essentially free invariant measure of
   full support.

5. **Groups containing `T`.** Under the same assumption on `T`, no simple group
   containing `T` has a nontrivial realization. For instance, Lodha's finitely presented
   simple circle group (arXiv:1710.06220) contains `T`.

**Where this leaves the certificate.** Every Thompson-like finitely presented simple
group recorded in the graph is excluded from
`fp-simple-group-in-amenable-orbit-full-group`, whether through characters (this node
and `stabilizer-rigid-groups-avoid-amenable-orbit-full-groups`) or through containment
of `V`. Gardella--Tanner (TeX line 1919) ask whether, for étale essentially principal
Cantor groupoids, proper characters of `A(G)` correspond exactly to invariant
probability measures. Our certificate is the soficity face of that dichotomy: invariant
measures give sofic subgroups, and their absence gives character rigidity, which blocks
realizations.

Proof: `no-proper-character-groups-avoid-orbit-full-groups-proof`.
