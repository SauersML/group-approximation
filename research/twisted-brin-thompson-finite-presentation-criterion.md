---
rg: 2
id: twisted-brin-thompson-finite-presentation-criterion
kind: claim
title: A twisted Brin-Thompson group is finitely presented exactly when the base is, pair-orbits are finite and point stabilizers are finitely generated
distinct_from:
  boone-final-group-finitely-presented: that establishes that one specific HNN tower's final group is finitely presented; this is an if-and-only-if criterion for a family of groups built from actions, and its hypotheses are about orbits and stabilizers rather than about relators.
  finitely-presented-nonsofic-group-exists: that is an existence statement about soficity failing in a finitely presented group; this is a finite-presentation criterion with no approximation content.
  finitely-presented-sofic-non-mf: that is about the approximation properties of the literal group E; this is a criterion for finite presentability of twisted Brin-Thompson groups and names no particular group.
  hnn-extension-finite-presentation-permanence: that is finite-presentation permanence for HNN extensions along finitely generated associated subgroups; this is a criterion for a completely different construction, is an equivalence rather than a permanence, and its hypotheses are about a group ACTION rather than about a subgroup pair.
  boone-higman-thompson-simple-envelope: that produces a computably presented simple envelope from a solvable word problem; this says when a twisted Brin-Thompson group is finitely presented, and supplies simplicity only when the underlying action is faithful.
  chatterji-kassabov-normal-generator-embedding: that is an embedding theorem producing a finitely presented property (T) group; this characterizes finite presentability of a specific construction and involves no embedding and no property (T).
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

For a group `G` acting on a set `S`, the twisted Brin--Thompson group `SV_G`
is finitely presented if and only if

1. `G` is finitely presented,
2. the action of `G` on `S` has finitely many orbits of two-element subsets,
3. the stabilizer in `G` of any element of `S` is finitely generated.

If in addition the action is **faithful**, `SV_G` is simple and contains `G`.

**Verification status.**  Read from source 2026-08-17.  Zaremsky, *Finite
presentability of twisted Brin--Thompson groups*, arXiv:2405.18354 (submitted
28 May 2024, revised 25 November 2024), abstract, verbatim: "$SV_G$ is
finitely presented if and only if we have the following: $G$ is finitely
presented, the action of $G$ on $S$ has finitely many orbits of two-element
subsets of $S$, and the stabilizer in $G$ of any element of $S$ is finitely
generated."

The same criterion is reachable from Fournier-Facio--Wu--Zaremsky,
arXiv:2603.24687v2, Definition 1.3 and Theorem B, also read this session:
type `[A_n]` asks that `G` be of type `F_n`, that `Stab_G(T)` be of type
`F_{n-|T|}` for finite `T ⊆ S`, and that the diagonal action on `S^n` have
finitely many orbits; Theorem B says `SV_G` is "finitely presented iff G↷S is
of type [A_2]".  At `n = 2` those conditions are exactly the three above.

**Attribution correction.**  The external attempt this region came from
attributes the criterion to a "Lemma 5.5" of arXiv:2603.24687v2 phrased in
terms of finite bi-index.  Section 5 of that paper was retrieved on
2026-08-17 and contains no such lemma and no occurrence of "bi-index"; see
`research/artifacts/boone-higman-audit-2026-08-17.md` §A.3.  The criterion is
Zaremsky's.  "Bi-index" is used in this graph as a local name for
`|H \ Gamma / H|`, defined where it is used, and is not a quotation.

## Why the graph carries it

It is the payoff of `boone-higman-via-finite-bi-index-envelope`.  All three
conditions are cheap for the coset action of the Chatterji--Kassabov envelope
on `Gamma/S` except the second, which by
`simple-core-bi-index-counts-coset-action-pair-orbits` is exactly finiteness
of the double coset set — and that is the one thing the construction gives no
control over.
