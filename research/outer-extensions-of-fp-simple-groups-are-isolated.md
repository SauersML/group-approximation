---
rg: 2
id: outer-extensions-of-fp-simple-groups-are-isolated
kind: claim
title: An extension of a finitely presented nonabelian simple group by a finitely presented group acting faithfully by outer automorphisms is isolated
distinct_from:
  fp-simple-groups-are-isolated: that is the trivial extension; this allows a nontrivial finitely presented quotient that embeds in the outer automorphism group, so the extension need not be simple.
  decidable-groups-embed-in-outer-extensions-of-fp-simple-groups: that is the open universality statement asking every decidable group to sit inside such an extension; this is the theorem that such an extension is isolated.
---

**ESTABLISHED** by `outer-extension-isolated-via-centralizer-argument` (elementary).

Terms as in `fp-simple-groups-are-isolated`, from Cornulier--Guyot--Pitsch,
arXiv:math/0511714 (TeX source on MSI,
`/scratch.global/sauer354/bh-isolated/math_0511714.tex`).

**Statement.** Let `1 → S → I → Q → 1` be an extension of groups such that
- `S` is finitely presented, simple and nonabelian,
- `Q` is finitely presented, and
- the conjugation homomorphism `Q → Out(S)` is injective.

Then `I` is isolated. In particular, if `φ: Q → Aut(S)` is injective with
`φ(Q) ∩ Inn(S) = 1`, then `S ⋊_φ Q` is isolated, and so every finitely generated
subgroup of `Q` embeds in an isolated group.

**Relation to the source.** This is a special case of CGP Corollary
`cor ext_out` (lines 1147–1155), quoted verbatim: "Consider an extension of
groups 1→K→G→Q→1. Suppose that K is G-finitely discriminable, and that the
natural homomorphism Q→Out(K) is injective. Then G is finitely
discriminable." Combined with their Proposition (lines 554–557), and with the
closure of finite presentation under extensions stated in their proof of
Corollary `cor extensions_fd` (lines 1143–1145: "the class of finitely
presented groups is closed under extensions"), it gives the statement. The
route proves the simple case directly, without CGP's Theorem
`thm stabextension`.

**Novelty.** None claimed; it is CGP's corollary specialized. The node exists
so the outer-extension route to `every-decidable-group-embeds-in-an-isolated-group`
can cite it.
