---
rg: 2
id: gkp-free-generalized-wreath-soficity-citation
kind: route
title: Gao--Kunnawalkam Elayavalli--Patchell Theorem 3.7, free case, read from arXiv:2401.04945v3
target: gkp-free-generalized-wreath-soficity
requires: []
---

**Literature import.** Gao, Kunnawalkam Elayavalli, Patchell, *Soficity for
group actions on sets and applications*, arXiv:2401.04945v3. The HTML of v3
was fetched on MSI on 2026-09-12 and the statements below were extracted
from it verbatim, with the math markup flattened.

**Definition 2.1** (standing hypotheses). "Let G be a countable discrete
group, X be a countable discrete set, α : G ↷ X be an action, A be a finite
set, φ : G → Sym(A) be a map (not necessarily a homomorphism)". Parts
(1)--(3) define unital, (F, ε)-multiplicative, and (F, E, ε)-orbit
approximation. The action α is sofic if for all finite F ⊆ G, E ⊆ X and
ε > 0 there is a finite set A and a unital, (F, ε)-multiplicative map
φ : G → Sym(A) that is an (F, E, ε)-orbit approximation of α.

**Definition 3.2.** "Let G, H be groups, α : H ↷ X be an action on a set,
and A ≤ G be a subgroup. Then H acts on the amalgamated free product
∗_A^{x∈X} G_x where G_x are copies of G by permuting G_x according to α.
Denote this action by β. Then the amalgamated free generalized wreath
product ... is given by G ≀^{∗_A}_α H = (∗_A^{x∈X} G_x) ⋊_β H. In case
A = {1_G}, we shall call this group the free generalized wreath product and
denote it by G ≀^∗_α H."

**Theorem 3.7.** "Let H be a sofic group, α : H ↷ X be a sofic action,
A ≤ G be an inclusion of countable discrete groups s.t. the amalgamated free
product of any countably many copies of G over A is sofic. Then the
amalgamated free generalized wreath product G ≀^{∗_A}_α H is sofic. In
particular, if G, H are sofic groups and α : H ↷ X is a sofic action, then
the free generalized wreath product G ≀^∗_α H is sofic, and under the same
conditions, if we in addition have an amenable subgroup A of G, then the
amalgamated free generalized wreath product G ≀^{∗_A}_α H is sofic."

**Match with the target.** The target is the "In particular" clause of
Theorem 3.7 with the paper's `G` renamed `K`: `K` and `H` countable sofic,
`α : H ↷ X` a sofic action on a countable set (the setting of
Definition 2.1), and `K ≀^∗_α H = (∗_{x∈X} K_x) ⋊ H` as in Definition 3.2
with `A = {1}`. Nothing is added. The target's remark about Corollary 3.10
(the hyperlinear analogue, which needs `α` sofic and `K, H` hyperlinear) was
also checked against the same text. It is not part of the imported claim.

**Not verified here.** The journal version (Res. Math. Sci. 12 (2025), 48)
was not consulted. Theorem numbers above are those of arXiv v3.

**Effect on the graph.** Two peer routes were blocked only on this import:
`coset-difference-cocycle-embeds-double-proof`, into
`sofic-coset-action-makes-amalgam-double-sofic`, and
`free-lamp-double-and-sofic-action-proof`, into
`one-kun-thom-compressor-is-relatively-embeddable`. Their other premises
were already established. Before landing, both derivations were re-read.
Checked: the difference cocycle identity (CDC1); the free basis of the
fold kernel read off the two-vertex quotient graph (CDC4); the Nielsen
change of basis (CDC5); the Tietze rewriting (FLD4)--(FLD6); and
restriction of a sofic action to an invariant orbit, which is immediate
from Definition 2.1.
