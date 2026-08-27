---
rg: 2
id: fournier-facio-torsion-free-skeleton
kind: claim
title: The Fournier-Facio torsion-free group has a simple group inside its compression defect
distinct_from:
  kazhdan-clifford-non-mf-construction: that construction builds the compression data by hand from a self-embedding and marks a Clifford sign; this claim records a published torsion-free group that already carries the compression data, with a simple group in the defect and no mark at all.
  infinite-order-central-mark-group: that claim asks for a torsion-free group with an infinite-order *central* mark; this one supplies a torsion-free group whose defect contains a *simple* subgroup, which is the input the normal-Kazhdan branch wants.
  torsion-free-countable-non-mf: that claim asserts a torsion-free group is not MF; this one asserts nothing about MF and only records the group-theoretic structure of a published nonsofic example.
  torsion-free-finitely-presented-non-mf: that root is the non-MF existence statement; this claim is one of its inputs and is already established.
  torsion-free-higman-embedding: that claim is an embedding theorem for recursively presented groups; this one is a concrete published construction and its compression core.
---

Fournier-Facio, *A torsion-free non-sofic group* (arXiv:2608.02025, 3 August
2026), Theorem 1.3 and Section 2, constructs a **finitely presented,
torsion-free** group `G` with property (T) together with:

- `Gamma = pi(P) <= G` with property (T), infinite, and
  `G = <Gamma, t_1, t_2>` with `t_i Gamma t_i^-1 <= Gamma`;
- a finitely presented simple torsion-free group `S` (Burger--Mozes or
  Hyde--Lodha) with `pi|_S` injective, and `J = t_1^-1 pi(S) t_1` satisfying
  `[Gamma, J] = 1`, `Gamma cap J = 1`, and `t_1 J t_1^-1 = pi(S) <= Gamma`.

**Conjugation convention.**  `J` is `pi(S)` pushed *out* of `Gamma` by the
inverse stable letter, not into it.  The direction is forced: `t_1` compresses,
`t_1 Gamma t_1^-1 <= Gamma`, so `t_1 pi(S) t_1^-1` would lie inside `Gamma`,
and then `[Gamma, J] = 1` together with `Gamma cap J = 1` would give `J = 1`
and the claim would be vacuous.  This matches the formalization, whose root is
`c = u^-1 s u` with `s` in the simple factor and `u c u^-1 = s`.

Consequently `G` carries a `KazhdanCompressionCore` with `iota` the
inclusion of `Gamma`, `t = t_1`, and `c` any element of `J`; and — this part
is not in the paper — **its compression defect contains a copy of `S`**:

    S' := t_1 J t_1^-1 = pi(S)  is a copy of S inside Gamma, and
    S' <= defectNormal.

So the published torsion-free group already satisfies every hypothesis of
`normal-kazhdan-defect-non-mf` except one: the copy of `S` sitting in the
defect must be enlarged to a **normal** subgroup of `G` with property (T).
That single gap is isolated as `defect-normally-generates-torsion-free-quotient`.

The torsion-freeing device, for the record, is not one trick.  Every
ingredient is chosen torsion-free from a menu that already exists — a
universal finitely presented torsion-free group (Higman; Belegradek--
Szczepanski; Chiodo), a finitely presented simple torsion-free group, a
torsion-free hyperbolic Kazhdan group (random groups at density) — and both
gluing steps have published torsion-preservation clauses: Osin's small
cancellation over relatively hyperbolic groups (Theorem 2.4.5) and Hull's
common-quotient theorem (Theorem 7.1(e)).  What carried the torsion in the
OpenAI example was the non-LEF witness, Thompson's `V`; Fournier-Facio
replaces it by a torsion-free finitely presented simple group.
