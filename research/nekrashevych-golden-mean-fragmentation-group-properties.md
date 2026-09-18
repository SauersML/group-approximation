---
rg: 2
id: nekrashevych-golden-mean-fragmentation-group-properties
kind: claim
title: Nekrashevych's golden-mean group F is periodic, of intermediate growth and equal to its own topological full group, and every fragmentation of a minimal dihedral action is amenable
distinct_from:
  contracting-rsg-torsion-subgroups-are-residually-finite: that is a claim about all finitely generated torsion subgroups of contracting rational similarity groups; this imports the properties of one periodic group F and of the fragmentation class it belongs to, with no host.
  almost-automorphism-torsion-subgroups-are-rf: that proves residual finiteness of torsion in almost automorphism groups; this imports facts about Nekrashevych's fragmentation groups, which are not residually finite.
---

**ESTABLISHED** (literature import, `nekrashevych-golden-mean-fragmentation-group-properties-citation`).

Let `X = {1,2}^ω` and let `F = <a_i, b_i, c_i, d_i : i = 0,1,2>` be the group of homeomorphisms of `X`
defined in §7 ("Fragmenting the golden mean dihedral group") of V. Nekrashevych, *Palindromic subshifts
and simple periodic groups of intermediate growth*, arXiv:1601.01033. Then:

1. `F` coincides with its topological full group `full(F, X)`. It is periodic and of intermediate growth.
   Its derived subgroup `[F,F]` is simple and of finite index in `F`.
2. `F/[F,F]` is a quotient of `(Z/2Z)^9`.
3. Every fragmentation of a minimal action of the infinite dihedral group on a Cantor set embeds in the
   topological full group of a minimal `Z`-action on a Cantor set, and so it is amenable.
4. For a group `G` acting on a Cantor set `X`, `full(G, X)` and `alt(G, X)` are defined as in the
   citation. In particular, whenever `g_1(U), ..., g_n(U)` are pairwise disjoint for a nonempty clopen
   `U` and `g_i ∈ G`, the rule `α -> h_α` is a monomorphism `Sym_n -> full(G, X)`, and
   `h_α ∈ alt(G, X)` for every `α ∈ Alt_n`.
5. As a status remark, the paper says that all known examples of finitely generated infinite groups of
   bounded exponent are non-amenable (2016).
