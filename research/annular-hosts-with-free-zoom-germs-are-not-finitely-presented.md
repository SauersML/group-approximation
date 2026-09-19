---
rg: 2
id: annular-hosts-with-free-zoom-germs-are-not-finitely-presented
kind: claim
title: An annular germ host <V, Ĝ> whose germ group at 0^∞ is the free product of the input germs and the zoom is never finitely presented; finite presentation needs relations across depths
distinct_from:
  annular-free-product-germ-hosts-are-not-finitely-presented: that proves the local rigidity lemma and applies it to the ping-pong hosts of residually finite groups, using ping-pong to decide deep triviality; this removes ping-pong, and proves non-finite-presentation for every annular host whose germ group is (Ĝ)_p * <t>, by reducing short relations to germ relations.
  annular-free-factor-germ-extensions-fail-bhm-singfix: that shows the Belk--Hyde--Matucci SingFix certificate fails for free-factor germ groups; this shows the host itself is not finitely presented.
  orbit-preserving-germ-corollary-extensions-of-v-are-rational: that treats germ groups in which the zoom germs are normal, where hosts are rational; this treats germ groups in which the zoom is free.
---

**ESTABLISHED** by `annular-free-zoom-window-equations-proof` (lane proof, elementary;
not reviewed; no priority claimed).

**Setting.** Notation of `rf-groups-have-free-product-germs-over-v`: `C`, `p = 0^∞`,
`A_n = 0^n 1 C`, `α_n`, the zoom `τ` with germ `t`. An *annular host* is
`Γ_ρ = <S_V, ĝ_1, ..., ĝ_k>`, where:
- `G = <g_1, ..., g_k>` and `ρ_n: G -> V` are homomorphisms;
- `ĝ` fixes `p` and acts on `A_n` by `α_n ρ_n(g) α_n^(-1)`.

No ping-pong, residual finiteness or faithfulness is assumed.

**Theorem.**
1. **Short relations are germ relations plus a seed (window lemma).** For every `R`
   there are `B` and finitely many *window words* `u_1, ..., u_r`, each a product of
   `t`-conjugates of the `ĝ_i^(±1)` with total `t`-exponent 0, such that the following
   holds for annular data `ρ'` agreeing with `ρ` on depths at most `2B + 1`. Every
   relation of `Γ_ρ` of length at most `R` holds for `ρ'` exactly when each `u_j`
   evaluates to `1` at every depth `n >= B + 2`, with the offsets in `u_j` read as depth
   shifts. Each `u_j` is trivial in the germ group `(Γ_ρ)_p`.
2. **Free zoom kills finite presentation.** Suppose that `(Γ_ρ)_p = (Ĝ)_p * <t>` and that
   `ρ_n(G) != 1` for infinitely many `n`. Then `Γ_ρ` is not finitely presented.

Item 2 covers every host of `rf-groups-have-free-product-germs-over-v`, whose germ group
is `G * Z`, without the ping-pong analysis.

**What this says for Problem 5.3(12).** Combined with the earlier nodes, annular hosts at
one rational point now have three extreme cases decided at the level of germ relations:
- if the zoom germs are normal, the host is rational
  (`orbit-preserving-germ-corollary-extensions-of-v-are-rational`);
- if the zoom is free, the host is not finitely presented (item 2);
- if the germs ascend under the zoom, finite annular actions force a finite input
  (`annular-free-factor-germ-extensions-fail-bhm-singfix`, item 2).

What is left are germ groups with relations linking depth `n` to depth `n + δ` along a
finite-index subgroup only. That is the virtual endomorphism shape.

**Lesson for general BH.**
- For Thompson-like hosts, finite presentation is a statement about the germ group's
  relations across depths. Short relations of the host reduce to finitely many germ
  relations plus a finite seed.
- If no germ relation crosses depths, the deep data can be changed freely, and the host
  is not finitely presented. So the host must hold the input's algorithm in relations
  that cross depths, of the form `t^(-δ) u t^δ = v`, not in data stored level by level.
- This test needs only the germ group and a seed, so it can be run on any proposed host
  before any finiteness machinery. The design question for Boone--Higman becomes:
  which finitely presented germ groups `<H, t | cross-depth relations>` can be realized
  on annuli with a unique deep solution? Virtual endomorphisms give one answer. A
  machine whose transition rule is a cross-depth relation would give another, and
  has not been attempted.
