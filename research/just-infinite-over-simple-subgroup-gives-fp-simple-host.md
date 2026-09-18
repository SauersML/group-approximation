---
rg: 2
id: just-infinite-over-simple-subgroup-gives-fp-simple-host
kind: claim
title: A finitely presented group that is just-infinite above an infinite simple subgroup is virtually a power of a finitely presented simple group containing it
distinct_from:
  cornulier-isolated-hji-groups-are-not-elementary-sofic: that concerns isolated hereditarily just-infinite groups in the space of marked groups and their soficity; this is a purely algebraic structure lemma, with no hereditary hypothesis, turning just-infiniteness of a finitely presented host into a finitely presented simple host.
  grigorchuk-group-is-just-infinite-torsion-not-fp: that is one residually finite just-infinite group that is not finitely presented; this lemma is about just-infinite hosts that contain an infinite simple subgroup, which are exactly the non-residually-finite ones it can use.
  boone-higman-thompson-simple-envelope: that produces a computably presented simple envelope; this upgrades any finitely presented just-infinite envelope of a simple group into a finitely presented simple one, and produces no envelope by itself.
---

**ESTABLISHED** through `just-infinite-over-simple-subgroup-gives-fp-simple-host-proof`.

Let `Γ` be a finitely generated group and `S ≤ Γ` an infinite simple subgroup. Put
`N = <<S>>^Γ`. Assume that **every nontrivial normal subgroup of `Γ` contained in
`N` has finite index in `Γ`**. This holds, for example, when `Γ` is just-infinite.

Then there are a finitely generated infinite simple group `T`, an integer `k ≥ 1`
and a finite-index normal subgroup `R ◁ Γ` such that

1. `R ≅ T^k`, and `R` has no proper finite-index subgroup;
2. `S ≤ R`, and some coordinate projection `R → T` is injective on `S`;
3. `T` is finitely presented **if and only if** `Γ` is finitely presented.

In particular, if `Γ` is finitely presented then `S` embeds in the finitely
presented infinite simple group `T`.

**What this denies.** Earlier Boone–Higman routes looked for hosts with no finite
quotients, and they built simplicity element by element. This lemma lets the host
have as many finite quotients as it likes. It needs only a normal-subgroup
dichotomy for the host, as delivered by normal subgroup theorems, plus one
simple subgroup. Finite presentability then passes to a retract of a
finite-index subgroup at no cost. Compare Caprace, arXiv:1709.05949, Proposition
1.1: "Let G be a hereditarily just-infinite group. Either G is residually finite,
or the intersection G(∞) of all its subgroups of finite index is simple and of
finite index in G." That result needs the hereditary hypothesis. This lemma drops
it, and pays with the power `T^k` and the simple subgroup.

DERIVATION
just-infinite-over-simple-subgroup-gives-fp-simple-host-proof
