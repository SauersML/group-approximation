---
rg: 2
id: kun-thom-stabilizer-not-co-amenable
kind: claim
title: The Kun--Thom lamp stabilizer is never co-amenable, so no dividend transfers through it
distinct_from:
  no-invariant-mean-on-coset-space: that is the general Kazhdan theorem, stated for an arbitrary subgroup of infinite index; this is its instantiation at the Kun--Thom pair, where the infinite index is not a hypothesis one may choose but a consequence of infranormality plus non-normality.
  amenable-rep-of-kazhdan-has-fd-subrep: that is a representation-theoretic dichotomy about amenable representations of a Kazhdan group; this is about invariant means on a coset space and about which transfer theorems can be applied to the lamp action.
artifacts:
  - research/artifacts/sofic-dividends-audit-2026-08-17.md
---

Let `Gamma <= G` be a Kun--Thom pair: `Gamma` infranormal but not normal in
`G`, both with property (T), as in `kun-thom-nonsofic-wreath`.  Then `Gamma`
is **not** co-amenable in `G` — there is no `G`-invariant finitely additive
probability measure on the lamp site space `X = G/Gamma`.

No hypothesis on the index is needed: infranormal-and-not-normal already
forces `[G : Gamma]` infinite
(`infranormal-nonnormal-has-infinite-compression-orbit`), and a Kazhdan group
has no invariant mean on an infinite-index coset space
(`no-invariant-mean-on-coset-space`).

## What this closes

The standard sofic-approximation proofs of several dividends do not apply
to the nonsofic wreath product W. One proposed repair is to find a sofic
subgroup through which the
conclusion transfers, and the transfer theorems in that literature want the
subgroup to be co-amenable.  Inside `W = N semidirect G` the natural
candidate is the sofic base `G`, and the natural site-space transfer runs
through the stabilizer `Gamma`; this claim says the stabilizer route is
unavailable, permanently and for structural reasons, not for want of a better
Folner sequence.

An external audit ingested on 2026-08-17 proposed exactly that transfer.  Its
own Proposition 7.1 is this graph's `no-invariant-mean-on-coset-space`, and
its application step assumed the infinite index that
`infranormal-nonnormal-has-infinite-compression-orbit` proves.

This excludes one proposed proof of `kun-thom-wreath-stably-finite`.
The radical-containment proposal fails separately at
`modular-radical-does-not-lift-direct-finiteness`. Neither restriction is
exhaustive: `rf-lamp-permutational-wreaths-satisfy-stable-finiteness` now
establishes the all-field result through finite marked-site tensors and
split local-corner extensions, without a mean on the site space.
