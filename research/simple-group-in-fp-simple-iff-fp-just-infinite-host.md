---
rg: 2
id: simple-group-in-fp-simple-iff-fp-just-infinite-host
kind: claim
title: An infinite simple group, finitely generated or not, embeds in a finitely presented simple group iff it maps nontrivially to a finitely presented group that is just-infinite above its image
distinct_from:
  boone-higman-iff-fp-just-infinite-hosts: that is a class-level equivalence for finitely generated decidable inputs, proved through the Thompson simple envelope; this is a per-input equivalence for one simple group of any cardinality, with no word-problem or finite-generation hypothesis, and with a homomorphism in place of an embedding.
  just-infinite-over-simple-subgroup-gives-fp-simple-host: that is the structure lemma for a simple subgroup of a just-infinite host; this is the resulting two-sided criterion for embeddability of the simple group itself.
---

**ESTABLISHED** by `simple-group-in-fp-simple-iff-fp-just-infinite-host-proof`
(a direct corollary of the structure lemma; not independently reviewed).

## Statement

Let `S` be an infinite simple group. `S` need not be finitely generated. The
following are equivalent.

1. `S` embeds in a finitely presented simple group.
2. There are a finitely presented group `Γ` and a nontrivial homomorphism
   `ρ : S -> Γ` such that every nontrivial normal subgroup of `Γ` contained in
   the normal closure `<<ρ(S)>>^Γ` has finite index in `Γ`. This holds, for
   example, when `Γ` is just-infinite.

When (2) holds, `S` embeds in a finitely presented simple group `T` with
`T^k` a finite-index normal subgroup of `Γ` for some `k >= 1`.

## Use for the root

With `sl-odd-q-simple-inputs-for-gl-n-q-root`, apply this to `S = SL_m(Q)` for
odd `m`. The host in (2) may have finite quotients (it is only just-infinite
above the image), and the map need only be nontrivial. This is the target
`sl-odd-q-has-fp-just-infinite-host`, equivalent to the root. The host must not
be residually finite: a residually finite group has no infinite simple subgroup.
That is O1 again, in its sharpest form.
