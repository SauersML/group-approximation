---
rg: 2
id: proper-normal-subgroups-miss-the-normally-generating-core-proof
kind: route
title: Simplicity forces the intersection to be trivial or everything, and everything contradicts properness
target: proper-normal-subgroups-miss-the-normally-generating-core
requires: []
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

Let `N <| Gamma` be proper.  Then `N ∩ S` is normal in `S`, so by simplicity
it is `1` or `S`.  Suppose it is `S`.  Then `S <= N`, so `s in N`, and since
`N` is normal it contains the whole normal closure:

    Gamma = <<s>>_Gamma <= N ,

contradicting `N != Gamma`.  Hence `N ∩ S = 1`.  The restriction of the
quotient map to `S` has kernel `N ∩ S = 1`, so it is injective.

## Existence of a maximal proper normal subgroup

Let `P` be the set of proper normal subgroups of `Gamma != 1`, ordered by
inclusion, and let `C ⊆ P` be a chain with union `U`.  A union of a chain of
subgroups is a subgroup, and it is normal because each member is.

`U != Gamma`: write `Gamma = <x_1,…,x_m>` and suppose `U = Gamma`.  Each
`x_i` lies in some `N_i in C`.  The finitely many `N_1,…,N_m` are linearly
ordered by inclusion, so one of them contains all the others and hence every
`x_i`; that member equals `Gamma`, contradicting `N_i in P`.

So every chain has an upper bound in `P`, and Zorn gives a maximal element
`M`.  Maximality among *proper normal* subgroups is by definition simplicity
of `Gamma/M`.  The first part then embeds `S` into `Gamma/M`.

## Where finite generation is used, and where it is not

Finite generation is used **only** to produce `M`, and only through the
step "finitely many members of a chain have a largest".  It is not used
anywhere in `N ∩ S = 1`, which holds for every proper normal subgroup of
every group satisfying the hypotheses.

This is worth separating because the finitely presented envelope of
`chatterji-kassabov-normal-generator-embedding` is finitely generated for
free, so the Zorn step is never in question here — but the trivial-
intersection half is the part that is quoted downstream, and it needs no
finiteness at all.
