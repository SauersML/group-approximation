---
rg: 2
id: core-element-normal-generation-upgrade-proof
kind: route
title: Push the normal closure through the simple core, then through the commutator subgroup
target: every-nontrivial-core-element-normally-generates-the-envelope
requires: []
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

**Clause 1.**  Let `1 != t in S`.  Simplicity of `S` gives `S = <<t>>_S`, and
`<<t>>_S <= <<t>>_Gamma`, so `s in <<t>>_Gamma`.  The normal closure of `s`
is the smallest normal subgroup containing `s`, so

    Gamma = <<s>>_Gamma  <=  <<t>>_Gamma  <=  Gamma ,

forcing equality.

**Clause 2.**  Assume `S` infinite.  An infinite simple group is nonabelian
(an abelian simple group is cyclic of prime order), and a nonabelian simple
group is perfect, because `[S,S]` is a nontrivial normal subgroup of `S`.
Hence `s in [S,S] <= [Gamma,Gamma]`.  The commutator subgroup is normal and
contains a normal generator of `Gamma`, so `[Gamma,Gamma] = Gamma`.

**Clause 3.**  By
`proper-normal-subgroups-miss-the-normally-generating-core`, every proper
`N <| Gamma` has `N ∩ S = 1`, so `S` embeds in `Gamma/N`.  An infinite
subgroup forces an infinite group.

## The infinite core costs nothing

Feed `G × Z` rather than `G` to `boone-higman-thompson-simple-envelope`.  It
is finitely generated, has solvable word problem (decide each coordinate
separately), and contains `G`.  The resulting simple envelope contains a copy
of `Z`, hence is infinite, and it still contains `G` through
`G <= G × Z`.  Every downstream statement is about `G`'s embedding, so the
extra factor is invisible past this point.

## A remark on clause 3 that is easy to get backwards

Clause 3 says proper quotients are infinite; it does **not** say `Gamma` is
just infinite, nor that proper quotients are simple, nor that there are few
of them.  It says only that the infinite core survives each one, which is
already the content of the previous claim.
