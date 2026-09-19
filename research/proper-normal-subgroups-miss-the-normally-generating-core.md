---
rg: 2
id: proper-normal-subgroups-miss-the-normally-generating-core
kind: claim
title: If a simple subgroup contains a normal generator of the ambient group, every proper normal subgroup meets it trivially
distinct_from:
  countable-group-embeds-in-two-generator-simple-group: that is an embedding theorem producing simple groups; this takes a simple subgroup as given and deduces that the ambient group's proper normal subgroups all avoid it, constructing nothing.
  finite-infranormal-subgroup-is-normal: that is about finite subgroups and their normalizers; this is about intersections of arbitrary proper normal subgroups with a simple subgroup that is typically infinite, and uses no finiteness anywhere.
  mf-finite-normal-tracially-visible: that says finite normal subgroups of an MF group are visible to traces, an approximation statement about finite subgroups; this says proper normal subgroups meet a simple core trivially, with no trace, no MF hypothesis and no finite subgroup.
  simple-lamp-radical-one-relation: that computes the MF radical of one concrete wreath group and shows it is the normal closure of a single lamp; this is a general lattice statement about ANY simple subgroup containing a normal generator, has no radical, no approximation property and no particular group in it.
  defect-normally-generates-torsion-free-quotient: that makes one specific compression defect normally generate a Kazhdan subgroup of a constructed quotient; this starts FROM a normal generator and deduces that the whole proper normal lattice avoids the simple subgroup containing it.
  boone-higman-thompson-simple-envelope: that is an embedding theorem producing a simple envelope; this is a lattice consequence of having such a core sitting inside a larger group, and it constructs nothing.
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

Let `S` be a nontrivial simple group with `S <= Gamma`, and suppose some
`1 != s in S` normally generates the ambient group:

    Gamma = <<s>>_Gamma .

Then for every normal `N <| Gamma` with `N != Gamma`,

    N ∩ S = 1 ,

so the quotient map `Gamma -> Gamma/N` restricts to an embedding of `S`.

If in addition `Gamma` is finitely generated, a maximal proper normal
subgroup `M` exists, and `Gamma/M` is then a simple group containing an
isomorphic copy of `S`.

## Why this is the whole content of the near-solution

Applied to the composite of `boone-higman-thompson-simple-envelope` and
`chatterji-kassabov-normal-generator-embedding` it gives, for every finitely
generated `G` with solvable word problem, a chain

    G  <=  S  <=  Gamma  -->>  Gamma/M

with `Gamma` finitely presented and property (T), `Gamma/M` simple, and `G`
still embedded at the end.  **Every** maximal proper normal quotient works;
there is no choice to make and no risk of the quotient killing the group one
is trying to keep.  That is unusual, and it is what makes the remaining gap
so narrow: only finite presentability of `Gamma/M` is missing, which by
`fp-quotient-iff-kernel-finitely-normally-generated` is
exactly finite normal generation of `M`.

## What it does not say

It does **not** say `Gamma` is relatively simple.  Two proper normal
subgroups `N_1, N_2` both miss `S`, but nothing here forbids
`N_1 N_2 = Gamma`, so there need be no largest proper normal subgroup and no
canonical simple quotient.  Anyone reading "all proper normals avoid the same
core" as "the proper normals form a directed family" is reading in a
conclusion that is not proved.

It also does not narrow the *lattice*: it re-describes it.  By this claim the
proper normal subgroups of `Gamma` are precisely the normal subgroups
invisible on `S`, which is a clean reformulation and not a finiteness
statement about any of them.
