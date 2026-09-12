---
rg: 2
id: finite-edge-hnn-closures-cannot-finish-the-nonce-atlas
kind: claim
title: Finite-edge HNN chord closures cannot finish the no-CE signed atlas
artifacts:
  - research/artifacts/signed-hecke-common-type-normalization-2026-08-20.md
distinct_from:
  cycle-closure-cannot-remain-in-the-join-tree-group: that rules out completing the atlas without enlarging the acyclic group; this also rules out every finite iteration of HNN extensions over finite associated subgroups.
  finite-character-idempotents-have-exact-hnn-transport: that proves such a stable letter transports each matched local character piece exactly; this proves that iterating only those locally exact transports stays in a hyperlinear group class and cannot finish the source.
---

Start with the residually finite join-tree group `(CJG1)`.  Every finite
iteration of HNN extensions whose associated subgroups are finite is
residually finite.  In particular, repeatedly applying `(FHI2)` to transport
finite-subgroup character idempotents produces a residually finite, hence
hyperlinear, final group.

Therefore no such finite-edge Bass--Serre construction can complete the
compatible projection atlas of the fixed no-CE BCS.  If it did, the canonical
signed-corner trace would pull back to a Connes-embeddable BCS trace.  The
first genuinely decisive chord operation must instead use an infinite
associated subgroup, a non-Bass--Serre relation, or another extension for
which residual finiteness is not inherited from the acyclic base.

This is stronger than the observation that one stable letter gives conjugacy
rather than equality: even a fully piecewise family of stable letters that
does produce the desired additive equality locally cannot finish the global
no-CE atlas while every edge group remains finite.
