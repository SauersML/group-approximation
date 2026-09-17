---
rg: 2
id: thompson-f-is-autostackable
kind: claim
title: Thompson's group F is autostackable (Corwin–Golan–Hermiller–Johnson–Šunić)
distinct_from:
  thompson-f-is-automatic: that is the open claim that F is automatic; this is the established weaker property, autostackability, which contains every group that is asynchronously automatic over a prefix-closed normal form and every group with a finite complete rewriting system
  thompson-f-guba-sapir-normal-forms-not-automatic: that says one natural normal form is not an automatic structure; this says F carries a bounded regular convergent prefix-rewriting system
---

**ESTABLISHED by citation** (route `thompson-f-is-autostackable-citation`).

Richard Thompson's group `F` is autostackable. It has a finite generating set with
a bounded regular convergent prefix-rewriting system.

Autostackability (Brittenham–Hermiller–Holt) asks for a prefix-closed set of normal
forms, one for each group element, and a bounded flow function. The flow function
sends each directed edge of the Cayley graph that is not on the normal form tree to
a path with the same endpoints, and the flow must be well-founded. The graph of the
flow function must be a regular language. The class contains all groups that are
asynchronously automatic over a prefix-closed normal form set, and all groups with
finite complete rewriting systems (`thompson-f-is-autostackable-citation`).
