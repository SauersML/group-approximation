---
rg: 2
id: regular-enumerations-can-make-near-shift-free-product
kind: claim
title: Generic regular enumerations make the near shift group a free product and decidable inputs admit effective such enumerations
artifacts:
  - research/artifacts/boone-higman-free-shift-presentation-obstruction-2026-09-08.md
---

**ESTABLISHED** by `regular-free-shift-fresh-trajectory-proof`, an
elementary back-and-forth construction. Referee a PASS
(`research/artifacts/gq-referee-a-free-shift-houghton-envelopes-and-regular-enumerations.md`,
afbbd1818). Status line added by bh-map, 2026-09-18.

A finite prescription fixes finitely many values of both nu and
nu^-1, so the basic open sets of the topology below are given by
finite partial bijections (referee a, N3).

Let P be a countably infinite group. For nu:P->N, transport its
left regular action to lambda(P) and let s be the cofinite shift
n->n+1. The set of enumerations for which the canonical surjection

    P * <s> -> R_nu=<lambda(P),s> <= NearSym(N)

is injective is a dense comeagre subset of the space of bijections
P->N with the topology of finite prescriptions.

If P is finitely generated with a supplied word-problem algorithm,
such a nu and its inverse on word representatives can be computed,
extending any given consistent finite prescription. The construction
is uniform in that algorithm and prescription. No finite presentation
of the associated Cantor shell envelope is supplied by genericity.
