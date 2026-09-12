---
rg: 2
id: copy-codes-make-one-sided-table-identities-strict
kind: claim
title: Copying one cell is a strict rule pair exactly when the forward table sends that cell to the origin and the reverse table does not send its transpose there
distinct_from:
  smallest-boolean-strict-core-is-a-one-sided-inverse: that is one 2 x 2 table; this is the copy-code criterion for arbitrary label sets, of which that table's strict rules are one instance.
  boolean-core-is-uniform-single-demand-network-coding: that recasts strict data as network codes and proves two filters; this names the simplest family of strict codes and its exact criterion.
artifacts:
  - research/artifacts/boolean-core-alphabets-and-network-coding-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

**ESTABLISHED** by `copy-codes-one-sided-table-identities-proof`.

Take finite label sets `S` and `M` with labels `1`, tables `T_f` on `S x M` and `T_r` on `M x S`,
and labels `s0` in `S` and `m0` in `M`. The code

    mu = pi_(m0),   nu = pi_(s0)

has forward composite `p(s0,m0)` and reverse composite `q(m0,s0)`. So over every alphabet with at
least two symbols, it is strict for `(T_f, T_r)` iff `(s0,m0) T_f (1,1)` while `(m0,s0)` is not
`T_r`-related to `(1,1)`.

At a labelling in a group the premise reads `x_(s0) x_(m0) = 1` and the conclusion
`x_(m0) x_(s0) != 1`, which no group satisfies. So copy codes never give counterexamples: their
automata are shifts. They are the Boolean shadow of one-sided inverses, and every strict
single-coincidence 2 x 2 table except `x_a = x_b` is strict through one of them.

Proof: Lemma 6.1 of the artifact.
