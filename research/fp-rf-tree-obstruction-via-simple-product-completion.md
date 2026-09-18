---
rg: 2
id: fp-rf-tree-obstruction-via-simple-product-completion
kind: route
title: A finitely presented residually finite group with an open simple product in its completion acts on no regular rooted tree
target: some-fp-rf-group-acts-on-no-regular-rooted-tree
requires:
  - fp-rf-group-with-simple-product-completion
  - simple-product-completions-block-regular-tree-actions
---

Let `Γ` be the group given by `fp-rf-group-with-simple-product-completion`. It
is finitely presented and residually finite, and its completion has an open
subgroup of the form `(SP1)` with each order bound met by only finitely many
factors. By `simple-product-completions-block-regular-tree-actions`, `Γ` embeds
in `Aut(T_d)` for no `d >= 2`. That is the target. `∎`

This route is independent of `fp-rf-tree-obstruction-via-unbounded-torsion`.
Its group need not have torsion, and a group with torsion primes bounded by a
small number would still qualify.
