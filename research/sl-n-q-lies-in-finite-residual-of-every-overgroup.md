---
rg: 2
id: sl-n-q-lies-in-finite-residual-of-every-overgroup
kind: claim
title: For n >= 2 every finite-index subgroup of every group containing GL_n(Q) contains SL_n(Q), and the finite residual of GL_n(Q) is exactly SL_n(Q)
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that is the open embedding problem; this is the exact form of its obstruction O1, identifying which part of GL_n(Q) every profinite topology misses.
  lifts-add-no-unipotent-divisibility: that rules out central and covering lifts of Q-free groups as hosts; this says what every finite quotient of every host does to GL_n(Q).
---

**ESTABLISHED** through `sl-n-q-lies-in-finite-residual-of-every-overgroup-proof`.
Not independently reviewed. The argument is elementary and no priority is claimed.

## Statement

Let `n >= 2` and let `H` be any group containing `GL_n(Q)`.

1. Every subgroup of finite index in `H` contains `SL_n(Q)`.
2. Every homomorphism from `H` to a residually finite group is trivial on
   `SL_n(Q)`. Its restriction to `GL_n(Q)` factors through
   `det : GL_n(Q) -> Q^x`.
3. The finite residual of `GL_n(Q)` (the intersection of its subgroups of finite
   index) is exactly `SL_n(Q)`. So the image of `GL_n(Q)` in the profinite
   completion of any overgroup is abelian: it is a quotient of `Q^x`.

## What it says about unions and hosts

- `GL_n(Q) = ⋃_m GL_n(Z[1/m!])`, since every rational number has a denominator
  dividing some `m!`. Each stage is a finitely generated linear group, hence
  residually finite (Mal'cev), and each has many congruence quotients. By (3)
  none of the quotients that are nontrivial on `SL_n(Z[1/m!])` survives in the
  union, nor in any group containing it. A construction that certifies an
  embedding of the stages through finite quotients (congruence subgroups, level
  stabilizers of a rooted tree, residual finiteness of intermediate hosts)
  cannot be passed to the limit.
- This is the exact content of the root's obstruction O1. Every intermediate
  group in a route to `gl-n-q-embeds-in-fp-simple-group` has infinite finite
  residual, which contains all of `SL_n(Q)`.
- Only the part `SL_n(Q)` is invisible. The quotient `GL_n(Q)/SL_n(Q) ~ Q^x`
  is residually finite, so a host can still separate elements of `GL_n(Q)` with
  different determinants by finite quotients.
