---
rg: 2
id: simple-inputs-have-fp-essential-shell-germ-algebras
kind: claim
title: Every infinite finitely generated computably presented simple group has a computable enumeration whose essential shell germ algebra A_nu/J is finitely presented
distinct_from:
  shell-germ-steinberg-algebra-is-finitely-presented: that asks, for SOME perfect input and SOME enumeration, that A_nu itself is finitely presented; this asks, for EVERY infinite simple input, that the essential quotient A_nu/J is finitely presented. Only this universal quotient form feeds Boone--Higman, because A_nu is never simple.
  simple-inputs-have-fp-elementary-leavitt-tensor-hosts: that asks for any finitely presented central simple host algebra, together with a finitely normally generated Steinberg kernel; this fixes the host to be the essential shell germ algebra and asks only for its finite presentation.
  shell-germ-quotient-algebra-fp-forces-fp-local-algebra: that is a necessary consequence of finite presentation of A_nu/J for one enumeration; this is the universal existence statement.
---

**OPEN.**

Let `S` be an infinite finitely generated simple group with computable presentation. The claim: there
is a computable bijection `nu : S -> N` such that, for the shell envelope `E_nu = <V, hat(S)>` of
`shell-cantor-embeddings-are-finite-germ-extensions`, its germ groupoid `G_nu`, `A_nu = A_(F_2)(G_nu)`
and the singular ideal `J`, the essential algebra `A_nu/J` is a finitely presented `F_2`-algebra.

## Role

This is the first of the two universal holes of
`boone-higman-via-essential-shell-germ-algebras`. It is the gate that step 4 of
`boone-higman-via-germ-steinberg-algebra-presentation` actually uses once that route is read with
the correction of bh-free-53 (`A` is never simple, so `A/J` is the host) and with the quantifier
that step 4 needs (every simple input, not one perfect input).

## How it can fail independently

- **Local algebra.** By `shell-germ-quotient-algebra-fp-forces-fp-local-algebra`, each witness `nu`
  makes the local algebra `K[Q_nu]/J_p` at the singular point finitely presented. So one infinite
  simple `S` for which every enumeration has infinitely presented local algebra refutes this.
- **Not through A.** A sufficient path is: `A_nu` finitely presented and `J` finitely generated as an
  ideal. By `shell-germ-algebra-fp-forces-fp-germ-group` the first half already forces the germ
  group `Q_nu` to be finitely presented, and `generic-shell-germ-algebras-are-not-finitely-presented`
  excludes it for generic `nu`. So this path runs into the germ half of the shell group gate, and
  a proof must use `A/J` directly, or a non-generic `nu` for every simple input.
- It says nothing about the Steinberg kernel. That is the second hole,
  `essential-shell-germ-leavitt-tensors-have-fng-steinberg-kernels`, which can fail even when
  this holds.

## Attempts

1. **Through finite presentation of A_nu (swarm-0917-w17-bh-last1, 2026-09-19).** *It dies at the germ group, for generic enumerations.*
   The obvious path is to present `A_nu` finitely and add finitely many generators of `J`.
   By `shell-germ-algebra-fp-forces-fp-germ-group`, the first step already needs a finitely
   presented germ group `Q_nu`. `generic-shell-germ-algebras-are-not-finitely-presented` rules
   that out for every generic `nu`, and no one-ended input is known to have any `nu` with `Q_nu`
   finitely presented (Attempt 1 of `steinberg-resolvent-shell-envelope-is-finitely-presented`).
   The direct `A/J` attack is deferred. Its first test is whether
   `K[Q_gen]/ω(F_e)ω(F_o)K[Q_gen]` is finitely presented, the open question in Attempt 3 of
   `shell-germ-algebra-fp-forces-fp-germ-group`.
