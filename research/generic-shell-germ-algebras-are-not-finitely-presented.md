---
rg: 2
id: generic-shell-germ-algebras-are-not-finitely-presented
kind: claim
title: For every generic enumeration of every infinite finitely generated input, the shell germ group is not finitely presented, so the germ Steinberg algebra is not finitely presented over any field
distinct_from:
  generic-shells-have-infinitely-generated-singular-ideals: that proves the singular ideal is not finitely generated for generic enumerations, and concludes only "if A_nu is finitely presented then A_nu/J is not"; this shows A_nu itself is never finitely presented there, so that conditional has a false hypothesis.
  shell-germ-algebra-fp-forces-fp-germ-group: that is the general implication from the algebra to the germ group; this applies it to the generic class, where the germ group is an explicit parity graph product.
---

**ESTABLISHED** by `generic-shell-germ-algebra-not-fp-proof` (lane proof, elementary, not
reviewed; no priority claimed).

Let `P` be infinite and finitely generated, `nu` a generic enumeration in the sense of
`generic-shells-have-infinitely-generated-singular-ideals`, and `K` any field. Then:

1. `Q_gen = <P, τ | [P, τ^D P τ^(-D)] = 1, D odd>` is not finitely presented;
2. hence the germ group `Q_nu ≅ Q_gen` at `p` is not finitely presented;
3. hence `A_K(G_nu)` is not finitely presented.

So for the algebra route, generic enumerations are excluded at the level of `A_nu`, and not
only at the level of `A_nu/J`. Whether `A_nu/J` can be finitely presented for a generic `nu`
is not decided here. By `shell-germ-quotient-algebra-fp-forces-fp-local-algebra`, it would need
`K[Q_gen]/ω(F_e)ω(F_o)K[Q_gen]` to be a finitely presented algebra.
