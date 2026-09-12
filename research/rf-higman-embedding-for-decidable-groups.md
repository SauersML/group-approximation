---
rg: 2
id: rf-higman-embedding-for-decidable-groups
kind: claim
root: true
title: Every finitely generated residually finite group with solvable word problem embeds in a finitely presented residually finite group
distinct_from:
  torsion-free-higman-embedding: that is a Higman embedding preserving torsion-freeness, with no residual finiteness in its output; this asks for a finitely presented overgroup that is residually finite.
  fp-residually-finite-boone-higman: that asks for a finitely presented simple overgroup of a finitely presented residually finite group; this asks for a finitely presented residually finite overgroup of a finitely generated residually finite group with solvable word problem, the residually finite analogue of Higman's embedding theorem.
---

**OPEN.** Every finitely generated residually finite group with solvable word
problem embeds in a finitely presented residually finite group.

**Source.** Kharlampovich--Myasnikov--Sapir, *Algorithmically complex
residually finite groups*, arXiv:1204.6506, §1.1.7 ("What next?"). They call it
the residually finite version of Higman's embedding theorem:

> "Thus it would be very interesting to find out whether every finitely
> generated residually finite group with solvable word problem embeds into a
> finitely presented residually finite group."

**Why the word-problem hypothesis is needed.** Finitely presented residually
finite groups have solvable word problem, by McKinsey's algorithm (their §1.2).
Solvability passes to finitely generated subgroups. The same paragraph of §1.1.7
records that a finitely generated, recursively presented, residually finite
group can have undecidable word problem, and such a group has no finitely
presented residually finite overgroup.

## Consequence for the self-similar route

A positive answer can be applied to the group of
`cycle-transposition-lef-group-has-no-regular-tree-action`. It gives a finitely
presented residually finite group with elements of every prime order `p >= 5`
(route `unbounded-prime-torsion-via-rf-higman-embedding`). By
`regular-tree-torsion-orders-have-primes-at-most-degree`, that group embeds in
no `Aut(T_d)`, and this refutes
`every-fp-rf-group-embeds-in-fp-self-similar-group`.

So the self-similar route to `fp-residually-finite-boone-higman` needs this
question to have a negative answer, at least for that one group.

## Attempts

1. **Kharlampovich--Myasnikov--Sapir constructions.** They build finitely
   presented residually finite solvable groups that simulate Minsky machines,
   and present this as a step towards the theorem. No prescribed group is
   embedded, so the question stays open.
2. **Classical Higman embeddings.** The torsion-order-preserving Higman
   embedding of `torsion-free-higman-embedding` gives no control over residual
   finiteness in its output. Its amalgam and HNN stages are the usual source of
   non-residually-finite groups. Not pursued further here.
3. **Test input.** The group `Gamma` of
   `cycle-transposition-lef-group-has-no-regular-tree-action` has
   polynomial-time word problem and elements of every prime order `p >= 5`.
   Every overgroup inherits that torsion. No finitely presented residually
   finite overgroup is known here.
