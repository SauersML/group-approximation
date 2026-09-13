---
rg: 2
id: rf-higman-embedding-for-decidable-groups
kind: claim
root: true
title: Every finitely generated residually finite group with solvable word problem embeds in a finitely presented residually finite group
refuted_by:
  - rf-higman-embedding-for-decidable-groups-fails
distinct_from:
  torsion-free-higman-embedding: that is a Higman embedding preserving torsion-freeness, with no residual finiteness in its output; this asks for a finitely presented overgroup that is residually finite.
  fp-residually-finite-boone-higman: that asks for a finitely presented simple overgroup of a finitely presented residually finite group; this asks for a finitely presented residually finite overgroup of a finitely generated residually finite group with solvable word problem, the residually finite analogue of Higman's embedding theorem.
---

**REFUTED (2026-09-13)** by `rf-higman-embedding-for-decidable-groups-fails`. Rauzy, arXiv:2002.02540, Theorem 1, answers the question negatively. The refuted statement: every finitely generated residually finite group with solvable word problem embeds in a finitely presented residually finite group.

**Source of the question.** Kharlampovich--Myasnikov--Sapir, *Algorithmically complex residually finite groups*, arXiv:1204.6506, §1.1.7 ("What next?"). They call it the residually finite version of Higman's embedding theorem:

> "Thus it would be very interesting to find out whether every finitely generated residually finite group with solvable word problem embeds into a finitely presented residually finite group."

**Why the word-problem hypothesis is needed.** Finitely presented residually finite groups have solvable word problem, by McKinsey's algorithm (their §1.2), and solvability passes to finitely generated subgroups. The same paragraph of §1.1.7 notes that a finitely generated, recursively presented, residually finite group can have undecidable word problem. Such a group has no finitely presented residually finite overgroup. Rauzy shows that solvable word problem is still not enough: effective residual finiteness is also necessary.

## Consequence for the self-similar route

An embedding of the group of `cycle-transposition-lef-group-has-no-regular-tree-action` in a finitely presented residually finite group would do three things:
- it would give a finitely presented residually finite group with elements of every prime order `p >= 5` (route `unbounded-prime-torsion-via-rf-higman-embedding`);
- by `regular-tree-torsion-orders-have-primes-at-most-degree`, that group embeds in no `Aut(T_d)`;
- so it would refute `every-fp-rf-group-embeds-in-fp-self-similar-group`.

Rauzy's theorem refutes the universal statement, but it gives no answer for that one group. That group is effectively residually finite (see `rf-higman-embedding-for-decidable-groups-fails`), so the obstruction does not apply to it. The self-similar route to `fp-residually-finite-boone-higman` needs that specific group to have no finitely presented residually finite overgroup, and this is still open.

## Attempts

1. **Kharlampovich--Myasnikov--Sapir constructions.** They build finitely presented residually finite solvable groups that simulate Minsky machines, and present this as a step towards the theorem. No prescribed group is embedded.
2. **Classical Higman embeddings.** The torsion-order-preserving Higman embedding of `torsion-free-higman-embedding` gives no control over residual finiteness in its output. Its amalgam and HNN stages are the usual source of non-residually-finite groups. Not pursued further here.
3. **Test input.** The group `Gamma` of `cycle-transposition-lef-group-has-no-regular-tree-action` has polynomial-time word problem and elements of every prime order `p >= 5`. Every overgroup inherits that torsion. No finitely presented residually finite overgroup is known here.
4. **Answered negatively in general (Rauzy 2020).** Some finitely generated residually finite group with solvable word problem is not effectively residually finite, and so has no finitely presented residually finite overgroup (`rf-higman-embedding-for-decidable-groups-fails`). Specific embeddings remain possible: a decidable group that is effectively residually finite, such as `Gamma` above, is not excluded by this obstruction.
