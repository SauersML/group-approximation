---
rg: 2
id: a2-action-kernels-are-recursive
kind: claim
title: Every type [A_2] action has a recursive kernel, so every action image has solvable word problem
refuted_by:
  - some-a2-action-has-a-nonrecursive-kernel
distinct_from:
  a2-kernel-removal-forces-recursive-kernel: that proves every type [A_2] kernel is co-recursively enumerable and every removable kernel is recursive; this asserts that every kernel is recursive.
  a2-pairs-embed-in-a2-pairs-with-fng-kernels: that asks for removal of every kernel, which implies this; this is only the computability condition, which gives removal once the permutational Boone--Higman conjecture is added.
  a2-kernel-removal-iff-image-satisfies-pbh: that proves removal of one kernel is the permutational conclusion for the image; this is the computability hypothesis under which that conclusion would follow from the permutational conjecture.
---

**OPEN.**

**Statement.** Let `G ↷ S` be of type [A_2], in the sense of
Fournier-Facio--Wu--Zaremsky, arXiv:2603.24687v2, Definition 1.3:
- `G` is finitely presented;
- point stabilizers are finitely generated;
- there are finitely many orbits on `S x S`.

Let `K` be its kernel. Then the set of words in a finite generating set of `G`
representing elements of `K` is recursive. Equivalently, the action image `G/K`
has solvable word problem.

**What is known.**
- **Co-r.e.** `K` is always co-recursively enumerable
  (`a2-kernel-removal-forces-recursive-kernel`, part (a)). So `K` is recursive
  iff it is r.e., iff `G/K` is recursively presented.
- **Necessary for Question 5.9.** A removable kernel is recursive (same node,
  part (b)). A positive first part of FFWZ Question 5.9 therefore implies this
  claim.
- **Sufficient modulo PBH.** This claim, `permutational-boone-higman-conjecture`
  and `a2-kernel-removal-iff-image-satisfies-pbh` together give the first part
  of Question 5.9 (route `a2-kernel-removal-via-pbh-and-recursive-kernels`).
  Under PBH, the first part of Question 5.9 is exactly this claim.
- **Faithful actions give nothing.** A type (A_2) action has trivial kernel.

**Where a counterexample would come from.** Take the FFWZ Theorem C actor of an
infinite finitely presented simple group `Γ`. Its one-variable mixed identities
many-one reduce to its kernel (`a2-kernel-removal-forces-recursive-kernel`, part
(c)). So a finitely presented simple group with a non-recursive set of mixed
identities would refute this claim. No such group is known in this graph.

**Status of the question.** FFWZ do not ask it, and no literature search beyond
the FFWZ text was made.
