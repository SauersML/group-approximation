---
rg: 2
id: conjugacy-finite-recursive-presentation-solvable-wp
kind: claim
title: A recursively presented group with finitely many conjugacy classes has solvable word problem
distinct_from:
  simple-envelope-forces-solvable-word-problem: that derives decidability from an embedding into a finitely presented simple group, using two enumerations against the normal closure of a fixed nontrivial element; this derives decidability from finiteness of the conjugacy class set of the group itself, with no envelope and no simplicity, and its complementary enumeration runs over conjugators rather than over normal-closure certificates.
  novikov-boone-fp-group-undecidable-word-problem: that exhibits a finitely presented group whose word problem is undecidable; this shows one concrete hypothesis that makes the word problem decidable, so together they say a finitely presented group with unsolvable word problem has infinitely many conjugacy classes.
  fp-strongly-shift-similar-admits-type-a-action: that gets decidability out of finite presentation plus a self-similarity property of a permutation group, by citation; this gets it out of conjugacy finiteness, by a two-line enumeration argument, and depends on no external theorem.
artifacts:
  - research/artifacts/boone-higman-fiber-product-and-shift-compiler-2026-08-24.md
---

Let `G = <X | R>` be a recursive presentation on a finite generating set,
and suppose `G` has finitely many conjugacy classes.  Then `G` has solvable
word problem.

## Proof

Both the word problem and its complement are recursively enumerable, so it
is decidable.

The word problem is r.e. as always: enumerate the consequences of `R`.

For the complement, fix conjugacy class representatives `g_1 = 1, g_2, ...,
g_k` -- words in `X`, existing by hypothesis, chosen non-uniformly, which is
all decidability of a fixed group requires.  For each `i` the set

    { w : w is conjugate to g_i }

is r.e.: enumerate pairs `(u, p)` where `u` is a word and `p` is a proof
from `R` that `w^{-1} u g_i u^{-1} = 1`.  Every word is conjugate to exactly
one `g_i`, and `w` is conjugate to `g_1 = 1` exactly when `w = 1` in `G`.
So

    { w : w != 1 }  =  union over i >= 2 of { w : w is conjugate to g_i },

a finite union of r.e. sets, hence r.e.  `∎`

## Why the graph carries it

It is the citation-free half of
`compilers-cannot-drop-the-decidability-hypothesis`.  In the degenerate case
`N = T` of the fiber-product data, the hypotheses read "`T` finitely
presented, `Z(T) = 1`, finitely many conjugacy classes", and the conclusion
"`T` has solvable word problem" -- which the imported Corollary B delivers by
a long route through twisted Brin--Thompson groups -- follows here in four
lines and from nothing.  A route whose only decidability consequence needed
an unread paper would be worth distrusting; this makes the sharpest case of
that consequence checkable by hand.

It also tells the right story about the strength of the hypothesis.
Conjugacy finiteness is not a mild condition to impose on a finitely
presented group: by `novikov-boone-fp-group-undecidable-word-problem` no
finitely presented group with unsolvable word problem has it, and no
finitely presented group with finitely many conjugacy classes and more than
one element is known.
