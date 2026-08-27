---
rg: 2
id: compilers-cannot-drop-the-decidability-hypothesis
kind: claim
title: Both 2026-08-24 Boone-Higman compilers force their input to have solvable word problem, so neither can be proved from a finite presentation alone
invalidates: [boone-higman-via-hypothesis-free-shift-compiler]
distinct_from:
  simple-envelope-forces-solvable-word-problem: that is the converse half of Boone-Higman and derives decidability from an embedding into a finitely presented SIMPLE group; this derives decidability from finite presentability of a shift-similar envelope, and from a normal-subgroup finiteness package, neither of which mentions a simple group. It is the same phenomenon applied one construction earlier, and it is what makes those constructions impossible rather than merely unproved.
  novikov-boone-fp-group-undecidable-word-problem: that exhibits one finitely presented group with unsolvable word problem; this uses that group to show two proposed universal constructions must consume a decidability algorithm, and is a statement about proofs rather than about a group.
  conjugacy-finite-recursive-presentation-solvable-wp: that is the citation-free special case, proved by enumerating conjugacy classes; this is the general statement, which rests on imported theorems, and it names the two compiler claims explicitly.
  fp-strongly-shift-similar-admits-type-a-action: that is the imported proposition supplying the type (A) action; this is the contrapositive consequence drawn from it about what a proof of the compiler statements must contain.
artifacts:
  - research/artifacts/boone-higman-fiber-product-and-shift-compiler-2026-08-24.md
---

**(a)** If `E_nu(P)` is finitely presented for some bijection `nu`, then `P`
has solvable word problem.  Hence for a finitely presented `P` with
unsolvable word problem -- one exists by
`novikov-boone-fp-group-undecidable-word-problem` -- **no** `nu` makes
`E_nu(P)` finitely presented, and the hypothesis of `shift-higman-compiler`
cannot be dropped.

**(b)** If `T, N` carry the fiber-product data of
`universal-fiber-product-data-for-word-problem-groups` -- `T` finitely
presented, `N <| T` finitely generated, `T/N` of type `F_3`, `C_T(N) = 1`,
finitely many `T`-conjugacy classes in `N` -- then `T` has solvable word
problem.  So the data never exists over a finitely presented group with
unsolvable word problem, and clause 1 of that claim cannot be met by an
arbitrary finitely presented overgroup.

## Proof

*(a).*  Suppose `E_nu(P)` is finitely presented.  By
`mallery-zaremsky-shift-similar-envelope` it is strongly shift-similar, so
by `fp-strongly-shift-similar-admits-type-a-action` its natural action on
`N` is of type (A), and by
`type-a-action-gives-boone-higman-for-subgroups` every subgroup of it has
solvable word problem.  `P` is such a subgroup.

*(b).*  By `fiber-product-conjugation-action-lemma` and
`one-two-three-fibre-product-theorem` the group `Gamma = T x_Q T` is
finitely presented and acts on `N` with type (A) -- faithfully because
`C_T(N) = 1`, with point stabilizers conjugate to `Delta T`, and with
finitely many two-element-subset orbits because there are finitely many
`T`-conjugacy classes in `N`.  So by
`type-a-action-gives-boone-higman-for-subgroups` every subgroup of `Gamma`
has solvable word problem, and `Delta T` is isomorphic to `T`.  `∎`

## The degenerate case needs no citation

Take `N = T` in (b): the data reads "`T` finitely presented, `Z(T) = 1`,
finitely many conjugacy classes", and the conclusion "`T` has solvable word
problem" is then
`conjugacy-finite-recursive-presentation-solvable-wp`, proved in four lines
by complementary enumeration and depending on nothing imported.  So the
sharpest instance of this claim is checkable by hand, which is the reason to
believe the imported route in the general case rather than to suspect a
misread hypothesis.

## What this does and does not rule out

It does **not** refute either compiler statement.  Both keep their
decidability hypothesis and both remain open.

What it rules out is a class of proofs: any argument that establishes finite
presentability of `E_nu(P)`, or existence of the fiber-product data, by
manipulating a finite presentation without ever consuming a word-problem
algorithm.  That is a real constraint, because finite-presentability
arguments are normally uniform in the presentation, and it says the proof
that is wanted here cannot be.  It is the exact analogue, one construction
earlier, of the standard observation that a finitely presented simple group
has solvable word problem.
