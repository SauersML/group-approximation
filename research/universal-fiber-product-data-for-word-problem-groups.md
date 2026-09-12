---
rg: 2
id: universal-fiber-product-data-for-word-problem-groups
kind: claim
title: Every finitely generated group with solvable word problem sits in a finitely presented group carrying a finitely generated normal subgroup with trivial centralizer, finitely many conjugacy classes and an F_3 quotient
distinct_from:
  boone-higman-conjecture: that asks for a finitely presented SIMPLE group containing the input; this asks for a finitely presented group with a normal subgroup meeting four finiteness conditions, and mentions no simple group anywhere. The point of the reduction is that simplicity is discharged afterwards by an imported theorem rather than built.
  ck-envelope-simple-core-has-finite-bi-index: that asks for finiteness of a double coset set in the Chatterji-Kassabov envelope, a condition on a COSET action of a group already known to exist; this asks for a group to exist at all, with conditions on a two-sided translation action on a normal subgroup, and neither condition is known to imply the other.
  clapham-fp-embedding-preserves-word-problem: that is Clapham's theorem, which supplies the finitely presented decidable envelope and nothing else; this asks that the envelope additionally carry the normal subgroup data, which Clapham's construction says nothing about. Clapham is the first line of any attempt on this and never the last.
  shift-higman-compiler: that asks for finite presentability of one explicit permutation group built from a chosen bijection; this asks for an abstract group with a normal subgroup meeting four conditions. Both feed the conjecture through the same imported corollary, and neither is known to imply the other.
  boone-higman-thompson-simple-envelope: that is a theorem producing a computably presented simple envelope; this is an open construction problem whose output is not simple and whose input hypothesis is the same solvable word problem.
artifacts:
  - research/artifacts/boone-higman-fiber-product-and-shift-compiler-2026-08-24.md
---

For every finitely generated group `G` with solvable word problem there are
a group `T` and a normal subgroup `N <| T` with

1. `G <= T`,
2. `T` finitely presented,
3. `N` finitely generated,
4. `Q = T/N` of type `F_3`,
5. `C_T(N) = 1`,
6. `N` has finitely many `T`-conjugacy classes.

Call this the **fiber-product data** for `G`.

## What it buys, and what it costs

It buys the whole conjecture: `boone-higman-via-fiber-product-criterion`
turns the data into a type (A) action of `T x_Q T` on `N` and hands it to
`type-a-action-gives-boone-higman-for-subgroups`.  Nothing in the list
mentions simplicity, finite presentability of a simple group, or a normal
lattice; the simple group appears only at the end, produced by the imported
theorem, and the construction never has to prove anything about it.

What it costs is that six conditions must hold at once, and clauses 5 and 6
pull against clause 3.  `fiber-product-conjugation-action-lemma` records
three screens that come for free: `Z(N) = 1`; `N` realizes only finitely
many element orders; and `N` infinite whenever `G` is, since a finite `N`
with `C_T(N) = 1` forces `T <= Aut(N)` finite.  A fourth screen is
`compilers-cannot-drop-the-decidability-hypothesis`: the data forces `T` to
have solvable word problem, so clause 1 cannot be met by an arbitrary
finitely presented overgroup and Clapham's theorem
(`clapham-fp-embedding-preserves-word-problem`) is the right first step
rather than Higman's.

## The sharpest special case

Take `N = T`, so `Q = 1`, which is of type `F_infinity`.  Clauses 3 and 4
are automatic, the 1-2-3 theorem is not needed (`T x_1 T = T x T` is
finitely presented outright), and the data collapses to:

> every finitely generated group with solvable word problem embeds in a
> finitely presented group with trivial center and finitely many conjugacy
> classes.

That is a complete statement of a sufficient condition for Boone--Higman in
one line, with no auxiliary object.  It is carried as its own claim,
`every-wp-group-embeds-in-fp-conjugacy-finite-group`, feeding this one
through `fiber-product-data-from-conjugacy-finite-overgroup` -- a route into
*this* claim rather than a second route into `boone-higman-conjecture`, which
would prove the same target by the same argument.

The special case is also where the difficulty is visible.  A finitely
presented group with finitely many conjugacy classes has solvable word
problem by `conjugacy-finite-recursive-presentation-solvable-wp`, so the
hypothesis is consistent -- but no infinite finitely presented group with
finitely many conjugacy classes is known.  The known constructions of
finitely generated groups with finitely many conjugacy classes (small
cancellation over relatively hyperbolic groups) produce direct limits of
hyperbolic groups, which are finitely generated and not finitely presented,
and the limit is what makes the class set finite.  The general clause 6 is a
genuine relaxation of this: only the `T`-classes inside `N` must be finite in
number, and `T` may be much larger than `N`.

## Attempts

1. **`N = T` by small cancellation over relatively hyperbolic groups.**  The
   standard route to finitely many conjugacy classes builds an infinite
   ascending union of hyperbolic groups in which every previous element gets
   conjugated into a fixed one.  Each stage is finitely presented and the
   limit is not, and the limit is exactly where the class set becomes finite.
   Deferred at the identified step: nothing here refutes a finitely presented
   example, and the obstruction is that the construction is a limit by
   design.
2. **Relax to clause 6 with `N` proper, and take `N` a Burnside-type
   group.**  Clause 6 is easier for `N` proper because `T` supplies extra
   conjugators, and a finitely generated `N` of finite exponent has only
   finitely many element orders for free, which is one of the free screens.
   Deferred: no construction was found that also gives `C_T(N) = 1` together
   with clause 4, and clause 4 is the binding one -- `T/N` must be of type
   `F_3`, which forbids the quotient from being the usual infinitely
   presented limit.
3. **Weaken clause 4 to finite presentability of `Q`.**  This is the
   `n`-`(n+1)`-`(n+2)` question for `n = 1` and is not available: the 1-2-3
   theorem's `F_3` hypothesis is what makes the fibre product finitely
   presented, and Mihailova's fibre products are the standard witnesses that
   `F_2` on the quotient is not enough.  Not refuted for the special shape
   here, but no reason to expect it.
4. **Hide a non-faithful action upstairs.**  Given a group `Gamma` with the
   right orbit data but a kernel, pass to a finitely presented cover
   `Gamma-hat` acting through `Gamma`.  Dies immediately on clause 5 as it
   is used: the cover's action has kernel containing the covering kernel, so
   it is not faithful, and faithfulness is the clause of type (A) that
   supplies simplicity of `SV_G`.  There is no version of the criterion in
   which the kernel is harmless.  This graph already records the correct
   handling of that kernel in a neighbouring lane:
   `boone-higman-via-bffhz-action-image` quotients by the action kernel and
   pays for it by needing finite presentability of the *quotient*, which is
   its open input.  So the move is not new, it is the standard one, and it
   relocates the difficulty rather than removing it.
5. **Wreath and Houghton-style envelopes for clause 6.**  *Dies* at
   `wreath-base-conjugacy-classes-are-finite-multisets`: in
   `B wr_S Sym_fin(S)` the conjugacy classes of the base are exactly the
   finite multisets of nontrivial `B`-classes, so support size alone is an
   unbounded invariant and the count is infinite for every nontrivial `B`.
   The finitary top group kills positional invariants and nothing else.
   Recorded as `fiber-product-data-via-permutational-wreath`.
6. **Buy clause 6 with transitivity instead.**  By
   `two-transitive-action-reduces-type-a-to-two-clauses` a 2-transitive
   faithful action satisfies the pair-orbit clause for free, so one could
   drop the fiber-product action entirely and look for a 2-transitive one.
   Deferred, and it is a different problem rather than a repair of this one:
   what remains is finite presentation of the acting group, which is where
   `boone-higman-via-bffhz-action-image` is already stuck.
