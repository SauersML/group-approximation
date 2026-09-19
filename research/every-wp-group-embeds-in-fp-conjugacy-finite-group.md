---
rg: 2
id: every-wp-group-embeds-in-fp-conjugacy-finite-group
kind: claim
title: Every finitely generated group with solvable word problem embeds in a finitely presented group with trivial center and finitely many conjugacy classes
distinct_from:
  universal-fiber-product-data-for-word-problem-groups: that asks for a finitely presented overgroup together with a proper normal subgroup carrying four finiteness conditions; this is its N = T specialization, where the normal subgroup is the whole group, the quotient is trivial and the 1-2-3 theorem is not needed. This one strictly implies that one.
  boone-higman-conjecture: that asks for a finitely presented SIMPLE overgroup; this asks for a finitely presented overgroup with trivial center and finitely many conjugacy classes, which is neither implied by nor implies simplicity.
  conjugacy-finite-recursive-presentation-solvable-wp: that is the theorem saying such a group automatically has solvable word problem; this is the open construction problem asking that one exist over every prescribed input. The theorem is what makes this hypothesis consistent rather than self-defeating.
  clapham-fp-embedding-preserves-word-problem: that supplies a finitely presented overgroup preserving decidability and is a theorem; this asks for the same overgroup to additionally have trivial center and finitely many conjugacy classes, which Clapham's construction does not give.
artifacts:
  - research/artifacts/boone-higman-fiber-product-and-shift-compiler-2026-08-24.md
---

For every finitely generated group `G` with solvable word problem there is a
finitely presented `T` with `G <= T`, `Z(T) = 1`, and finitely many
conjugacy classes.

This is the `N = T` case of
`universal-fiber-product-data-for-word-problem-groups` and it implies it:
take `N = T`, so `Q = 1`, which is of type `F_infinity`; `N` is finitely
generated because `T` is finitely presented; `C_T(N) = Z(T) = 1`; and the
`T`-conjugacy classes of `N` are the conjugacy classes of `T`.

It is the shortest sufficient condition for Boone--Higman this graph knows.
It carries no auxiliary object at all: one group, two adjectives, one
finiteness condition, and no simple group anywhere.

## Consistency, and where the difficulty sits

The hypothesis is not self-defeating.  By
`conjugacy-finite-recursive-presentation-solvable-wp` any such `T` already
has solvable word problem, which is exactly what
`compilers-cannot-drop-the-decidability-hypothesis` says the data must force,
so there is no clash with the input having solvable word problem either.

What is missing is an example.  No infinite finitely presented group with
finitely many conjugacy classes is known.  The standard constructions of
finitely generated groups with finitely many conjugacy classes -- small
cancellation over relatively hyperbolic groups, producing a group with two
conjugacy classes -- build a direct limit of hyperbolic groups in which every
element of every earlier stage is conjugated into a fixed one.  Each stage is
finitely presented; the limit is not; and the limit is precisely where the
class set becomes finite.  So the whole difficulty of this claim is the
tension between the two adjectives, not the construction of either alone.

## Attempts

1. **Stop a small-cancellation limit at a finite stage.**  Deferred at the
   identified step: at every finite stage only finitely many elements have
   been conjugated together, and the elements introduced by that stage's
   relators are new classes.  Nothing here refutes a cleverer scheme; the
   obstruction is that the known one is a limit by design.
2. **Ask only for finitely many classes and drop `Z(T) = 1`.**  Does not
   help and is not weaker in any useful sense: the centre is contained in
   every centralizer, so a nontrivial centre makes the action of `T x T` on
   `T` unfaithful and `SV` non-simple.  A group with finitely many conjugacy
   classes and more than two elements has trivial centre anyway, since a
   central element is its own class.
3. **Relax to the general fiber-product data.**  This is the honest fallback
   and is `universal-fiber-product-data-for-word-problem-groups`: only the
   `T`-classes inside a proper normal `N` need be finite in number, and `T`
   may be far larger than `N`, at the price of an `F_3` quotient and the
   1-2-3 theorem.
4. **Permutational wreath products.**  *Dies* at
   `wreath-base-conjugacy-classes-are-finite-multisets`; recorded as
   `fiber-product-data-via-permutational-wreath`.
