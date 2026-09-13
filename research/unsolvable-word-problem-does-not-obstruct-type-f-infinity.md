---
rg: 2
id: unsolvable-word-problem-does-not-obstruct-type-f-infinity
kind: claim
title: "Word-problem complexity cannot obstruct embedding a group into a type F_infinity group"
---

Type `F_infinity` (indeed type `F`) does not bound the complexity of the word
problem, so one cannot rule out an embedding of a group `G` into a group of
type `F_{n+1}` / `F_infinity` on the ground that the word problem of `G` is
too complicated. This is the second dead general strategy for the
obstruction-side claim
`some-type-fn-group-embeds-in-no-type-fn-plus-1-group`.

**Reason.** There is a group of type `F` with unsolvable word problem
(Collins--Miller; noted by Xiaolei Wu, and recorded by Zaremsky as the
negative answer to Problem 1.2 of the same list). Hence "type `F_infinity`
implies solvable word problem" is false: a group of type `F_infinity` may
have arbitrarily complicated -- even unsolvable -- word problem. A subgroup
of such a group inherits no bound on its own word problem from the finiteness
type of the overgroup.

**Complementary direction.** Higman's embedding theorem says every finitely
generated recursively presented group embeds in a finitely presented group;
so having a hard (even unsolvable, as long as recursively enumerable) word
problem is not even an obstruction to embedding in a type-`F_2` group, let
alone a reason it could not sit in a larger-finiteness-type overgroup.
Together these remove word-problem complexity as a candidate obstruction and
leave the crux where
`some-type-fn-group-embeds-in-no-type-fn-plus-1-group` records it: a
structural invariant monotone under passage to type-`F_{n+1}` overgroups.
