---
rg: 2
id: whitehead-vanishing-finitely-presented-torsion-free
kind: claim
title: Whitehead vanishing for finitely presented torsion-free groups
distinct_from:
  whitehead-vanishing-recursively-presented-torsion-free: that drops finite presentation to recursive presentation and is what actually implies the global conjecture; this is the finitely presented sub-case, which does not imply it without whitehead-injective-torsion-free-embedding.
  whitehead-vanishing-torsion-free: that is the global conjecture; this is its restriction to finitely presented groups, a class that does not exhaust the finitely generated ones that a Whitehead class can be supported on.
  whitehead-vanishing-universal-test-group: that concentrates the *finitely generated* case into one restricted product; this quantifies over finitely presented groups. The analogous product for this class is the repository's coded payload, and the two statements are equivalent to each other but not to that one.
  hnn-torsion-theorem: that claim is about torsion-freeness of HNN extensions, a group-theoretic permanence property; this is about vanishing of a K_1 quotient for groups already assumed torsion-free and finitely presented.
  operator-mf-is-a-markov-property: that claim is about operator MF being a Markov property of finitely presented groups, an approximation-theoretic statement; this is an algebraic K-theory vanishing. Both quantify over finitely presented groups and nothing else is shared -- see this node's parent root on why no implication runs either way.
  torsion-free-finitely-presented-non-mf: that is this program's root asserting some finitely presented torsion-free group fails MF; this asserts that all of them have vanishing Whitehead group. Same quantified class, unrelated predicates -- a group can, for all anyone knows, satisfy both.
artifacts:
  - research/artifacts/whitehead-vanishing-audit-2026-08-17.md
---

`Wh(H) = 0` for every finitely presented torsion-free group `H`.

Open, and **not** known to imply `whitehead-vanishing-torsion-free`.  The
temptation is to think it does, since every Whitehead class is supported on a
finitely generated subgroup and every finitely generated recursively
presented torsion-free group embeds in a finitely presented torsion-free one
(`torsion-free-higman-embedding`, now a theorem).  The embedding is real; the
implication is not, because an embedding gives only a map `Wh(K) -> Wh(H)`
and nothing says it is injective.  A factorization found over `ZH` may use
group elements of `H` that no homomorphism carries back to `K`.  See
`whitehead-injective-torsion-free-embedding`.

By `whitehead-vanishing-universal-test-group`'s split argument the
repository's coded product `UniversalFinitelyPresentedTorsionFreeGroup`
absorbs exactly this class: `Wh` of that product vanishing is equivalent to
this claim, since every finitely presented torsion-free group is a coordinate
with a splitting.  That is the exact strength of the Lean payload -- no more,
and, contrary to a natural misreading of its name, no less.

## Attempts

**Decompose the presentation.**  A finite presentation invites induction on
splittings: for amalgams and HNN extensions there are Waldhausen exact
sequences computing `Wh` of the total group from the pieces.  *Dies* on two
counts -- a general finitely presented group admits no such splitting, and
even when it does the sequences carry Nil summands that are themselves
unknown, so the induction has no base and no bounded step.

**Route through the coded universal product.**  Reduces this to `Wh` of one
countable group.  *Dies* for the same reason as
`whitehead-vanishing-universal-test-group`: every coordinate is a split
summand, so the product contains the difficulty rather than resolving it.
The Lean payload is a faithful formalization of a construction that cannot
help here.

**Deferred to Farrell--Jones.**  Most finitely presented torsion-free groups
one can name are in the `FJ` class, so this claim is *known* for them; what
is missing is any argument covering the ones that are not, and no finitely
presented torsion-free group with nonvanishing `Wh` is known either.  This
node is open because nobody can rule the remainder out, not because a
specific candidate resists.
