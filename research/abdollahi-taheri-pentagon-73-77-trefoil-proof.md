---
rg: 2
id: abdollahi-taheri-pentagon-73-77-trefoil-proof
kind: route
title: Substitute directly, apply one Nielsen move to reach the trefoil relator, and match all 105 rows against the census
target: abdollahi-taheri-pentagon-relations-73-and-77-are-trefoil-type
requires: []
---

**Source.** The TeX source of arXiv:1612.00934, fetched from `arxiv.org/e-print`
on MSI. Table `tab-C5` and the enumerated items `(73)` and `(77)` of the
appendix are quoted in the claim.

(1) **The displayed Tietze step.** Relator (73) is
`h_2 . h_3^-1 h_3^-1 . h_2 h_2 . h_3^-1 . h_2`. Under `h_3 -> h_2 h_3` each
`h_3^-1` becomes `h_3^-1 h_2^-1`, so the image is

```text
h_2 . h_3^-1 h_2^-1 h_3^-1 h_2^-1 . h_2 h_2 . h_3^-1 h_2^-1 . h_2
  = h_2 h_3^-1 h_2^-1 h_3^-1 h_2 h_3^-1 ,
```

which is cyclically reduced of length 6. The appendix displays the length-5
word `h_2h_3^{-1}h_2^{-1}h_3^{-2}`.

(2) **Trefoil normal forms.** Under `h_3 -> h_3 h_2^2`, `h_3^-1` becomes
`h_2^-2 h_3^-1`, and (73) goes to

```text
h_2 . h_2^-2 h_3^-1 . h_2^-2 h_3^-1 . h_2^2 . h_2^-2 h_3^-1 . h_2
  = h_2^-1 h_3^-1 h_2^-2 h_3^-2 h_2 ,
```

a conjugate of `h_3^-3 h_2^-2`. Under `h_2 -> h_2 h_3^2`, `h_2 h_3^-2` becomes
`h_2`, so `(h_2 h_3^-2)^2 h_2` goes to `h_2 h_2 h_2 h_3^2 = h_2^3 h_3^2`. Both
maps are automorphisms of `F(h_2, h_3)`. So `<h_2, h_3 | (73)>` and
`<h_2, h_3 | (77)>` are each isomorphic to `<a, b | a^3 b^2>`, the trefoil
group. `torus_witness.out` repeats these computations mechanically.

(3) **No contradiction by itself.** The trefoil group `T` is the fundamental
group of a knot exterior. It is torsion-free, and its commutator subgroup is
free of rank 2, so it is neither abelian nor solvable. In
`T = <h_2, h_3 | (73)>`:
- `h_2 != 1`, since killing `h_2` leaves `<h_3 | h_3^3>`, which is finite;
- `h_3 != 1`, since killing `h_3` leaves `<h_2 | h_2^4>`;
- `h_2 != h_3`, since identifying them leaves `<h | h^(4-3)>`, which is
  trivial.

The same holds for (77), where killing `h_2` leaves `<h_3 | h_3^4>`, killing
`h_3` leaves `<h_2 | h_2^3>`, and identifying them gives exponent sum
`3 - 4 != 0`. So the relation holds in a torsion-free, non-solvable group
with the three support elements distinct. It contradicts none of the three
conditions the appendix uses: torsion, commutativity, solvability.

(4) **All rows.** `at_c5_parse.py` parses the 105 rows of `tab-C5`, matches
each to a census class up to rotation and inversion (no row is unmatched),
and reports the stars against the census types (`at_c5_parse.out`):
- starred: 15 cyclic, 18 solvable, 2 torus (rows 73 and 77);
- unstarred: 28 torus, 6 `BS(2, +-2)`, 36 unrecognized.

(5) **The repository bound.** The route of
`f2-support-three-zero-divisors-need-support-at-least-22` uses A--T Cor 6.2
only for `n >= 20`. The artifact `zero-divisor-search-2026-09-12.md` §6
records that `zds3.c` excludes every connected triangle-free cubic graph with
at most 18 vertices (runs `ladder.595297` and `n18.595304`), and uses only
A--T Thm 2.9 (Schweitzer Thm 4.2), which concerns cycles of length at most 3.
