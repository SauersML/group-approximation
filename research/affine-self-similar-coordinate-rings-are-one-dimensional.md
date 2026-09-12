---
rg: 2
id: affine-self-similar-coordinate-rings-are-one-dimensional
kind: claim
title: Finitely generated commutative coordinate domains of self-similar affine groups have transcendence degree zero
distinct_from:
  fp-self-similar-groups-embed-in-fp-simple-groups: that is the embedding theorem for finitely presented self-similar groups; this is an obstruction on the coordinate rings that affine self-similar examples can use.
  rational-linear-groups-satisfy-boone-higman: that uses self-similar affine groups over suitable rings to reach GL_n(Q); this shows that finitely generated section-closed rings of the digit type are one-dimensional, so the construction stays at transcendence degree zero.
  char-zero-leavitt-unit-groups-have-congruence-kernels: that obstructs Leavitt unit groups over characteristic-zero coefficient rings as simple hosts; this obstructs affine self-similar groups over coordinate rings of positive transcendence degree.
---

**ESTABLISHED.** Let `O` be a complete discrete valuation ring with uniformizer
`pi` and finite residue field. Let `R <= O` be a subring that is a finitely
generated commutative ring and a domain of characteristic zero. Suppose `R` is
*section-closed*:

```text
(SC)   b in R and b in pi O   ==>   b/pi in R.
```

Then `P = R ∩ pi O` is a maximal ideal of `R`, the localization `R_P` is a
discrete valuation ring, and `Frac(R)` is a number field.

**Zaremsky's criterion (part b).** Let `R` be a finitely generated commutative
ring that is a domain of characteristic zero. Suppose some `x in R` has `R/xR`
finite and `∩_k x^k R = 0`. Then `trdeg(Frac R / Q) = 0`.

This is the ring hypothesis of Zaremsky's Example 4.7 (arXiv:2405.09722v2), read
from the HTML text on 2026-09-12. There `R^n x| GL_n(R)` acts self-similarly on
the tree of cosets of the powers of a finite-index principal left ideal `J = Rx`,
with `x` not a zero divisor and `∩_k R x^k = {0}`. When that group is finitely
presented, it satisfies Boone--Higman. A finitely generated affine group
`R^n x| GL_n(R)` forces `R` to be a finitely generated ring, since the
translation parts of the generators must span `R^n`.

## Why (SC) is the relevant condition

Fix `n >= 1` and a finite set `D <= O^n` of representatives of `(O/pi O)^n`.
Every `x in O^n` has a unique expansion `x = r + pi x'` with `r in D`. Iterating
identifies `O^n` with the boundary of the `|O/pi O|^n`-regular rooted tree.

An affine map `g(x) = Mx + b` acts on this tree. Its section at the digit `r` is
`x' -> M x' + c` with `c = (Mr + b - s)/pi`, where `s in D` is the digit of
`Mr + b`.

Suppose the translation group `R^n` is self-similar for this action. Take
`b in R^n ∩ pi O^n` and let `r` be the representative of `0`. Then `s = r`, and
the section of `x -> x + b` at `r` is the translation by `b/pi`. So `b/pi in R^n`,
which is (SC) coordinatewise.

Therefore every digit self-similar affine group `R^n x| GL_n(R)` whose coordinate
ring is a finitely generated domain of characteristic zero has
`trdeg(Frac R / Q) = 0`.

## Scope

**What it excludes.** Every commutative version of the affine route of
`rational-linear-groups-satisfy-boone-higman` at positive transcendence degree:
- **Zaremsky's Example 4.7 criterion:** part (b) shows it never holds for a
  finitely generated commutative coordinate domain of positive transcendence
  degree. For example `Z[t]/(f)` is infinite for every nonzero nonunit `f`.
- **The p-adic digit version:** sending `t` to a transcendental `p`-adic integer
  fails, because the digit shift `(t - s)/p` leaves `Z[t]`.

**What it does not exclude.**
- Noncommutative coordinate rings with a finite-index principal left ideal.
- Self-similar hosts that are not affine.
