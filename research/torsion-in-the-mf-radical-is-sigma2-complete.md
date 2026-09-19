---
rg: 2
id: torsion-in-the-mf-radical-is-sigma2-complete
kind: claim
title: Having a nontrivial torsion element in the MF radical is Sigma-zero-two complete for finite presentations
distinct_from:
  fixed-non-mf-mark-query-is-second-level-complete: that query names the fixed template E and its mark; this property mentions no auxiliary group at all, only the input group's own torsion and its own MF radical.
  mf-recognition-finite-presentations-is-pi2-complete: that asks whether the whole MF radical is trivial and is open; this asks whether the radical meets the torsion and is settled.
  fixed-mf-radical-membership-is-sigma2-complete: that fixes the group and varies the word; this varies the finite presentation and quantifies the word away.
---

ESTABLISHED.  For finite presentations `P` with group `G_P`, each of the
following sets is `Sigma^0_2`-complete:

```text
TRAD_MF   = { P : some g != 1 of finite order lies in Rad_MF(G_P) },
TRAD_fd   = { P : some g != 1 of finite order is killed by every
                  finite-dimensional unitary representation of G_P },
TRAD_fin  = { P : some g != 1 of finite order is killed by every
                  finite quotient of G_P }.                             (TR1)
```

Equivalently, each of the complementary "residual" properties -- every
torsion element of `G_P` is detected by some finite-dimensional approximate
representation, by some finite-dimensional unitary representation, by some
finite quotient -- is `Pi^0_2`-complete.  These are torsion-relative versions
of residual finiteness sitting exactly at the second level, one level below
where residual finiteness of finite presentations is presently known to live
(`Pi^0_3` upper bound).

## Proof

*Upper bounds.*  `g != 1` is `Pi^0_1` and `g^n = 1` is `Sigma^0_1` for finite
presentations.  `g in Rad_MF(G_P)` is `Sigma^0_2` by
[[mf-radical-membership-has-a-sigma2-upper-bound]].  "`g` dies in every finite
quotient" is `Pi^0_1`: a finite quotient is a finite multiplication table
with an assignment of generators, and checking the relators and the image of
`g` is decidable.  "`g` dies in every unitary representation of dimension
`d`" is a first-order sentence over the reals, decidable for each `d`, so
the universal statement over `d` is `Pi^0_1`.  Existential quantification
over `g` and over the order keeps everything in `Sigma^0_2`.

*Hardness.*  Take the reduction `e -> T(P_e)` of
[[fixed-non-mf-mark-query-is-second-level-complete]]: the exact `E` switch
followed by Chiodo's torsion-order-preserving compiler.  If `e in INF` then
`T(P_e)` is torsion-free and none of the three sets contains it.  If `e in
FIN` then `E` embeds in `T(P_e)` and its central involution `w` survives;
`w in Rad_MF(E)`, so by functoriality of the MF radical `w in
Rad_MF(T(P_e))`.  Every finite-dimensional unitary representation and every
finite quotient of `T(P_e)` restricts to one of `E`, and these kill `w`
because `w` lies in the MF radical of `E` (finite-dimensional
representations are norm-microstates).  So `T(P_e)` lies in all three sets.
Hence `FIN <=_m TRAD_*` for each of the three.

## Remark on inputs

`TRAD_MF` and `TRAD_fd` use the literal non-MF group `E` through its
torsion mark; `TRAD_fin` could also be reduced to from any finitely presented
group with a torsion element in its profinite kernel (for instance an
infinite finitely presented simple group with torsion), so its hardness is
independent of the non-MF construction.  The three coincide on the reduction
image but are different properties in general.
