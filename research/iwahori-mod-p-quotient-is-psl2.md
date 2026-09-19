---
rg: 2
id: iwahori-mod-p-quotient-is-psl2
kind: claim
title: Killing the p-th power of the half-parabolic gives PSL2(F_p)
artifacts:
  - experiments/psl2_short_quotient_check.py
  - experiments/psl2-short-quotient-smoke.json
distinct_from:
  iwahori-square-root-presentation-is-bs14-plus-one-involution: that identifies the ambient arithmetic group and its half-parabolic; this identifies its exact odd-prime torsion quotients.
  iwahori-weil-cycle-packets-extend-exactly: that constructs particular representations of the quotient; this proves the quotient group itself is PSL2(F_p).
---

Let

```text
G = PSL_2(Z[1/2])
  = <x,r,s | x^2, (xr)^2, (xs^2)^3, (xrs)^3,
               r s r^(-1) s^(-4)>,
```

where `s=[[1,1/2],[0,1]]`.  For every odd prime `p`,

```text
G / <<s^p>> ~= PSL_2(F_p).                            (MPQ1)
```

Indeed, put `u=s^2=[[1,1],[0,1]]`.  The two normal closures agree:
`u^p=s^(2p)` lies in `<<s^p>>`, while

```text
s^p = r^(-1) s^(4p) r = r^(-1) u^(2p) r
```

lies in `<<u^p>>`.  Behr--Mennicke's congruence presentation (equivalently
Proposition 3.1 of Guralnick--Kantor--Kassabov--Lubotzky, *Presentations of
finite simple groups: a quantitative approach*) says that adjoining
`u^p=1` to the standard presentation of `SL_2(Z[1/2])` gives `SL_2(F_p)`.
Passing through the central quotient gives `(MPQ1)`.

The bounded Sage/GAP check computes orders `12,60,168` for `p=3,5,7`,
matching `|PSL_2(F_p)|`; it is retained only as a replayable falsification
check, not as the proof.

## Consequence

Any exact Iwahori extension on which `s` has primitive odd-prime order `p`
is a nontrivial complex representation of `PSL_2(F_p)`.  Thus the exact
character degrees of `PSL_2(F_p)`, rather than only the determinant fence,
classify the possible prime BS cycle packets.
