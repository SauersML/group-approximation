---
rg: 2
id: leavitt-degree4-strict-omega-four-cycle-no-go-proof
kind: route
title: Classify the signed topology and reduce the pivot equation in the free product
target: leavitt-degree4-strict-omega-four-cycle-no-go
requires:
  - leavitt-omega-four-cycle-compiler
---

The attached audit performs exact Reidemeister--Schreier rewriting with a
distinct marker in every coefficient slot.  Through length twenty it finds
the profile `(1,1,3,3)` only at length eight: 20 sign words in the three
dihedral classes displayed in the claim.  The class `--++++++` has trivalent
corner-length profiles `(3,4,1)` and `(1,4,3)`, so it does not have the two
singleton corners required by the strict corrected pattern.

It remains first to audit `-++-++++`.  Write its slots as `g_0,...,g_7`.  The two trivalent
orbits have signed corners

```text
(+,g_0,0), (-,g_1,3),
  (+,g_2,0 g_3,1 g_4,0 g_5,1 g_6,2 g_7,3),

(+,g_3,0), (-,g_4,3),
  (+,g_5,0 g_6,1 g_7,2 g_0,3 g_1,2 g_2,3).
```

Here the second index is the free-product copy.  Thus the two strict common
singleton corners require

```text
g_0=g_3=k,                 g_1=g_4=k^-1.              (1)
```

The unary corners are

```text
U_1=g_7,0 g_0,1 g_1,0 g_2,1 g_3,2 g_4,1 g_5,2 g_6,3,
U_2=g_6,0 g_7,1 g_0,2 g_1,1 g_2,2 g_3,3 g_4,2 g_5,3. (2)
```

If `U_1` is the pivot `H=k_0`, retracting (2) to the four coefficient
copies gives

```text
g_7=k^2,   g_2=1,   g_5=k^-1,   g_6=1.
```

After substitution, the reduced free-product word for `U_1` is

```text
k^2_0 k_1 k^-1_0 k_2 k^-1_1 k^-1_2.
```

It cannot equal `k_0` unless `k=1`.  The four displayed component equations
then make `g_2,g_5,g_6,g_7` trivial as well.  If `U_2` is the pivot, the copy
retractions instead give

```text
g_6=k,   g_7=k,   g_2=1,   g_5=k^-1,
```

and its substituted normal form again contains separated nontrivial
syllables in copies 1, 2, and 3 unless `k=1`.  Therefore every slot is
trivial in either pivot choice, so neither long corner can contain the
nonidentity target `T`.

For completeness, in the class `-+++-+++` the two singleton pairs instead
force

```text
g_0=g_4=k,                 g_1=g_5=k^-1.
```

Its unary corners are

```text
g_7,0 g_0,1 g_1,0 g_2,1 g_3,2 g_4,3 g_5,2 g_6,3,
g_3,0 g_4,1 g_5,0 g_6,1 g_7,2 g_0,3 g_1,2 g_2,3.
```

Equating the first to `k_0` gives
`g_7=k^2,g_2=k^-1,g_3=k,g_6=k^-1`; equating the second gives
`g_3=k^2,g_6=k^-1,g_7=k,g_2=k^-1`.  In either case substitution leaves the
reduced word

```text
k^2_0 k_1 k^-1_0 k^-1_1 k_2 k_3 k^-1_2 k^-1_3,
```

which cannot equal `k_0` for nontrivial `k`.  Thus `k=1` again makes all
eight slots trivial.

Finally, the tempting length-14 sign word `--+-+-+-++++++` has orbit profile
`(3,9,1,1)` and equal-copy gate incidences, but its ordered first residual
corner is

```text
c_3 a_2 d_3 b_2 c_3 a_2 d_3 b_2 (g_9)_3.
```

Thus `abab` and `cdcd` are interleaved between copies rather than forming an
Omega corner.  This records why equal-copy incidence alone is insufficient.
