---
rg: 2
id: toeplitz-child-section-loses-square-or-exit
kind: claim
title: A Toeplitz child section either loses the central square or leaves the exit unpaid
distinct_from:
  aggregate-child-wordization-three-route-no-go: that proves the Toeplitz proper isometries themselves cannot be group words; this analyzes compression of the honest unitary stable letter and every ordinary closed return word.
  two-chart-square-lift-recreates-schur-m2: that rules out a full equal-carrier return by Morita matrix units; this treats the remaining one-child-to-two-child proper-corner geometry.
  projective-gauge-charge-forces-morita-or-corner: that identifies the proper-corner exception abstractly; this refutes its direct realization by the existing binary Toeplitz stable letter.
---

# A Toeplitz child section either loses the central square or leaves the exit unpaid

ESTABLISHED. In the exact binary Toeplitz head let `P` be the parent carrier,
let

```text
Q=tPt^*=Q_0+Q_1                                          (TSE1)
```

be its two-child image, and let `p<=P` be the source cut corresponding to one
child. The stable letter does give a genuine rectangular section

```text
v=Qtp=tp,       v^*v=p,       vv^*=r=tpt^*<=Q.           (TSE2)
```

The unused projection `Q-r` is the desired branch complement. Thus exact
algebraic placement is not the obstruction.

The obstruction appears when one closes the section to obtain a phase-bearing
same-carrier word. Let `h` be any global unitary group word obtained by going
through the Toeplitz head and returning, and put

```text
W=php in pMp.                                             (TSE3)
```

There is an exact compression identity

```text
p h^2 p = W^2 + p h(1-p)h p.                             (TSE4)
```

Therefore an ordinary central relation `h^2=J` gives

```text
W^2-Jp = -p h(1-p)h p,                                  (TSE5)
```

not the required corner relation `W^2=Jp`. The second term is precisely the
uncontrolled return through the complementary channels. It can carry the
entire central square at zero relator defect: on two equal blocks, an
off-diagonal unitary `h=[0,I;JI,0]` has `h^2=J` while `php=0`.

If one instead requires `W` to be a unitary in `pMp`, the leakage disappears
for a structural reason. From

```text
p-W^*W=p h^*(1-p)h p,                                   (TSE6)
```

and its range analogue, corner unitarity gives `(1-p)hp=0` and
`(1-p)h^*p=0`; hence `[h,p]=0`. After conjugating by the Toeplitz edge, the
intermediate range `r=tpt^*` reduces the head word. The complement `Q-r`
then carries an arbitrary reducing representation and pays no group-relator
energy. Direct sums and amplifications preserve this zero-defect spectator.

This yields the dichotomy:

```text
nonreducing proper-corner excursion  => central square does not compress;
unitary phase-bearing compression    => proper complement is reducing.    (TSE7)
```

The conclusion is robust at the level needed to locate any future correction:
the squared HS norm of the off-corner column is

```text
||(1-p)hp||_2^2=tau(p-W^*W).                             (TSE8)
```

Thus making `W` approximately unitary forces small average excursion, while
using a fixed amount of the exit forces a fixed Gram defect. A central square
defect alone does not control that positive Gram quantity because `(TSE5)`
contains a non-selfadjoint, phase-canceling cross term rather than its
modulus.

Finally, replacing `h` by the coefficient-ring Toeplitz isometries cannot
repair the problem. The relations `yx=1`, `xy=1-P` are genuinely nonunitary;
if `x,y` were ordinary group words, unitarity would make both products equal
and force `P=0`, with the same equality in normalized HS norm approximately.

Hence the existing parent-to-two-child stable letter does not realize
`proper-corner-charged-section`. A surviving construction must obtain the
positive support/Gram correction only in finite matrices (for example by a
spectral or singular-value decoder) while allowing a proper isometry in the
exact infinite marked model. Neither a global square relator nor the raw
Toeplitz stable letter supplies that correction.
