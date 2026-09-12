---
rg: 2
id: four-cell-marked-star-has-an-eighth-head-flag
kind: claim
title: A fourth marked-star cell gives a literal one-eighth head flag but its shortest holonomy is a four-cycle
artifacts:
  - research/four-cell-asymmetric-head-support-proof.md
distinct_from:
  marked-star-asymmetric-heads-have-half-quarter-sources: that computes the first two nested head flags and isolates their unauthenticated product gauge; this adds a fourth positive marked center, computes the third flag, and audits the shortest palindromic alternatives.
  marked-star-outer-corrected-whiteheads-are-quarter-swaps: that gives three cells and two outer-corrected adjacent transports with quarter labels; this extends the same construction to four cells and three adjacent transports, but obtains an eighth source rather than an eighth involutory label.
  center-chain-four-hecke-flags-have-native-ranks: that obtains an eighth flag on a nonabelian signed character atom; this obtains it representation-universally on a positive commuting marked-root star.
  binary-leavitt-two-shared-gauge-selector-compiler: that needs an eighth controlled label carrying the same involutive reservoir gauge as the quarter row; this produces an eighth partial source whose shortest optimistic reservoir word is a noninvolutory Coxeter element.
---

Retain the mark projection `P`, the three centers `C_1,C_2,C_3`, and the
first three anchored Pauli cells.  Add the fourth center and cell

```text
C_4=x_(11,2)(q),
A_4=x_(11,10)(a_4),          B_4=x_(10,2)(b_4),       (FCS1)
```

where `a_4=s_1t_(0000)` and `b_4=s_(0000)t_1`.  Put

```text
E_4=P_(C_1,-)P_(C_2,-)P_(C_3,-)P_(C_4,-)P.
```

The prescribed four-root instance of the marked-star overlap theorem gives

```text
tau(E_4)>=(1/1190)tau(P)>0.                             (FCS2)
```

On `E_4H`, the four pairs `(A_i,B_i)` are cross-commuting Pauli pairs.
Write

```text
Z_2=B_2,                  Z_3=B_3,                  Z_4=B_4
```

and adjoin the third literal asymmetric head

```text
H_1=x_84(b_2)x_47(a_1),
H_2=x_95(b_3)x_58(a_2),
H_3=x_(10,6)(b_4)x_69(a_3).                            (FCS3)
```

The two shortest palindromic attempts do not create the next flag.  Exactly,

```text
E_4H_1H_2H_1E_4=0,                                    (FCS4)
```

whereas, for `T_212=E_4H_2H_1H_2E_4`,

```text
T_212^*T_212=E_4(1-Z_2)/2,
T_212T_212^*=E_4(1-Z_2Z_3)/2.                          (FCS5)
```

Thus the live palindrome has relative source and range rank `1/2`, not
`1/8`.

A seemingly more direct nested-corner use of `H_2` is also sign-fenced.
If `P_1=E_4(1+Z_2)/2`, then

```text
P_1H_2P_1=0.                                           (FCS5')
```

Indeed the transported center condition forces `Z_3=+1`, while the
transported `Z_2=+1` condition becomes `Z_3C_2Z_2=+1`; since `C_2=-1`,
this forces `Z_2=-1`.  More generally `H_2` maps the quarter atom
`E_4(Z_3=+1,Z_2=epsilon)` onto the opposite quarter atom
`E_4(Z_3=+1,Z_2=-epsilon)`.  It is a quarter-to-quarter flip, not a
same-corner half-to-quarter selector.

The monotone three-head word does give the literal next flag.  For

```text
T_321=E_4H_3H_2H_1E_4
```

one has

```text
T_321^*T_321=E_4(1+Z_2)(1+Z_3)(1+Z_4)/8,
T_321T_321^*=E_4(1-Z_2)(1-Z_3)(1+Z_4)/8.               (FCS6)
```

Both projections have relative rank `1/8`.  Together with the first two
heads, this gives a literal nested star source flag of relative ranks

```text
1/2,                         1/4,                    1/8. (FCS7)
```

There is nevertheless no shortest shared-involution conclusion.  Extend
the outer-corrected prefix words to the third adjacent word

```text
U_3=w_(6,11)(1)J_3,
```

where `J_3` is the prefix Whitehead on middle indices `(9,10)`.  The three
words act as adjacent swaps of the four Pauli cells.  Their reservoir
involutions `V_1,V_2,V_3` obey the type-`A_3` Coxeter relations and are
conjugate.  Even if one grants the still-unproved favorable identification
of each head polar gauge with `V_i`, the eighth transport in `(FCS6)` has
reservoir word

```text
V_3V_2V_1.                                             (FCS8)
```

This is a Coxeter element, hence a four-cycle of order four in the standard
`S_4` model, not an involution conjugate to any `V_i`.  This obstruction is
sharp at the shortest length: a word of at most two heads cannot expose all
three independent signs `Z_2,Z_3,Z_4`, while every length-three word that
does so uses each head once and therefore has Coxeter-element holonomy.

The first involutive Coxeter palindrome joining the endpoints,
`V_3V_2V_1V_2V_3`, does not retain the three flags.  Its corresponding head
word has only a half-dimensional source: its source condition is `Z_2=-1`,
and its range condition is `Z_2Z_3Z_4=+1`.

Thus an actual one-eighth star source exists without Property `(T)`, but
the shortest occurrence that creates it multiplies the three gauges into
a noninvolutory Coxeter holonomy.  A selector compiler still needs an odd
identity-outer comparison that turns `(FCS8)` into one of the native
involutions without erasing two of the three source flags.

DERIVATION
four-cell-asymmetric-head-support-proof
