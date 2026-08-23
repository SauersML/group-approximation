---
rg: 2
id: atlas-independent-phase-incidence-no-coercivity-proof
kind: route
title: Put cancelling signs on two private boundary edges and absorb the interior fold on a private edge
target: atlas-independent-phase-incidence-is-not-coercive
requires: []
---

For a two-chart word

```text
w=(epsilon_1,g_1)...(epsilon_m,g_m),
```

write `p_i=g_1...g_i` for its folded prefixes and

```text
P_x=lambda(x)Ulambda(x)^*.
```

Induction over the syllables gives the exact identity

```text
pi_U(w)
 = [product_(i:epsilon_i=2) P_(p_(i-1)) P_(p_i)^*]
   lambda(p_m).                                       (IPFP1)
```

Indeed a chart-one syllable only changes the final folded prefix, while a
chart-two syllable uses

```text
lambda(p) U lambda(g) U^*
 =P_p P_(pg)^* lambda(pg).
```

Formula `(IPF1)` is what remains when the finitely many `P_x` in `(IPFP1)`
are freed from their common-orbit constraint.

In the literal transported prefix table, boundary row `11` has the two
ordered edges

```text
a=01010000000101000000010000000001
  -> b=00010000010101000000010000000001,

c=00010000010001000000010000000001
  -> d=00010100010001000000010000000001.              (IPFP2)
```

Each of `a,b,c,d` occurs in no other one of the twenty-seven edge
occurrences.  Fix any trace-zero self-adjoint involution `Z` on
`C^20160`.  Set every phase vertex provisionally equal to `Z`, and replace
the four displayed values by

```text
P_a=P_c=-Z,       P_b=P_d=Z.                          (IPFP3)
```

The two affected multiplicative factors of row `11` are both `-I`; their
ordered product is `I`.  All its other factors, and all factors of the other
four boundary rows, will be `I`.  On the other hand, its additive
circulation is

```text
L_11=(-Z-Z)+(-Z-Z)=-4Z.                               (IPFP4)
```

It remains to kill the fixed fold of the interior word without changing a
boundary row.  The interior prefix table contains the private edge

```text
r=01000000000100000001010100000001
  -> s=01000000000101000001000100000001,              (IPFP5)
```

and neither endpoint occurs in another edge.  The exact folded residual is

```text
fold(c_19243)=01000000000100010000010000000001,
```

a nonidentity involution of `A_8`.  Hence
`R=lambda(fold(c_19243))` is a trace-zero self-adjoint involution with
`+1` and `-1` eigenspaces both of dimension `10080`.

Choose a trace-zero self-adjoint involution `T` commuting with `R` and
satisfying `Tr(RT)=0`: split each of the two `R` eigenspaces into two
`5040`-dimensional subspaces and give `T` signs `+1,-1` on the two halves.
Put

```text
R=lambda(fold(c_19243)),
P_r=RT,
P_s=T,                                                (IPFP6)
```

and leave every phase vertex not named in `(IPFP3)` or `(IPFP6)` equal to
`Z`.  Every unaffected edge still contributes `ZZ^*=I`.  The interior
private edge contributes

```text
P_r P_s^*=RTT=R=R^*,
```

so `(IPF1)` gives

```text
H_int=R^*R=I.                                         (IPFP7)
```

Equations `(IPFP3)--(IPFP7)` prove `(IPF2)`.  Since the normalized
Hilbert--Schmidt norm of `-4Z` is `4`, the left side of `(IPF3)` is at least
`16` while its right-hand bracket is zero.  This disproves `(IPF3)` for
every finite `C`.

Finally, `Z,-Z,T,RT` are all trace-zero self-adjoint involutions: for `RT`
this uses `[R,T]=0` and `Tr(RT)=0`.  In one even dimension any two such
involutions are unitarily conjugate, since each has equally large `+1` and
`-1` eigenspaces.  Thus every phase variable in the construction has one
common unitary conjugacy type.

The assignment is not claimed to have the form
`P_x=lambda(x)Ulambda(x)^*`: its purpose is precisely to prove that the
independent phase-incidence relaxation loses the only structure capable of
making the five-row Atlas inequality true.
