---
rg: 2
id: titz-witzel-seven-relator-gate-proof
kind: route
title: Conjugate three involutions and derive the other two from the quartics
target: titz-witzel-sofic-gate-has-only-seven-relators
requires: []
---

Write the group operation multiplicatively.  Three of the advertised
involutions are freely conjugate to `E`; no defining relator is needed:

```text
B = z E z^(-1),
H = y E y^(-1),
F = x^(-1) H x.                                           (1)
```

Indeed, substituting `E=y^(-1)z^2` into the right sides and freely cancelling
gives exactly the words `B,H,F` in `(TWS3)`.  It follows from `E^2=1` that
`B^2=F^2=H^2=1`.

It remains to recover `A^2` and `S^2`.  The third and fourth quartics in
`(TW7)` say

```text
A E D F=1,                 D F E H=1.                     (2)
```

Since `E,F,H` are involutions, the first equality gives
`D=E A^(-1)F`.  Substitution into the second gives

```text
1=E A^(-1) F F E H=E A^(-1) E H,
```

and hence `H=E A E`.  Squaring this equality and using `E^2=H^2=1`
gives `A^2=1`.

Now (2) reads `D=EAF`.  The fifth quartic is

```text
D S F E=1,
```

so

```text
S=D^(-1) E F=F A E E F=F A F.
```

Thus `S^2=1` follows from `A^2=F^2=1`.  This proves that all five deleted
square relators lie in the normal closure of the seven relators `(TW7)`.

The same calculation verifies the triangular replacement `(TW9')` without
any circular use of `A^2`.  Before deriving that square relation, the third
quartic gives

```text
D=E A^(-1)F.                                               (2a)
```

Substituting (2a) in the fourth gives `H=EAE`, and substituting it in the
fifth gives `S=FAF`.  Conversely, assume these three displayed identities.
Using only `E^2=F^2=1`, their left sides recover the old quartics:

```text
A E D F = A E E A^(-1) F F = 1,
D F E H = E A^(-1) F F E E A E = 1,
D S F E = E A^(-1) F F A F F E = 1.
```

So replacing those three relators is an exact finite relator transformation.

For the change of generators, set

```text
c=C=y^2x,             e=E=y^(-1)z^2,             r=z.
```

It has the explicit free-group inverse

```text
y=r^2e^(-1)=Y,        x=Y^(-2)c=X,               z=r.      (3)
```

Both directions hold already in the free groups.  Starting with `(x,y,z)`,
the reverse substitution sends

```text
Y=z^2 E^(-1)=z^2 (y^(-1)z^2)^(-1)=y,
X=Y^(-2) C=y^(-2)y^2x=x.
```

Starting with `(c,e,r)`, equations (3) give

```text
Y^2X=c,                   Y^(-1)r^2=e,
```

so the forward substitution recovers `c=C`, `e=E`, and `r=z`.  Substitution
of (3) in the seven retained old relators is precisely `(TW8)--(TW9)`, while
the calculation in the first half of the proof recovers every deleted old
relator.  Conversely all seven relators in `(TW9)` are images of retained old
relators.  This proves both presentation maps are inverse.  Thus this is a
finite Tietze change, not merely a quotient or a comparison map.  The marked
word `y^8` becomes `Y^8` as a literal free-word substitution, and the inverse
map sends `Y^8` back to `y^8`.

Finally, the same calculation applies to asymptotic permutation solutions.
Normalized Hamming distance is bi-invariant, and evaluation of every fixed
word is Lipschitz in its letters.  Identities (1), the two substitutions in
(2), and the displayed derivation of `S=FAF` therefore bound the defect of
each deleted square by a fixed finite sum of defects of the retained seven
words.  Those deleted defects tend to zero whenever the seven retained
defects do.  Conversely, every retained word is one of the original relators.
The word substitutions (3) preserve dimensions and send the separation word
exactly to `Y^8`.  Hence `(TW10)` is quantitatively equivalent to the original
twelve-relator gate.

The following is a separate approximation observation, not part of the
presentation isomorphism.  An approximate involution can always be rounded to an exact
one at no greater normalized Hamming cost than its square defect.  Decompose a
permutation `p` into cycles.  The points at which `p^2` is nontrivial are
exactly the points in cycles of length greater than two.  Replace `p` on those
cycles by any involution, leaving its one- and two-cycles unchanged.  The
result `p_0` satisfies

```text
p_0^2=1,                  d_H(p,p_0) <= d_H(p^2,1).       (4)
```

Apply (4) separately to `c_n` and `e_n`.  Bi-invariance and the fixed-word
Lipschitz estimate show that changing them by `o(1)` changes the defects of
all five other relators, and the distance of `Y_n^8` from the identity, by
`o(1)`.  The rounded version of the gate may therefore take `c_n,e_n` to be
honest involutions at every finite stage.

The dependency-free checker attached to the claim verifies the free-word
identities in (1), both directions of (3), and the marked-word transport.  It
is only a transcription check; the group-theoretic derivation above is the
proof that the five discarded relators follow from the retained seven.
