---
rg: 2
id: atlas-two-transverse-shears-determinant-proof
kind: route
title: Solve the two-shear orbit equations on the marked CK slice
target: atlas-two-transverse-shears-have-determinant-balance-test
requires:
  - atlas-first-transverse-root-shear-leaves-fixed-character-face
  - atlas-steinberg-rank-five-translation
  - atlas-steinberg-spare-index-independence
---

The literal rows `st3_123_a1` and `st3_124_a1` are the two equations in
`(TTS2)`.  Steinberg (St2) gives all remaining commutations: the two actors
have the same source, all `13` and `14` roots have the same source, and each
actor is orthogonal to the other direction's target family.  Conjugating the
joint spectral projections therefore gives `(TTS3)`.

For `p=eE` and `q=fF`, spare-index independence extends the same identities
to the derived roots.  On a fixed `(D,E)` character sector, identify a sign
with a bit in `F_2`, with `-1` corresponding to `1`.  The action of `S^iT^j`
adds

```text
i (u_S,v_S) + j (u_T,v_T)                             (TTR1)
```

to the pair of bits recording the signs of `(C_p,C_q)`.  The marked sign is
their sum, and

```text
w_R=u_R+v_R                                            (TTR2)
```

because the root sign at `1=p+q` is the product of the signs at `p,q`.
Equations `(TTS5)--(TTS6)` follow.

There exists `(i,j)` satisfying both equations precisely when the linear
functional `u` is nonzero on `ker(w)`.  Over `F_2^2`, this is equivalent to
`u` not belonging to the one-dimensional annihilator

```text
ker(w)^perp=span{w},                                   (TTR3)
```

which is exactly the determinant condition `(TTS7)`.  Such a word is a
unitary bijection between the marked `p` and `q` cuts, hence their ranks are
equal.  If the determinant vanishes, every marked-preserving word fixes the
branch orientation; the orbit relations impose no equality.

Finally, restriction of a left regular finite-group representation to a
subgroup is a multiple of that subgroup's regular representation.  The two
independent coefficient-one roots `x_13(1),x_14(1)` generate `C_2^2`, so
each of their four joint characters, including the common fixed character,
has trace `1/4`.  This proves that the fixed face already has macroscopic
label mass before any coefficient-multiplicity choice.
