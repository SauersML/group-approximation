---
rg: 2
id: balanced-marginal-hnn-character-packing-proof
kind: proof
title: Proof of balanced marginal HNN character packing
proves:
  - balanced-marginal-hnn-character-packing
---

Put `chi_A=chi|A`.  For `r!=s`, set

```text
w=t_r^(-1)t_s,
beta=alpha_r^(-1) alpha_s in Aut(A).                   (BMP1)
```

The HNN relations give

```text
w a w^(-1)=beta(a)                    (a in A).        (BMP2)
```

The character idempotent satisfies

```text
a e_chi=e_chi a=chi(a)e_chi            (a in A).       (BMP3)
```

Choose `a in A` for which `chi(a)!=chi(beta(a))`; such an `a` exists
exactly because the two characters in `(BMH4)` indexed by `r,s` are
distinct.  Applying `(BMP2)--(BMP3)` in two ways gives

```text
chi(a) e_chi w e_chi
 =e_chi w a e_chi
 =e_chi beta(a) w e_chi
 =chi(beta(a)) e_chi w e_chi.                          (BMP4)
```

Hence `e_chi w e_chi=0`.  Conjugating `(BMP4)` by `t_r` on the left and
`t_s^(-1)` on the right yields

```text
p_r p_s=0.                                             (BMP5)
```

The base group embeds in `(BMH2)` by the normal-form theorem for multiple
HNN extensions, so `e_chi` and all its conjugates are genuine nonzero
projections in the complex group algebra.

For the extension statement, let

```text
iota_0:C[A]->M,        iota_0(a)=pi(a),
iota_r:C[A]->M,        iota_r(a)=pi(alpha_r(a)).       (BMP6)
```

The assumed invariance says that `iota_0` and `iota_r` have the same trace
on every minimal character projection of `C[A]`.  Two trace-preserving
embeddings of a finite-dimensional abelian algebra into a finite factor are
unitarily conjugate: match their character projections, which have equal
trace, by partial isometries and sum those partial isometries.  Thus there
is `U_r in U(M)` satisfying

```text
U_r pi(a) U_r^*=pi(alpha_r(a))          (a in A).      (BMP7)
```

Assigning `t_r` to `U_r` realizes every relation in `(BMH2)` and extends
`pi`.

If `J in A` and every `alpha_r` fixes `J`, then `(BMH2)` makes every stable
letter commute with `J`; since `H` is abelian, `J` is central in `Gamma`.
The equality `chi(J)=-1` gives

```text
e_chi<=q_-,             p_r<=q_-.                     (BMP8)
```

All characters in `(BMH4)` take the value `-1` on `J`.  There are exactly
`|A|/2` such characters, proving `K<=|A|/2`; the inclusion `A<=H` gives
the second inequality in `(BMH6)`.  Finally the canonical trace of a
one-dimensional character idempotent of `H` is `1/|H|`, while the canonical
trace of `(1-J)/2` is `1/2`.  Orthogonality and `(BMP8)` therefore give
`(BMH7)`, with equality possible when `A=H` and all `J=-1` characters are
used.  This proves both the construction and its optimality.
