---
rg: 2
id: mihailova-free-rounding-projective-cross-fence
kind: claim
title: Free-factor rounding leaves a genuinely projective cross-stability problem in the Mihailova actor
distinct_from:
  mihailova-actor-liftable-ce-forces-q-hyperlinear: that consumes exact levelwise adjoint actor representations; this identifies why freeness of the two coordinate factors does not produce them.
  no-published-unconditional-codense-stable-host: that cites failure of ordinary HS-stability for products of free groups in a different HNN program; this separates ordinary from projective exactification and exhibits the scalar packet that survives passage to adjoints.
---

Let `G=F_m x F_k`, with free generators `a_1,...,a_m` and
`b_1,...,b_k`.  A matrix microstate for `G` is already an exact
representation on each free factor after simply declaring the generator
matrices to be its images.  Its entire relation defect is therefore

```text
max_(i,j) ||[U_i,V_j]-1||_2.                         (MPS1)
```

There are two different promotion problems, and neither follows merely from
the freeness of the factors.

1. Replacing the tuples by nearby tuples which commute exactly is ordinary
   Hilbert--Schmidt stability of `F_m x F_k`.  Ioana proves that this fails
   for `m,k>=2`, even flexibly.
2. Replacing their adjoint actions by exact finite-dimensional actions asks
   only for nearby **projectively commuting** tuples:

```text
[U_i',V_j'] in C.1.                                  (MPS2)
```

   This is the promotion actually consumed by
   `mihailova-actor-liftable-ce-forces-q-hyperlinear`, because scalar
   commutators vanish under `Ad`.

The second problem cannot be silently reduced to the first by observing that
the scalars tend to `1`.  In dimension `d`, let `S_d,D_d` be the cyclic shift
and clock matrices and put `zeta_d=exp(2 pi i/d)`.  Then

```text
D_d S_d = zeta_d S_d D_d,
||[D_d,S_d]-1||_2 = |zeta_d-1| -> 0,                 (MPS3)
Ad(D_d) Ad(S_d) = Ad(S_d) Ad(D_d)                   (MPS4)
```

on the full `d`-dimensional packet.  Thus asymptotically trivial scalar
multipliers can occupy normalized mass one; determinant quantization does
not make them vanish.  The same packet embeds in `F_m x F_k` by assigning
one generator in each factor to `D_d,S_d` and the others to `1`.

Consequently a Mihailova proof based on factorwise free-group lifts must
establish one of two genuinely new statements:

- global projective HS-stability for the cross relations `(MPS2)`; or
- the weaker, state-specific version which preserves the centered-lamp
  coefficient attached to the Mihailova stabilizer.

Ioana's theorem rules out replacing either target by ordinary commuting
rounding.  The clock--shift packet rules out deleting the word
"projective" by a determinant or small-scalar argument.  This is a fence,
not a negative result about the state-specific target.

The normalized Hilbert--Schmidt identity behind `(MPS4)` is exact:

```text
||Ad(W)-1||_(2,M_(d^2))^2 = 2(1-|tr_d(W)|^2).        (MPS5)
```

Hence `(MPS1)` does make the adjoint tuples approximate representations;
what is missing is precisely their levelwise exactification.
