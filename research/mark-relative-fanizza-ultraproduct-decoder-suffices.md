---
rg: 2
id: mark-relative-fanizza-ultraproduct-decoder-suffices
kind: claim
title: A mark-relative Fanizza corner decoder is enough for threshold-free reverse Kleene
distinct_from:
  fanizza-native-signal-ultraproduct-groupification: that states unconditional death of a named word as the compiler target; this isolates a sufficient decoder which is invoked only when a rational group-algebra mark survives.
  unconditional-bcs-ultraproduct-decoder-forces-ce: that applies the decoder to the trivial homomorphism; this explicitly allows every mark-dead homomorphism, including the trivial one.
  fanizza-canonical-profile-groupification: that asks only for canonical-delta collapse; this gives collapse in every matrix-ultraproduct homomorphism, but only conditionally on survival of the mark.
---

For the computable Fanizza `HALT` family `(B_m,D_m)`, it is enough to
construct totally computably:

- a finite generating set and uniformly recursively enumerable relators for
  a group `Gamma_m`;
- a finite rational group-algebra mark `p_m in Q[Gamma_m]`;

with the following clauses.

```text
m halts  => p_m!=0 in Q[Gamma_m],                       (MRF1)
```

and, when `m` does not halt, for every homomorphism

```text
pi:Gamma_m -> U(prod_U M_(d_n)),                        (MRF2)
```

the implication

```text
pi(p_m)!=0
  => there is a perfect B_m strategy/state phi_pi
     with phi_pi(D_m)>0                                 (MRF3)
```

holds.  The decoder need not exist when `pi(p_m)=0`.  In particular the
trivial homomorphism is harmless whenever the coefficient sum of `p_m` is
zero.  The decoded corner may depend nonfunctorially on `pi` and may be any
nonzero support corner extracted from `pi(p_m)`.

Fanizza NONHALT soundness says that every perfect strategy has
`phi(D_m)=0`.  Hence `(MRF3)` is impossible on a NONHALT instance and every
matrix-ultraproduct homomorphism must kill `p_m`.  Thus `p_m` lies in the
hyperlinear radical in the group-algebra sense, and the reverse-Kleene
proof-enumeration diagonal gives a finitely presented nonhyperlinear group.

No finite-coordinate modulus, defect threshold, or decoder on mark-dead maps
is needed.  This is the smallest categorical reverse-Kleene interface: the
entire remaining problem is a finite-dimensional-only implication from
survival of one group-algebra mark to positive native Fanizza signal.
