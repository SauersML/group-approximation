---
rg: 2
id: product-clock-synchronizes-fanizza-and-e5-proof
kind: route
title: Conjugate one base bridge by the commuting product of the two shifts
target: product-clock-synchronizes-fanizza-and-e5
requires:
  - fanizza-bad-atoms-have-symmetric-frames
  - fanizza-symmetric-kernel-has-two-root-e5-clock
  - hard-sign-transport-captures-exit-mass
  - fanizza-turing-bcs-signal-collapse
---

Relations `(PCL2)` imply `(UD_L)^n=U^nD_L^n`.  They also imply

```text
T^n w_i T^-n
 = U^nD_L^n(s_i c_i)D_L^-nU^-n
 = (U^n s_i U^-n)c_i.                                 (1)
```

Conjugation preserves commutators, while `U` commutes with the E5 factor, so

```text
T^n[w_0,w_2]T^-n
 = [T^nw_0T^-n,T^nw_2T^-n],
T^n b T^-n=D_L^n bD_L^-n.                              (2)
```

Conjugating `(PCL3)` and substituting `(1)--(2)` proves `(PCL4)`.

There are finitely many atom types and only 26 bad atoms, so a presentation
may include one aligned base bridge per atom while sharing `U,D_L,T`.  The
frame audit shows every bridge uses the same kernel and, after at most the
fixed simultaneous coordinate swap, the same hard commutator position.

For exact-model preservation, use the unsheared diagonal coefficient
character.  Its form cancels the identical source form on every selector
atom, so the combined hard commutator in `(PCL3)` is trivial.  The trivial E5
representation makes `b=D_L=1`; all cross commutators and the bridge hold,
while the Fanizza factor and its trace are unchanged.
