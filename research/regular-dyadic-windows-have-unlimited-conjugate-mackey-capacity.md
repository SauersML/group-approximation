---
rg: 2
id: regular-dyadic-windows-have-unlimited-conjugate-mackey-capacity
kind: claim
title: Regular dyadic congruence windows have unlimited stationary capacity for Mackey cocycles
distinct_from:
  cartantype-mackey-cocycle-is-pauli-and-locally-absorbed: that cancels the first rank-two cocycle and abstractly treats a fixed finite groupoid; this shows that regular congruence normalization supplies the required absorber without losing character or conductor, even for a growing sequence of windows.
  finite-regular-adjoint-retains-full-conductor: that proves conjugate doubling retains conductor; this applies it to arbitrary finite Mackey sector groupoids and rules out multiplicity-capacity arguments.
  regular-congruence-depth-mixtures-remain-folner: that constructs scalar depth profiles without joint intertwiners; this says any projective phases on already-available joint intertwiners can be absorbed at zero normalized-character cost.
---

Let `Q` be any finite congruence quotient and `lambda_Q` its left regular
representation.  If a finite packet/groupoid of parahoric types and
intertwiners occurs inside a regular `Q`-block with scalar Mackey cocycle
`c`, then conjugate doubling replaces every arrow `C_g` by

```text
C_g tensor conjugate(C_g),                              (RMC1)
```

and cancels `c` identically on every path.  This operation does not leave
the regular congruence sector, because

```text
lambda_Q tensor conjugate(lambda_Q) ~= |Q| lambda_Q.    (RMC2)
```

It therefore preserves the normalized regular character, every minimal
congruence conductor present in the regular block, and all normalized-HS
defects and overlap fractions.

The statement remains true for a sequence of finite windows whose size and
projective rank tend to infinity: perform `(RMC1)` separately at each
matrix level.  Flexible matrix approximation places no upper bound on the
multiplicity overhead, and `(RMC2)` makes that overhead another regular
amplification rather than a new character sector.

Even without arbitrary external amplification, the raw exponents rule out
a rank-versus-volume obstruction on the surviving diagonal-type path.  A
path through `k` successive two-layer windows has stabilizer product of
order at most `16^k=2^(4k)`.  Its
alternating cocycle rank is at most `4k`, so a projective irreducible has
dimension at most `2^(2k)`.  In contrast,

```text
|SL_3(Z/2^(a+2k))|/|SL_3(Z/2^a)|=2^(16k).              (RMC4)
```

Thus even maximally independent symplectic ranks grow far more slowly than
the regular congruence carrier.  For a capacity proof it is immaterial
whether the actual ranks add linearly or recycle under mod-four conjugation.

Consequently no uniform dyadic commutant-transfer gap can be obtained from
the absolute size, projective rank, or minimal representation dimension of
a FINITE-window Mackey cocycle.  A live obstruction must prevent the
conjugate packet from occupying the same arithmetic carrier -- through
cross-depth branching, literal mixed-root identifications, or additive
multi-path interference -- rather than merely demand a larger multiplicity
space.  This is a capacity firewall, not a construction of the missing
joint parahoric intertwiners.
