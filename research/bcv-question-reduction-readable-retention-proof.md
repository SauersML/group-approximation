---
rg: 2
id: bcv-question-reduction-readable-retention-proof
kind: route
title: Cut out Intro corners with SamZ atoms and transport source words by Pauli-X shifts
target: bcv-question-reduction-retains-readable-closure
requires: []
---

Use the notation of BCV Definition 4.4.  Put

```text
e_z=F^Z_z tensor 1,             z in F_2^k.
```

The readable SamZ measurement in the sampling apparatus has the `e_z` as
its joint atoms.  Hence `ell^infinity(F_2^k) tensor 1` lies in the target
readable algebra.

Let `P^{x,R}_{a_R}` be a readable marginal of the source PVM at a
supported vertex `x`.  Equations (49)--(50) make the corresponding
readable Intro marginal on the A side

```text
sum_(z:s_A(z)=x) e_z tensor P^{x,R}_{a_R}.               (QRP1)
```

The B side has the analogous formula.  Multiplying by one SamZ atom cuts
`(QRP1)` down to `e_z tensor P^{x,R}_{a_R}` whenever `s_A(z)=x`.
The target Pauli-X unreadables satisfy

```text
(X^alpha tensor 1)e_z(X^alpha tensor 1)^*=e_(z+alpha).
                                                               (QRP2)
```

Thus every source readable spectral projection occurs in every Pauli block,
and

```text
e_w tensor D_0(S) subseteq D_infinity(QR_k(S))           (QRP3)
```

for every `w`.

It remains to transport source unreadable conjugations, rather than only
the initial readable algebra.  If `U^x_j` is a source unreadable
observable, the unreadable Intro observable induced by (49) on the A side
is block controlled: its `z`-block is `U^{s_A(z)}_j`; again use the B
side when that is where `x` occurs.  Fix a block `w`, choose a sampled
`z_x` with endpoint `x`, and conjugate this controlled Intro observable
by the Pauli shift carrying `w` to `z_x`.  The resulting target
unreadable word preserves the `w`-block and restricts there to
`U^x_j`.  Therefore, for every `d` already realized in that block,

```text
e_w tensor d
   maps under target unreadable conjugation to
e_w tensor U^x_j d (U^x_j)^*.                            (QRP4)
```

Induction on a source unreadable word upgrades `(QRP3)` to

```text
e_w tensor D_infinity(S)
    subseteq D_infinity(QR_k(S))                          (QRP5)
```

for every `w`. The orthogonal sum over all `2^k` SamZ blocks proves
`(QRR1)`.

Finally, a finite Boolean algebra with `b` atoms tensored with the
`2^k`-atom SamZ algebra has `2^k b` atoms.  A containing Boolean algebra
cannot have fewer atoms, proving the quantitative conclusion.  This is a
statement about BCV's explicit honest completeness strategy; it makes no
claim that a different perfect strategy could not have a smaller readable
closure.
